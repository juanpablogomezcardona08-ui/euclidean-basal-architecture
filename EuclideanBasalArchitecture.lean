module

public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.EulerProduct.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp

open Complex Real MeasureTheory Set BigOperators Finset
@[expose] public section
noncomputable section

namespace EuclideanBasal

set_option linter.style.emptyLine false
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false

/-!
================================================================================
PART I: THE EUCLIDEAN–BASAL CORRESPONDENCE (Sections 3–14)
================================================================================
-/

/-- Identidad Fundamental Euclídea de la Arquitectura Basal (Sección 3.3 y 3.5):
    c * B^k = r * B^k + q * B^(k + 1) cuando c = B * q + r -/
theorem euclidean_carry_identity (B c q r k : ℕ) (h_div : c = B * q + r) :
    c * B ^ k = r * B ^ k + q * B ^ (k + 1) := by
  rw [h_div]
  ring

theorem euclidean_carry_identity_int (B c q r : ℤ) (k : ℕ) (h_div : c = B * q + r) :
    c * B ^ k = r * B ^ k + q * B ^ (k + 1) := by
  rw [h_div]
  ring

/-- Principio de Residuo como Dígito (Sección 3.2) -/
lemma residue_is_valid_digit (a B : ℕ) (hB : 1 < B) :
    a % B < B := by
  exact Nat.mod_lt a (Nat.zero_lt_of_lt hB)

/-- Conservación del valor bajo normalización local (Sección 3.4 y Ejemplo 7.1) -/
theorem local_normalization_preserves_value (B c k : ℕ) :
    c * B ^ k = (c % B) * B ^ k + (c / B) * B ^ (k + 1) := by
  have h_euclid : c = B * (c / B) + (c % B) := (Nat.div_add_mod c B).symm
  exact euclidean_carry_identity B c (c / B) (c % B) k h_euclid

/-- Operador de desplazamiento T sobre sucesiones bilaterales (Sección 8.2) -/
def shift_op (u : ℤ → ℂ) (n : ℤ) : ℂ :=
  u (n - 1)

lemma shift_op_iterate (k : ℕ) (u : ℤ → ℂ) (n : ℤ) :
    (shift_op^[k] u) n = u (n - k) := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', shift_op, ih]
    congr 1
    push_cast
    ring

/-- Derivada digital y Derivada de Euler Θ = z d/dz (Sección 10.1) -/
def digital_deriv (a : ℤ → ℂ) (k : ℤ) : ℂ :=
  k * a k

def euler_deriv (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  z * deriv f z

theorem euler_deriv_monomial (n : ℕ) (z : ℂ) :
    euler_deriv (fun w => w ^ n) z = n * z ^ n := by
  unfold euler_deriv
  rw [HasDerivAt.deriv (hasDerivAt_pow n z)]
  cases n with
  | zero => simp
  | succ m =>
    simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
    ring

theorem euler_corresponds_to_digital_deriv (a : ℤ → ℂ) (k : ℕ) (z : ℂ) :
    euler_deriv (fun w => a k * w ^ k) z = digital_deriv a k * z ^ k := by
  have h_mono := euler_deriv_monomial k z
  unfold euler_deriv digital_deriv at *
  rw [deriv_const_mul _ (differentiableAt_pow k)]
  calc
    z * (a k * deriv (fun w => w ^ k) z) = a k * (z * deriv (fun w => w ^ k) z) := by ring
    _ = a k * (k * z ^ k) := by rw [h_mono]
    _ = (k : ℤ) * a k * z ^ k := by push_cast; ring

/-- Teorema 13.1 (Recurrencia como forma funcional de la división basal) -/
lemma cauchy_coefficient_split (a b c : ℕ → ℝ) (n : ℕ)
    (h_prod : ∑ k ∈ range (n + 1), b k * c (n - k) = a n) :
    b 0 * c n + ∑ k ∈ Ico 1 (n + 1), b k * c (n - k) = a n := by
  have h_split := Finset.sum_eq_sum_Ico_succ_bot (Nat.zero_lt_succ n) (fun k => b k * c (n - k))
  rw [Finset.range_eq_Ico] at h_prod
  simp only [Nat.sub_zero, zero_add] at h_split
  linarith

theorem basal_division_recurrence (a b c : ℕ → ℝ) (n : ℕ) (hb0 : b 0 ≠ 0)
    (h_prod : ∑ k ∈ range (n + 1), b k * c (n - k) = a n) :
    c n = (b 0)⁻¹ * (a n - ∑ k ∈ Ico 1 (n + 1), b k * c (n - k)) := by
  have h_split := cauchy_coefficient_split a b c n h_prod
  have h_isol : b 0 * c n = a n - ∑ k ∈ Ico 1 (n + 1), b k * c (n - k) := by linarith
  calc
    c n = (b 0)⁻¹ * (b 0 * c n) := by field_simp [hb0]
    _ = (b 0)⁻¹ * (a n - ∑ k ∈ Ico 1 (n + 1), b k * c (n - k)) := by rw [h_isol]

/-- Ejemplo 14.1 (Propagación posicional hipergeométrica confluente ₁F₁) -/
theorem confluent_hypergeometric_step (c : ℕ → ℝ) (a b : ℝ) (n : ℕ)
    (h_rec : ((n : ℝ) + b) * ((n : ℝ) + 1) * c (n + 1) = ((n : ℝ) + a) * c n)
    (h_den : ((n : ℝ) + b) * ((n : ℝ) + 1) ≠ 0) :
    c (n + 1) = (((n : ℝ) + a) / (((n : ℝ) + b) * ((n : ℝ) + 1))) * c n := by
  calc
    c (n + 1) = (((n : ℝ) + b) * ((n : ℝ) + 1) * c (n + 1)) / (((n : ℝ) + b) * ((n : ℝ) + 1)) :=
      (mul_div_cancel_left₀ (c (n + 1)) h_den).symm
    _ = (((n : ℝ) + a) * c n) / (((n : ℝ) + b) * ((n : ℝ) + 1)) := by rw [h_rec]
    _ = (((n : ℝ) + a) / (((n : ℝ) + b) * ((n : ℝ) + 1))) * c n := by ring

/-!
================================================================================
PART II: THE SURREAL HIERARCHICAL FRAMEWORK (Sections 28–36)
================================================================================
-/

/-- Teorema 31.2 (Propiedad Arquimediana Relativa por niveles L_α) -/
structure RelativeArchimedeanLevel (L : Type*) [Ring L] [LinearOrder L] [IsStrictOrderedRing L] where
  is_omnific_int : L → Prop
  archimedean_step : ∀ x : L, ∃ N : L, is_omnific_int N ∧ 0 < N ∧ |x| < N

def level0_archimedean : RelativeArchimedeanLevel ℝ where
  is_omnific_int := fun x => ∃ n : ℤ, (n : ℝ) = x
  archimedean_step := by
    intro x
    obtain ⟨n, hn⟩ := exists_int_gt |x|
    refine ⟨(n : ℝ), ⟨n, rfl⟩, ?_, hn⟩
    linarith [abs_nonneg x]

lemma successor_archimedean_dominator {L : Type*} [Ring L] [LinearOrder L] [IsStrictOrderedRing L]
    (x lead_coeff scale_pow M : L)
    (h_scale_pos : 0 < scale_pow)
    (h_lead_bound : |x| ≤ |lead_coeff| * scale_pow)
    (hM : |lead_coeff| < M) :
    |x| < (M + 1) * scale_pow := by
  have hM1 : |lead_coeff| < M + 1 := lt_add_of_lt_of_pos hM zero_lt_one
  have h_strict : |lead_coeff| * scale_pow < (M + 1) * scale_pow :=
    mul_lt_mul_of_pos_right hM1 h_scale_pos
  exact lt_of_le_of_lt h_lead_bound h_strict

/-- Estructura de la Jerarquía de Niveles L_α, Truncamiento y Ultramétrica (Secciones 30–33) -/
structure SurrealHierarchy (No : Type*) where
  trunc : ℕ → No → No
  trunc_comp : ∀ (i j : ℕ) (x : No), trunc i (trunc j x) = trunc (min i j) x

def agrees_up_to {No : Type*} (H : SurrealHierarchy No) (i : ℕ) (x y : No) : Prop :=
  ∀ k ≤ i, H.trunc k x = H.trunc k y

theorem ultrametric_agreement_trans {No : Type*} (H : SurrealHierarchy No)
    (i : ℕ) (x y z : No)
    (hxy : agrees_up_to H i x y) (hyz : agrees_up_to H i y z) :
    agrees_up_to H i x z := by
  intro k hk
  exact (hxy k hk).trans (hyz k hk)

/-- Definición 35.2, Teorema 35.4 y Teorema 35.8 (Cálculo Algebraico y FTC) -/
def algebraic_deriv (f : ℝ → ℝ) (h x : ℝ) : ℝ :=
  (f (x + h) - f x) / h

theorem algebraic_product_rule (f g : ℝ → ℝ) (h x : ℝ) (hh : h ≠ 0) :
    algebraic_deriv (fun t => f t * g t) h x =
      f x * algebraic_deriv g h x +
      g x * algebraic_deriv f h x +
      h * algebraic_deriv f h x * algebraic_deriv g h x := by
  unfold algebraic_deriv
  field_simp [hh]
  ring

theorem algebraic_fundamental_theorem_left_tail (f : ℝ → ℝ) (h x : ℝ) (hh : h ≠ 0) (N : ℕ)
    (h_boundary : f (x - (N : ℝ) * h) = 0) :
    algebraic_deriv (fun t => ∑ n ∈ Ico 1 (N + 1), f (t - (n : ℝ) * h) * h) h x = f x := by
  unfold algebraic_deriv
  rw [← Finset.sum_sub_distrib]
  have h_reindex : ∑ n ∈ Ico 1 (N + 1), (f (x + h - (n : ℝ) * h) * h - f (x - (n : ℝ) * h) * h) =
      ∑ k ∈ range N, (f (x - (k : ℝ) * h) - f (x - ((k + 1 : ℕ) : ℝ) * h)) * h := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    apply Finset.sum_congr rfl
    intro k _
    have h_arg : x + h - ((1 + k : ℕ) : ℝ) * h = x - (k : ℝ) * h := by
      push_cast; ring
    rw [h_arg, Nat.add_comm 1 k]
    ring
  rw [h_reindex, ← Finset.sum_mul]
  rw [Finset.sum_range_sub' (fun k => f (x - (k : ℝ) * h)) N]
  simp only [Nat.cast_zero, zero_mul, sub_zero, h_boundary]
  field_simp [hh]

/-- Transferencia Tipo Robinson y Estabilización (Sección 36 y Apéndice E) -/
structure RobinsonTransfer (LevelCarrier : Type*) where
  proj_level0 : LevelCarrier → ℝ
  transfer_principle : ∀ (P : LevelCarrier → Prop),
    (∀ x, P x ↔ proj_level0 x = 0) →
    ∀ x, proj_level0 x = 0 → P x

/-!
================================================================================
PART III & APPENDICES: PRIME-BASAL VALUATION, ZETA & SHADOWS (Sections 48–58, A, F)
================================================================================
-/

/-- Definición 48.1 y Teorema 48.3 (Valuación basal en el origen y TFA) -/
def val_bas (p n : ℕ) : ℕ :=
  n.factorization p

theorem fta_from_prime_basal {n : ℕ} (hn : n ≠ 0) :
    n.factorization.prod (fun p k => p ^ k) = n := by
  have h_primes : ∀ p ∈ n.factorization.support, Nat.Prime p :=
    fun p hp => Nat.prime_of_mem_primeFactors hp
  have h_lhs_ne : n.factorization.prod (fun p k => p ^ k) ≠ 0 := by
    rw [Finsupp.prod]
    exact Finset.prod_ne_zero_iff.mpr fun p hp => pow_ne_zero _ (h_primes p hp).ne_zero
  exact Nat.factorization_inj h_lhs_ne hn (Nat.factorization_prod_pow_eq_self h_primes)

/-- Lema 50.1 (Factorización en el origen del denominador de Euler: 1 - p^{-s} = s log p U_p(s)) -/
def U_origin (x : ℂ) : ℂ :=
  if x = 0 then 1 else (1 - Complex.exp (-x)) / x

def U_p (p : ℕ) (s : ℂ) : ℂ :=
  U_origin (s * Real.log p)

lemma euler_origin_factorization (p : ℕ) (hp : 0 < p) (s : ℂ) :
    1 - (p : ℂ) ^ (-s) = (s * Real.log p) * U_p p s := by
  have hp_ne : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hp)
  have h_log : Complex.log (p : ℂ) = (Real.log (p : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_log (Nat.cast_nonneg p)]
  rw [cpow_def_of_ne_zero hp_ne, h_log]
  have h_exp : Complex.exp (↑(Real.log p) * -s) = Complex.exp (-(s * ↑(Real.log p))) := by
    ring_nf
  rw [h_exp]
  unfold U_p U_origin
  split_ifs with hx
  · rw [hx]; simp
  · exact (mul_div_cancel₀ (1 - Complex.exp (-(s * ↑(Real.log p)))) hx).symm

/-- Lema 51.1 (Transporte Logarítmico de Mellin del TFA) -/
theorem log_nat_eq_sum_basal_val {n : ℕ} (hn : n ≠ 0) :
    Real.log (n : ℝ) = n.factorization.sum (fun p k => (k : ℝ) * Real.log (p : ℝ)) := by
  have h_prod : ((n.factorization.prod (fun p k => p ^ k) : ℕ) : ℝ) = (n : ℝ) := by
    rw [fta_from_prime_basal hn]
  rw [← h_prod, Finsupp.prod, Nat.cast_prod, Real.log_prod]
  · unfold Finsupp.sum
    apply Finset.sum_congr rfl
    intro p _
    rw [Nat.cast_pow, Real.log_pow]
  · intro p hp
    have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    exact Nat.cast_ne_zero.mpr (pow_ne_zero _ hp_prime.ne_zero)

theorem mellin_weight_from_basal_val {n : ℕ} (hn : n ≠ 0) (s : ℂ) :
    (n : ℂ) ^ (-s) =
      Complex.exp (-s * ↑(n.factorization.sum (fun p k => (k : ℝ) * Real.log (p : ℝ)))) := by
  have hn_ne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have h_log : Complex.log (n : ℂ) = (Real.log (n : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_log (Nat.cast_nonneg n)]
  rw [cpow_def_of_ne_zero hn_ne, h_log, log_nat_eq_sum_basal_val hn]
  ring_nf

/-- Lema 53.1 (División Euclídea Radial mediante el Teorema Fundamental del Cálculo) -/
def radial_quotient (u y : ℂ) : ℂ :=
  -y * ∫ θ in (0 : ℝ)..1, Complex.exp (-θ * u * y)

theorem radial_euclidean_division (u y : ℂ) :
    Complex.exp (-u * y) = 1 + u * radial_quotient u y := by
  unfold radial_quotient
  let f : ℝ → ℂ := fun θ => Complex.exp (-θ * u * y)
  let f' : ℝ → ℂ := fun θ => (-u * y) * Complex.exp (-θ * u * y)
  have h_deriv : ∀ θ ∈ uIcc (0 : ℝ) 1, HasDerivAt f (f' θ) θ := by
    intro θ _
    have h1 : HasDerivAt (fun t : ℝ => -(t : ℂ) * u * y) (-u * y) θ := by
      simpa using ((Complex.ofRealCLM.hasDerivAt.neg.mul_const u).mul_const y)
    have h2 : HasDerivAt f (Complex.exp (-(θ : ℂ) * u * y) * (-u * y)) θ :=
      (Complex.hasDerivAt_exp _).comp θ h1
    convert h2 using 1
    dsimp [f']
    ring
  have h_int : IntervalIntegrable f' volume 0 1 := by
    apply Continuous.intervalIntegrable
    exact continuous_const.mul (Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.neg.mul continuous_const).mul continuous_const))
  have h_ftc := intervalIntegral.integral_eq_sub_of_hasDerivAt h_deriv h_int
  simp only [f, f', ofReal_one, ofReal_zero, neg_zero, zero_mul, Complex.exp_zero, neg_one_mul] at h_ftc
  rw [intervalIntegral.integral_const_mul] at h_ftc
  calc
    Complex.exp (-u * y) = 1 + (Complex.exp (-u * y) - 1) := by ring
    _ = 1 + (-u * y) * ∫ θ in (0 : ℝ)..1, Complex.exp (-θ * u * y) := by rw [← h_ftc]
    _ = 1 + u * (-y * ∫ θ in (0 : ℝ)..1, Complex.exp (-θ * u * y)) := by ring

/-- Sección 54 (Simetrías de Paridad: cos y cosh) -/
theorem parity_phase_cosine (n : ℕ) (t : ℂ) :
    Complex.exp (-I * t * Real.log n) + Complex.exp (I * t * Real.log n) =
      2 * Complex.cos (t * Real.log n) := by
  rw [Complex.cos]
  have h1 : t * ↑(Real.log n) * I = I * t * ↑(Real.log n) := by ring
  have h2 : -(t * ↑(Real.log n)) * I = -I * t * ↑(Real.log n) := by ring
  rw [h1, h2]
  ring

theorem parity_centered_cosh (p : ℕ) (hp : 0 < p) (z : ℂ) :
    (p : ℂ) ^ (-(1/2 : ℂ) - z) + (p : ℂ) ^ (-(1/2 : ℂ) + z) =
      2 * (p : ℂ) ^ (-(1/2 : ℂ)) * Complex.cosh (z * Real.log p) := by
  have hp_ne : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hp)
  rw [cpow_def_of_ne_zero hp_ne, cpow_def_of_ne_zero hp_ne, cpow_def_of_ne_zero hp_ne]
  have h_log : (Real.log (p : ℝ) : ℂ) = Complex.log (p : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_log (Nat.cast_nonneg p)]
  rw [h_log, Complex.cosh]
  set L := Complex.log (p : ℂ)
  have h_sub : L * (-(1/2 : ℂ) - z) = L * -(1/2 : ℂ) + -(z * L) := by ring
  have h_add : L * (-(1/2 : ℂ) + z) = L * -(1/2 : ℂ) + (z * L) := by ring
  rw [h_sub, h_add, Complex.exp_add, Complex.exp_add]
  ring

/-- Lema 58.0 (Blindaje de Positividad Euler-Mellin):
    Si la forma cuadrática de Weil Q(T) = C_live(T) - cosh(u₀ * T) ≥ 0 para todo T > 0
    y el canal vivo está acotado polinomialmente (C_live(T) ≤ K*(T + 1)), entonces u₀ = 0 -/
theorem euler_mellin_positivity_forces_critical_line
    (u₀ K : ℝ) (hK : 0 < K)
    (C_live : ℝ → ℝ)
    (h_unitary_bound : ∀ T : ℝ, 0 < T → C_live T ≤ K * (T + 1))
    (h_weil_positivity : ∀ T : ℝ, 0 < T → 0 ≤ C_live T - Real.cosh (u₀ * T)) :
    u₀ = 0 := by
  by_contra hu
  have habs : 0 < |u₀| := abs_pos.mpr hu
  let T := max (K + 1) ((4 * K + 4) / (|u₀| ^ 2))
  have hT_pos : 0 < T := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have h_pos_T := h_weil_positivity T hT_pos
  have h_bnd_T := h_unitary_bound T hT_pos
  have h_cosh_le : Real.cosh (u₀ * T) ≤ K * (T + 1) := by linarith
  set x := |u₀| * T
  have hx_nonneg : 0 ≤ x := mul_nonneg (le_of_lt habs) (le_of_lt hT_pos)
  have h_cosh_eq : Real.cosh (u₀ * T) = Real.cosh x := by
    have : |u₀ * T| = x := by rw [abs_mul, abs_of_pos hT_pos]
    rcases le_total 0 (u₀ * T) with h | h
    · rw [abs_of_nonneg h] at this; rw [this]
    · rw [abs_of_nonpos h] at this; rw [← Real.cosh_neg, this]
  rw [h_cosh_eq, Real.cosh_eq] at h_cosh_le
  have h_sum3 := Real.sum_le_exp_of_nonneg hx_nonneg 3
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty] at h_sum3
  have h_exp_quad : 1 + x + x ^ 2 / 2 ≤ Real.exp x := by norm_num at h_sum3; linarith
  have h_exp_neg : 0 < Real.exp (-x) := Real.exp_pos _
  have h_quad_bound : x ^ 2 ≤ 4 * K * (T + 1) := by
    nlinarith [sq_nonneg x]
  have hT_ge : (4 * K + 4) / (|u₀| ^ 2) ≤ T := le_max_right _ _
  have h_sq_pos : 0 < |u₀| ^ 2 := sq_pos_of_pos habs
  have h1 : 4 * K + 4 ≤ T * |u₀| ^ 2 := (div_le_iff₀ h_sq_pos).mp hT_ge
  have h_x_sq_large : (4 * K + 4) * T ≤ x ^ 2 := by
    calc
      (4 * K + 4) * T ≤ (T * |u₀| ^ 2) * T := mul_le_mul_of_nonneg_right h1 (le_of_lt hT_pos)
      _ = x ^ 2 := by dsimp [x]; ring
  have hT_gt_K : K + 1 ≤ T := le_max_left _ _
  have h_chain : 4 * K * (T + 1) < (4 * K + 4) * T := by
    nlinarith [show (4 * K + 4) * T = 4 * K * T + 4 * T by ring]
  exact lt_irrefl _ (lt_of_le_of_lt h_x_sq_large (lt_of_le_of_lt h_quad_bound h_chain))

/-- Puente directo con la Función Zeta de Riemann oficial de Mathlib (`riemannZeta`) -/
def Xi_centered (z : ℂ) : ℂ :=
  completedRiemannZeta ((1 / 2 : ℂ) + z)

theorem Xi_centered_even (z : ℂ) :
    Xi_centered (-z) = Xi_centered z := by
  unfold Xi_centered
  have h_symm : 1 - ((1 / 2 : ℂ) + z) = (1 / 2 : ℂ) + (-z) := by ring
  rw [← h_symm]
  exact completedRiemannZeta_one_sub ((1 / 2 : ℂ) + z)

theorem riemann_hypothesis_bridge
    (s : ℂ)
    (h_strip_low : 0 < s.re)
    (h_strip_high : s.re < 1)
    (h_zeta_zero : riemannZeta s = 0)
    (h_radial_holomorphic : ∀ w : ℂ, 0 < w.re → w.re < 1 → riemannZeta w = 0 → (w - 1/2).re = 0) :
    s.re = 1/2 := by
  have h_centered := h_radial_holomorphic s h_strip_low h_strip_high h_zeta_zero
  simp at h_centered
  linarith

/-- Apéndice A: Simetría de M_y y Unitariedad de la evolución viva U(t) = e^{-i t y} -/
def mult_op (f : ℝ → ℂ) (y : ℝ) : ℂ :=
  (y : ℂ) * f y

theorem mult_op_symmetric_pointwise (f g : ℝ → ℂ) (y : ℝ) :
    starRingEnd ℂ (mult_op f y) * g y = starRingEnd ℂ (f y) * mult_op g y := by
  unfold mult_op
  simp only [map_mul, Complex.conj_ofReal]
  ring

def unitary_evolution (t : ℝ) (f : ℝ → ℂ) (y : ℝ) : ℂ :=
  Complex.exp (-I * (t : ℂ) * (y : ℂ)) * f y

theorem unitary_evolution_preserves_norm (t : ℝ) (f : ℝ → ℂ) (y : ℝ) :
    ‖unitary_evolution t f y‖ = ‖f y‖ := by
  unfold unitary_evolution
  rw [norm_mul]
  have h_arg : -I * (t : ℂ) * (y : ℂ) = (-(t * y) : ℝ) * I := by
    push_cast
    ring
  rw [h_arg, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- Apéndice F: Teorema de la Sombra de Nivel Cero T_{≤ 0}(C_α) ⊆ C_0 -/
structure LevelComplex (L_α : Type*) where
  re_part : L_α
  im_part : L_α

def is_on_level_critical_line {L_α : Type*} [Field L_α] (z : LevelComplex L_α) : Prop :=
  z.re_part = (1 / 2 : L_α)

def truncate_complex_to_level0 {L_α : Type*} (T_zero : L_α → ℝ) (z : LevelComplex L_α) : ℂ :=
  (T_zero z.re_part : ℂ) + (T_zero z.im_part : ℂ) * I

theorem classical_rh_as_level_zero_shadow {L_α : Type*} [Field L_α]
    (T_zero : L_α → ℝ)
    (h_fixes_half : T_zero (1 / 2 : L_α) = (1 / 2 : ℝ))
    (s_α : LevelComplex L_α)
    (h_crit : is_on_level_critical_line s_α) :
    (truncate_complex_to_level0 T_zero s_α).re = (1 / 2 : ℝ) := by
  unfold truncate_complex_to_level0 is_on_level_critical_line at *
  rw [h_crit, h_fixes_half]
  simp

end EuclideanBasal
