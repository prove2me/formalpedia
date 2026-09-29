-- Prove2me | solution 1 for DeepLearningTheory.gaussian_integral_normalization
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T01:01:25.303203+00:00
-- url     : https://prove2.me/submissions/aada87cd-e87b-4782-88db-aad4848bb55d

import Mathlib
import Definitions.Def_DLT_GaussianIntegrals

open MeasureTheory Real Matrix
open scoped MatrixOrder
open DeepLearningTheory

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ### One-dimensional moments -/

noncomputable def W5_DeepLearningTheory_M (k : ℕ) : ℝ :=
  ∫ x : ℝ, x ^ k * Real.exp (-(1 / 2) * x ^ 2)

theorem W5_DeepLearningTheory_int1 (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k * Real.exp (-(1 / 2) * x ^ 2)) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num) (s := (k : ℝ))
    (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Real.rpow_natCast]

theorem W5_DeepLearningTheory_M0 : W5_DeepLearningTheory_M 0 = Real.sqrt (2 * π) := by
  simp only [W5_DeepLearningTheory_M, pow_zero, one_mul]
  rw [integral_gaussian]
  congr 1
  ring

theorem W5_DeepLearningTheory_Modd (k : ℕ) (hk : Odd k) : W5_DeepLearningTheory_M k = 0 := by
  unfold W5_DeepLearningTheory_M
  have h := integral_neg_eq_self (fun x : ℝ => x ^ k * Real.exp (-(1 / 2) * x ^ 2)) volume
  simp only [hk.neg_pow, neg_sq, neg_mul, integral_neg] at h ⊢
  linarith

theorem W5_DeepLearningTheory_Hrec (q : ℝ) (hq : -1 < q) :
    ∫ x in Set.Ioi (0 : ℝ), x ^ (q + 2) * Real.exp (-(1 / 2) * x ^ (2 : ℝ)) =
      (q + 1) * ∫ x in Set.Ioi (0 : ℝ), x ^ q * Real.exp (-(1 / 2) * x ^ (2 : ℝ)) := by
  rw [integral_rpow_mul_exp_neg_mul_rpow two_pos (by linarith) (by norm_num),
    integral_rpow_mul_exp_neg_mul_rpow two_pos hq (by norm_num)]
  have e1 : -((q + 2) + 1) / 2 = -(q + 1) / 2 + (-1) := by ring
  have e2 : ((q + 2) + 1) / 2 = (q + 1) / 2 + 1 := by ring
  have hne : (q + 1) / 2 ≠ 0 := by
    have : 0 < (q + 1) / 2 := by linarith
    exact this.ne'
  rw [e1, e2, Real.rpow_add (by norm_num), Real.Gamma_add_one hne, Real.rpow_neg_one]
  ring

theorem W5_DeepLearningTheory_Meven (j : ℕ) :
    W5_DeepLearningTheory_M (2 * j) =
      2 * ∫ x in Set.Ioi (0 : ℝ), x ^ (2 * (j : ℝ)) * Real.exp (-(1 / 2) * x ^ (2 : ℝ)) := by
  unfold W5_DeepLearningTheory_M
  have h := integral_comp_abs (f := fun x : ℝ => x ^ (2 * j) * Real.exp (-(1 / 2) * x ^ 2))
  have habs : ∀ x : ℝ, |x| ^ (2 * j) * Real.exp (-(1 / 2) * |x| ^ 2) =
      x ^ (2 * j) * Real.exp (-(1 / 2) * x ^ 2) := by
    intro x
    rw [pow_mul, sq_abs, ← pow_mul]
  simp only [habs] at h
  rw [h]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  rw [show (2 * (j : ℝ)) = ((2 * j : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast,
    Real.rpow_two]

theorem W5_DeepLearningTheory_Mrec (j : ℕ) :
    W5_DeepLearningTheory_M (2 * (j + 1)) = (2 * (j : ℝ) + 1) * W5_DeepLearningTheory_M (2 * j) := by
  rw [W5_DeepLearningTheory_Meven, W5_DeepLearningTheory_Meven]
  have := W5_DeepLearningTheory_Hrec (2 * (j : ℝ)) (by
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith)
  rw [show (2 * ((j + 1 : ℕ) : ℝ)) = 2 * (j : ℝ) + 2 by push_cast; ring, this]
  ring

theorem W5_DeepLearningTheory_M1 : W5_DeepLearningTheory_M 1 = 0 :=
  W5_DeepLearningTheory_Modd 1 (by decide)

theorem W5_DeepLearningTheory_M2 : W5_DeepLearningTheory_M 2 = Real.sqrt (2 * π) := by
  have := W5_DeepLearningTheory_Mrec 0
  norm_num at this
  rw [this, W5_DeepLearningTheory_M0]

theorem W5_DeepLearningTheory_M3 : W5_DeepLearningTheory_M 3 = 0 :=
  W5_DeepLearningTheory_Modd 3 (by decide)

theorem W5_DeepLearningTheory_M4 : W5_DeepLearningTheory_M 4 = 3 * Real.sqrt (2 * π) := by
  have := W5_DeepLearningTheory_Mrec 1
  norm_num at this
  rw [this, W5_DeepLearningTheory_M2]

/-! ### Products over coordinates -/

theorem W5_DeepLearningTheory_prod_integrable {N : ℕ} (m : Fin N → ℕ) :
    Integrable (fun w : Fin N → ℝ => ∏ i, (w i ^ m i * Real.exp (-(1 / 2) * w i ^ 2))) :=
  Integrable.fintype_prod (f := fun i (x : ℝ) => x ^ m i * Real.exp (-(1 / 2) * x ^ 2))
    (μ := fun _ => (volume : Measure ℝ)) (fun i => W5_DeepLearningTheory_int1 (m i))

theorem W5_DeepLearningTheory_prod_integral {N : ℕ} (m : Fin N → ℕ) :
    ∫ w : Fin N → ℝ, ∏ i, (w i ^ m i * Real.exp (-(1 / 2) * w i ^ 2)) =
      ∏ i, W5_DeepLearningTheory_M (m i) :=
  integral_fintype_prod_volume_eq_prod (fun i (x : ℝ) => x ^ m i * Real.exp (-(1 / 2) * x ^ 2))

/-! ### Matrix facts -/

theorem W5_DeepLearningTheory_decomp {N : ℕ} (K : Matrix (Fin N) (Fin N) ℝ) (hK : K.PosDef) :
    ∃ C : Matrix (Fin N) (Fin N) ℝ, K = C * C.transpose ∧ C.det ≠ 0 := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hK.posSemidef.nonneg
  have hK' : K = B.transpose * B.transpose.transpose := by
    rw [hB, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.transpose_transpose]
  refine ⟨B.transpose, hK', fun h => ?_⟩
  have hpos := hK.det_pos
  rw [hK', Matrix.det_mul, h, zero_mul] at hpos
  exact lt_irrefl _ hpos

theorem W5_DeepLearningTheory_quad {N : ℕ} (K C : Matrix (Fin N) (Fin N) ℝ)
    (hKC : K = C * C.transpose) (hC : C.det ≠ 0) (w : Fin N → ℝ) :
    gaussQuadForm K (C *ᵥ w) = ∑ i, w i ^ 2 := by
  have h1 : ∀ z : Fin N → ℝ, gaussQuadForm K z = z ⬝ᵥ (K⁻¹ *ᵥ z) := by
    intro z
    simp only [gaussQuadForm, dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => by ring
  have hCi : C.transpose * K⁻¹ * C = 1 := by
    have hu : IsUnit C.det := isUnit_iff_ne_zero.mpr hC
    have hut : IsUnit C.transpose.det := by rwa [Matrix.det_transpose]
    rw [hKC, Matrix.mul_inv_rev, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hut,
      Matrix.one_mul, Matrix.nonsing_inv_mul _ hu]
  rw [h1, Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose C w, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hCi, Matrix.one_mulVec]
  simp [dotProduct, sq]

theorem W5_DeepLearningTheory_cov {N : ℕ} (C : Matrix (Fin N) (Fin N) ℝ) (hC : C.det ≠ 0)
    (f : (Fin N → ℝ) → ℝ) (hf : Continuous f) :
    ∫ z, f z = |C.det| * ∫ w, f (C *ᵥ w) := by
  have hmap := Real.map_matrix_volume_pi_eq_smul_volume_pi hC
  have hm : Measurable (Matrix.toLin' C) :=
    (Matrix.toLin' C).continuous_of_finiteDimensional.measurable
  have h1 : ∫ w, f (C *ᵥ w) = ∫ z, f z ∂(Measure.map (Matrix.toLin' C) volume) := by
    rw [integral_map hm.aemeasurable hf.aestronglyMeasurable]
    simp only [Matrix.toLin'_apply]
  rw [h1, hmap, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _), smul_eq_mul,
    ← mul_assoc, abs_inv, mul_inv_cancel₀ (abs_ne_zero.mpr hC), one_mul]

theorem W5_DeepLearningTheory_final {N : ℕ} (K C : Matrix (Fin N) (Fin N) ℝ)
    (hKC : K = C * C.transpose) :
    |C.det| * Real.sqrt (2 * π) ^ N = Real.sqrt ((2 * π) ^ N * K.det) := by
  have hs : Real.sqrt ((2 * π) ^ N) = Real.sqrt (2 * π) ^ N := by
    rw [← Real.sqrt_sq (pow_nonneg (Real.sqrt_nonneg (2 * π)) N), ← pow_mul, pow_mul',
      Real.sq_sqrt (by positivity)]
  rw [hKC, Matrix.det_mul, Matrix.det_transpose,
    Real.sqrt_mul (pow_nonneg (by positivity) N : (0 : ℝ) ≤ (2 * π) ^ N) (C.det * C.det),
    Real.sqrt_mul_self_eq_abs, hs, mul_comm]

theorem W5_DeepLearningTheory_quad_cont {N : ℕ} (K : Matrix (Fin N) (Fin N) ℝ) :
    Continuous (fun z : Fin N → ℝ => gaussQuadForm K z) := by
  unfold gaussQuadForm
  fun_prop

/-! ### Targets -/

theorem solution {N : ℕ} (K : Matrix (Fin N) (Fin N) ℝ)
    (hK : K.PosDef) :
    ∫ z : Fin N → ℝ, Real.exp (-(1 / 2) * gaussQuadForm K z)
      = Real.sqrt ((2 * Real.pi) ^ N * K.det) := by
  obtain ⟨C, hKC, hC⟩ := W5_DeepLearningTheory_decomp K hK
  rw [W5_DeepLearningTheory_cov C hC _ (by
    have := W5_DeepLearningTheory_quad_cont K
    fun_prop)]
  simp_rw [W5_DeepLearningTheory_quad K C hKC hC]
  have hw : ∀ w : Fin N → ℝ, Real.exp (-(1 / 2) * ∑ i, w i ^ 2) =
      ∏ i, (w i ^ (fun _ : Fin N => 0) i * Real.exp (-(1 / 2) * w i ^ 2)) := by
    intro w
    rw [Finset.mul_sum, Real.exp_sum]
    simp
  simp_rw [hw]
  rw [W5_DeepLearningTheory_prod_integral (fun _ => 0)]
  simp only [W5_DeepLearningTheory_M0, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact W5_DeepLearningTheory_final K C hKC

theorem W5_DeepLearningTheory_shift (c : ℝ) :
    ∫ x : ℝ, Real.exp (-(1 / 2) * x ^ 2 + c * x) = Real.sqrt (2 * π) * Real.exp (c ^ 2 / 2) := by
  rw [← integral_add_right_eq_self (fun x : ℝ => Real.exp (-(1 / 2) * x ^ 2 + c * x)) c]
  have h : ∀ x : ℝ, Real.exp (-(1 / 2) * (x + c) ^ 2 + c * (x + c)) =
      Real.exp (c ^ 2 / 2) * Real.exp (-(1 / 2) * x ^ 2) := by
    intro x
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [h]
  rw [integral_const_mul]
  have := W5_DeepLearningTheory_M0
  simp only [W5_DeepLearningTheory_M, pow_zero, one_mul] at this
  rw [this]
  ring

theorem W5_DeepLearningTheory_gaussian_generating_function {N : ℕ} (K : Matrix (Fin N) (Fin N) ℝ)
    (hK : K.PosDef) (J : Fin N → ℝ) :
    ∫ z : Fin N → ℝ, Real.exp (-(1 / 2) * gaussQuadForm K z + ∑ μ : Fin N, J μ * z μ)
      = Real.sqrt ((2 * Real.pi) ^ N * K.det) *
          Real.exp ((1 / 2) * ∑ μ : Fin N, ∑ ν : Fin N, J μ * K μ ν * J ν) := by
  obtain ⟨C, hKC, hC⟩ := W5_DeepLearningTheory_decomp K hK
  rw [W5_DeepLearningTheory_cov C hC _ (by
    have := W5_DeepLearningTheory_quad_cont K
    fun_prop)]
  set c : Fin N → ℝ := C.transpose *ᵥ J with hc
  have hlin : ∀ w : Fin N → ℝ, ∑ μ : Fin N, J μ * (C *ᵥ w) μ = ∑ i, c i * w i := by
    intro w
    change J ⬝ᵥ (C *ᵥ w) = c ⬝ᵥ w
    rw [Matrix.dotProduct_mulVec, hc, Matrix.mulVec_transpose]
  have hw : ∀ w : Fin N → ℝ,
      Real.exp (-(1 / 2) * gaussQuadForm K (C *ᵥ w) + ∑ μ : Fin N, J μ * (C *ᵥ w) μ) =
        ∏ i, Real.exp (-(1 / 2) * w i ^ 2 + c i * w i) := by
    intro w
    rw [W5_DeepLearningTheory_quad K C hKC hC, hlin, ← Real.exp_sum, Finset.sum_add_distrib,
      Finset.mul_sum]
  simp_rw [hw]
  rw [integral_fintype_prod_volume_eq_prod (fun i (x : ℝ) => Real.exp (-(1 / 2) * x ^ 2 + c i * x))]
  simp only [W5_DeepLearningTheory_shift, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, ← Real.exp_sum]
  have hq : ∑ μ : Fin N, ∑ ν : Fin N, J μ * K μ ν * J ν = ∑ i, c i ^ 2 := by
    have e1 : ∑ μ : Fin N, ∑ ν : Fin N, J μ * K μ ν * J ν = J ⬝ᵥ (K *ᵥ J) := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
      refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => by ring
    have e2 : ∑ i, c i ^ 2 = c ⬝ᵥ c := by simp [dotProduct, sq]
    rw [e1, e2, hKC, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, hc,
      Matrix.mulVec_transpose]
  rw [hq, ← W5_DeepLearningTheory_final K C hKC]
  have e : ∑ i, c i ^ 2 / 2 = (1 / 2) * ∑ i, c i ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  ring

/-! ### Two- and four-point functions -/

theorem W5_DeepLearningTheory_s_pos : 0 < Real.sqrt (2 * π) := Real.sqrt_pos.mpr (by positivity)

theorem W5_DeepLearningTheory_K_apply {N : ℕ} (K C : Matrix (Fin N) (Fin N) ℝ)
    (hKC : K = C * C.transpose) (a b : Fin N) : K a b = ∑ c, C a c * C b c := by
  rw [hKC, Matrix.mul_apply]
  simp [Matrix.transpose_apply]

theorem W5_DeepLearningTheory_const {N : ℕ} (K C : Matrix (Fin N) (Fin N) ℝ)
    (hKC : K = C * C.transpose) (hC : C.det ≠ 0) :
    |C.det| * ((Real.sqrt ((2 * π) ^ N * K.det))⁻¹ * Real.sqrt (2 * π) ^ N) = 1 := by
  have h := W5_DeepLearningTheory_final K C hKC
  have hpos : 0 < Real.sqrt ((2 * π) ^ N * K.det) := by
    rw [← h]
    exact mul_pos (abs_pos.mpr hC) (pow_pos W5_DeepLearningTheory_s_pos N)
  rw [← mul_assoc, mul_comm |C.det|, mul_assoc, h, inv_mul_cancel₀ hpos.ne']

theorem W5_DeepLearningTheory_sum2_mul {N : ℕ} (F : Fin N → Fin N → ℝ) (h : Fin N → ℝ) :
    (∑ a, ∑ b, F a b) * (∑ c, h c) = ∑ a, ∑ b, ∑ c, F a b * h c := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]

theorem W5_DeepLearningTheory_sum3_mul {N : ℕ} (F : Fin N → Fin N → Fin N → ℝ) (h : Fin N → ℝ) :
    (∑ a, ∑ b, ∑ c, F a b c) * (∑ d, h d) = ∑ a, ∑ b, ∑ c, ∑ d, F a b c * h d := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.mul_sum]

theorem W5_DeepLearningTheory_int2 {N : ℕ} (F : Fin N → Fin N → (Fin N → ℝ) → ℝ)
    (hF : ∀ a b, Integrable (F a b)) :
    ∫ w, ∑ a, ∑ b, F a b w = ∑ a, ∑ b, ∫ w, F a b w := by
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ fun b _ => hF a b)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finsetSum _ (fun b _ => hF a b)]

theorem W5_DeepLearningTheory_int4 {N : ℕ} (F : Fin N → Fin N → Fin N → Fin N → (Fin N → ℝ) → ℝ)
    (hF : ∀ a b c d, Integrable (F a b c d)) :
    ∫ w, ∑ a, ∑ b, ∑ c, ∑ d, F a b c d w = ∑ a, ∑ b, ∑ c, ∑ d, ∫ w, F a b c d w := by
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ fun b _ =>
    integrable_finsetSum _ fun c _ => integrable_finsetSum _ fun d _ => hF a b c d)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finsetSum _ (fun b _ => integrable_finsetSum _ fun c _ =>
    integrable_finsetSum _ fun d _ => hF a b c d)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_finsetSum _ (fun c _ => integrable_finsetSum _ fun d _ => hF a b c d)]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [integral_finsetSum _ (fun d _ => hF a b c d)]

theorem W5_DeepLearningTheory_T1 {N : ℕ} (P : Fin N → Fin N → Fin N → Fin N → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ d, P a b c d * ((if a = b then (1 : ℝ) else 0) * (if c = d then 1 else 0))
      = ∑ a, ∑ c, P a a c c := by
  refine Finset.sum_congr rfl fun a _ => ?_
  have h : ∀ b, ∑ c, ∑ d, P a b c d * ((if a = b then (1 : ℝ) else 0) * (if c = d then 1 else 0))
      = (∑ c, P a b c c) * (if a = b then 1 else 0) := by
    intro b
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp_rw [← mul_assoc]
    rw [Finset.sum_mul_boole]
    simp
  rw [Finset.sum_congr rfl fun b _ => h b, Finset.sum_mul_boole]
  simp

theorem W5_DeepLearningTheory_T2 {N : ℕ} (P : Fin N → Fin N → Fin N → Fin N → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ d, P a b c d * ((if a = c then (1 : ℝ) else 0) * (if b = d then 1 else 0))
      = ∑ a, ∑ b, P a b a b := by
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have h : ∀ c, ∑ d, P a b c d * ((if a = c then (1 : ℝ) else 0) * (if b = d then 1 else 0))
      = P a b c b * (if a = c then 1 else 0) := by
    intro c
    simp_rw [← mul_assoc]
    rw [Finset.sum_mul_boole]
    simp
  rw [Finset.sum_congr rfl fun c _ => h c, Finset.sum_mul_boole]
  simp

theorem W5_DeepLearningTheory_T3 {N : ℕ} (P : Fin N → Fin N → Fin N → Fin N → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ d, P a b c d * ((if a = d then (1 : ℝ) else 0) * (if b = c then 1 else 0))
      = ∑ a, ∑ b, P a b b a := by
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have h : ∀ c, ∑ d, P a b c d * ((if a = d then (1 : ℝ) else 0) * (if b = c then 1 else 0))
      = P a b c a * (if b = c then 1 else 0) := by
    intro c
    simp_rw [mul_comm (if a = _ then (1 : ℝ) else 0), ← mul_assoc]
    rw [Finset.sum_mul_boole]
    simp
  rw [Finset.sum_congr rfl fun c _ => h c, Finset.sum_mul_boole]
  simp

theorem W5_DeepLearningTheory_mono2 {N : ℕ} (c d : Fin N) (w : Fin N → ℝ) :
    ∏ i, (w i ^ ((if c = i then 1 else 0) + (if d = i then 1 else 0)) *
      Real.exp (-(1 / 2) * w i ^ 2)) = w c * w d * Real.exp (-(1 / 2) * ∑ i, w i ^ 2) := by
  rw [Finset.prod_mul_distrib]
  simp_rw [pow_add]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_boole, Finset.prod_pow_boole, Finset.mul_sum,
    Real.exp_sum]
  simp

theorem W5_DeepLearningTheory_mono4 {N : ℕ} (a b c d : Fin N) (w : Fin N → ℝ) :
    ∏ i, (w i ^ ((if a = i then 1 else 0) + (if b = i then 1 else 0) + (if c = i then 1 else 0)
      + (if d = i then 1 else 0)) * Real.exp (-(1 / 2) * w i ^ 2)) =
      w a * w b * w c * w d * Real.exp (-(1 / 2) * ∑ i, w i ^ 2) := by
  rw [Finset.prod_mul_distrib]
  simp_rw [pow_add]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_pow_boole, Finset.prod_pow_boole, Finset.prod_pow_boole, Finset.prod_pow_boole,
    Finset.mul_sum, Real.exp_sum]
  simp

theorem W5_DeepLearningTheory_two_eval {N : ℕ} (c d : Fin N) :
    ∏ i, W5_DeepLearningTheory_M ((if c = i then 1 else 0) + (if d = i then 1 else 0)) =
      if c = d then Real.sqrt (2 * π) ^ N else 0 := by
  split_ifs with h
  · subst h
    rw [Finset.prod_congr rfl (fun i _ => (show W5_DeepLearningTheory_M
        ((if c = i then 1 else 0) + (if c = i then 1 else 0)) = Real.sqrt (2 * π) by
      by_cases hi : c = i <;> simp [hi, W5_DeepLearningTheory_M0, W5_DeepLearningTheory_M2]))]
    simp
  · exact Finset.prod_eq_zero (Finset.mem_univ c)
      (by simp [h, Ne.symm h, W5_DeepLearningTheory_M1])

theorem W5_DeepLearningTheory_four_eval {N : ℕ} (c1 c2 c3 c4 : Fin N) :
    ∏ i, W5_DeepLearningTheory_M ((if c1 = i then 1 else 0) + (if c2 = i then 1 else 0) +
      (if c3 = i then 1 else 0) + (if c4 = i then 1 else 0)) =
      Real.sqrt (2 * π) ^ N *
        ((if c1 = c2 then 1 else 0) * (if c3 = c4 then 1 else 0) +
          (if c1 = c3 then 1 else 0) * (if c2 = c4 then 1 else 0) +
          (if c1 = c4 then 1 else 0) * (if c2 = c3 then 1 else 0)) := by
  have hs : Real.sqrt (2 * π) ≠ 0 := W5_DeepLearningTheory_s_pos.ne'
  have hfac : ∀ f : Fin N → ℝ, ∏ i, f i = Real.sqrt (2 * π) ^ N * ∏ i, (f i / Real.sqrt (2 * π)) := by
    intro f
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      mul_div_cancel₀ _ (pow_ne_zero N hs)]
  rw [hfac]
  congr 1
  have g0 : W5_DeepLearningTheory_M 0 / Real.sqrt (2 * π) = 1 := by
    rw [W5_DeepLearningTheory_M0, div_self hs]
  have g1 : W5_DeepLearningTheory_M 1 / Real.sqrt (2 * π) = 0 := by
    rw [W5_DeepLearningTheory_M1, zero_div]
  have g2 : W5_DeepLearningTheory_M 2 / Real.sqrt (2 * π) = 1 := by
    rw [W5_DeepLearningTheory_M2, div_self hs]
  have g3 : W5_DeepLearningTheory_M 3 / Real.sqrt (2 * π) = 0 := by
    rw [W5_DeepLearningTheory_M3, zero_div]
  have g4 : W5_DeepLearningTheory_M 4 / Real.sqrt (2 * π) = 3 := by
    rw [W5_DeepLearningTheory_M4, mul_div_assoc, div_self hs, mul_one]
  generalize Real.sqrt (2 * π) = S at g0 g1 g2 g3 g4 ⊢
  by_cases a : c1 = c2 <;> by_cases b : c1 = c3 <;> by_cases c : c1 = c4
  · subst a b c
    rw [Finset.prod_eq_single c1 (fun i _ hi => by simp [Ne.symm hi, g0])
      (fun h => absurd (Finset.mem_univ _) h)]
    norm_num [g4]
  · subst a b
    rw [Finset.prod_eq_zero (Finset.mem_univ c1) (by simp [Ne.symm c, g3])]
    simp [c, Ne.symm c]
  · subst a c
    rw [Finset.prod_eq_zero (Finset.mem_univ c1) (by simp [Ne.symm b, g3])]
    simp [b, Ne.symm b]
  · subst a
    by_cases d : c3 = c4
    · subst d
      rw [Finset.prod_eq_one (fun i _ => by
        by_cases h1 : c1 = i
        · subst h1; simp [b, Ne.symm b, g2]
        · by_cases h3 : c3 = i
          · subst h3; simp [b, Ne.symm b, g2]
          · simp [h1, h3, g0])]
      simp [b, Ne.symm b]
    · rw [Finset.prod_eq_zero (Finset.mem_univ c3) (by simp [b, Ne.symm d, g1])]
      simp [b, c, d]
  · subst b c
    rw [Finset.prod_eq_zero (Finset.mem_univ c1) (by simp [Ne.symm a, g3])]
    simp [a, Ne.symm a]
  · subst b
    by_cases d : c2 = c4
    · subst d
      rw [Finset.prod_eq_one (fun i _ => by
        by_cases h1 : c1 = i
        · subst h1; simp [a, Ne.symm a, g2]
        · by_cases h2 : c2 = i
          · subst h2; simp [a, Ne.symm a, g2]
          · simp [h1, h2, g0])]
      simp [a, Ne.symm a]
    · rw [Finset.prod_eq_zero (Finset.mem_univ c2) (by simp [a, Ne.symm d, g1])]
      simp [a, c, d]
  · subst c
    by_cases d : c2 = c3
    · subst d
      rw [Finset.prod_eq_one (fun i _ => by
        by_cases h1 : c1 = i
        · subst h1; simp [a, Ne.symm a, g2]
        · by_cases h2 : c2 = i
          · subst h2; simp [a, Ne.symm a, g2]
          · simp [h1, h2, g0])]
      simp [a, Ne.symm a]
    · rw [Finset.prod_eq_zero (Finset.mem_univ c2) (by simp [a, Ne.symm d, g1])]
      simp [a, b, d]
  · rw [Finset.prod_eq_zero (Finset.mem_univ c1)
      (by simp [Ne.symm a, Ne.symm b, Ne.symm c, g1])]
    simp [a, b, c]

theorem W5_DeepLearningTheory_gaussian_two_point {N : ℕ} (K : Matrix (Fin N) (Fin N) ℝ) (hK : K.PosDef)
    (μ₁ μ₂ : Fin N) :
    gaussExpect K (fun z => z μ₁ * z μ₂) = K μ₁ μ₂ := by
  obtain ⟨C, hKC, hC⟩ := W5_DeepLearningTheory_decomp K hK
  unfold gaussExpect gaussianDensity
  rw [W5_DeepLearningTheory_cov C hC _ (by
    have := W5_DeepLearningTheory_quad_cont K
    fun_prop)]
  simp_rw [W5_DeepLearningTheory_quad K C hKC hC]
  set D := (Real.sqrt ((2 * π) ^ N * K.det))⁻¹ with hD
  have hexp : ∀ w : Fin N → ℝ, D * Real.exp (-(1 / 2) * ∑ i, w i ^ 2) *
      ((C *ᵥ w) μ₁ * (C *ᵥ w) μ₂) = ∑ c, ∑ d, (D * (C μ₁ c * C μ₂ d)) *
        ∏ i, (w i ^ ((if c = i then 1 else 0) + (if d = i then 1 else 0)) *
          Real.exp (-(1 / 2) * w i ^ 2)) := by
    intro w
    simp only [W5_DeepLearningTheory_mono2]
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_mul_sum]
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring
  simp_rw [hexp]
  rw [W5_DeepLearningTheory_int2]
  swap
  · intro a b
    exact (W5_DeepLearningTheory_prod_integrable _).const_mul _
  simp only [integral_const_mul, W5_DeepLearningTheory_prod_integral,
    W5_DeepLearningTheory_two_eval, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]
  rw [W5_DeepLearningTheory_K_apply K C hKC, Finset.mul_sum]
  have h1 := W5_DeepLearningTheory_const K C hKC hC
  rw [← hD] at h1
  calc _ = ∑ i, (|C.det| * (D * Real.sqrt (2 * π) ^ N)) * (C μ₁ i * C μ₂ i) :=
        Finset.sum_congr rfl fun i _ => by ring
    _ = _ := by simp only [h1, one_mul]

theorem W5_DeepLearningTheory_gaussian_four_point {N : ℕ} (K : Matrix (Fin N) (Fin N) ℝ) (hK : K.PosDef)
    (μ₁ μ₂ μ₃ μ₄ : Fin N) :
    gaussExpect K (fun z => z μ₁ * z μ₂ * z μ₃ * z μ₄)
      = K μ₁ μ₂ * K μ₃ μ₄ + K μ₁ μ₃ * K μ₂ μ₄ + K μ₁ μ₄ * K μ₂ μ₃ := by
  obtain ⟨C, hKC, hC⟩ := W5_DeepLearningTheory_decomp K hK
  unfold gaussExpect gaussianDensity
  rw [W5_DeepLearningTheory_cov C hC _ (by
    have := W5_DeepLearningTheory_quad_cont K
    fun_prop)]
  simp_rw [W5_DeepLearningTheory_quad K C hKC hC]
  set D := (Real.sqrt ((2 * π) ^ N * K.det))⁻¹ with hD
  have hexp : ∀ w : Fin N → ℝ, D * Real.exp (-(1 / 2) * ∑ i, w i ^ 2) *
      ((C *ᵥ w) μ₁ * (C *ᵥ w) μ₂ * (C *ᵥ w) μ₃ * (C *ᵥ w) μ₄) =
      ∑ a, ∑ b, ∑ c, ∑ d, (D * (C μ₁ a * C μ₂ b * C μ₃ c * C μ₄ d)) *
        ∏ i, (w i ^ ((if a = i then 1 else 0) + (if b = i then 1 else 0) +
          (if c = i then 1 else 0) + (if d = i then 1 else 0)) *
          Real.exp (-(1 / 2) * w i ^ 2)) := by
    intro w
    simp only [W5_DeepLearningTheory_mono4]
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_mul_sum, W5_DeepLearningTheory_sum2_mul, W5_DeepLearningTheory_sum3_mul]
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring
  simp_rw [hexp]
  rw [W5_DeepLearningTheory_int4]
  swap
  · intro a b c d
    exact (W5_DeepLearningTheory_prod_integrable _).const_mul _
  simp only [integral_const_mul, W5_DeepLearningTheory_prod_integral,
    W5_DeepLearningTheory_four_eval]
  have h1 := W5_DeepLearningTheory_const K C hKC hC
  rw [← hD] at h1
  have e : ∀ a b c d : Fin N,
      D * (C μ₁ a * C μ₂ b * C μ₃ c * C μ₄ d) * (Real.sqrt (2 * π) ^ N *
        ((if a = b then 1 else 0) * (if c = d then 1 else 0) +
          (if a = c then 1 else 0) * (if b = d then 1 else 0) +
          (if a = d then 1 else 0) * (if b = c then 1 else 0))) =
      (D * Real.sqrt (2 * π) ^ N) *
        (C μ₁ a * C μ₂ b * C μ₃ c * C μ₄ d *
          ((if a = b then (1 : ℝ) else 0) * (if c = d then 1 else 0)) +
        C μ₁ a * C μ₂ b * C μ₃ c * C μ₄ d *
          ((if a = c then (1 : ℝ) else 0) * (if b = d then 1 else 0)) +
        C μ₁ a * C μ₂ b * C μ₃ c * C μ₄ d *
          ((if a = d then (1 : ℝ) else 0) * (if b = c then 1 else 0))) := by
    intro a b c d
    ring
  simp only [e, ← Finset.mul_sum, Finset.sum_add_distrib]
  rw [W5_DeepLearningTheory_T1, W5_DeepLearningTheory_T2, W5_DeepLearningTheory_T3,
    show ∀ X : ℝ, |C.det| * (D * Real.sqrt (2 * π) ^ N * X) = X from
      fun X => by rw [← mul_assoc, h1, one_mul]]
  simp only [W5_DeepLearningTheory_K_apply K C hKC, Finset.sum_mul_sum]
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring
