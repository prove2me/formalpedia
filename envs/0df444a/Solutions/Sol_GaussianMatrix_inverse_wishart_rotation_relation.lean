-- Prove2me | solution 1 for GaussianMatrix.inverse_wishart_rotation_relation
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T06:29:50.698407+00:00
-- url     : https://prove2.me/submissions/a7e4a19f-2a8c-4975-b56f-89cd0e6bdd5c

import Definitions.Def_GaussianMatrix_basic
import Theorems.Thm_GaussianMatrix_rotation_invariance
import Theorems.Thm_GaussianMatrix_inverse_wishart_diag_sq_moment

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

/-- The 45-degree rotation in the `(i, j)` coordinate plane. -/
noncomputable def iwrRot {r : ℕ} (i j : Fin r) : Matrix (Fin r) (Fin r) ℝ :=
  Matrix.of fun a => if a = i then (Real.sqrt 2)⁻¹ • (Pi.single i 1 + Pi.single j 1)
    else if a = j then (Real.sqrt 2)⁻¹ • (Pi.single j 1 - Pi.single i 1) else Pi.single a 1

lemma iwr_c_sq : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (1 / 2 : ℝ) := by
  rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]; norm_num

lemma iwrRot_orth {r : ℕ} (i j : Fin r) (hij : i ≠ j) :
    (iwrRot i j)ᵀ * iwrRot i j = 1 := by
  rw [mul_eq_one_comm]
  ext a b
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply]
  have hc := iwr_c_sq
  have hji : j ≠ i := Ne.symm hij
  by_cases hai : a = i <;> by_cases haj : a = j <;> by_cases hbi : b = i <;> by_cases hbj : b = j <;>
    simp_all [iwrRot, Pi.single_apply, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Matrix.one_apply, mul_add, add_mul, sub_mul, mul_sub, eq_comm] <;>
    linarith


lemma iwrRot_conj_apply {r : ℕ} (i j : Fin r) (N : Matrix (Fin r) (Fin r) ℝ) :
    (iwrRot i j * N * (iwrRot i j)ᵀ) i i = (N i i + N i j + N j i + N j j) / 2 := by
  have hc := iwr_c_sq
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  simp [iwrRot, Pi.single_apply, Finset.sum_add_distrib, add_mul, mul_add, eq_comm]
  linear_combination (-(N i i + N j i + N i j + N j j)) * hc

lemma iwr_measurable_inv_entry {r k : ℕ} (i j : Fin r) :
    Measurable (fun G : Fin r → Fin k → ℝ => (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i j) := by
  have hc : Continuous (fun G : Fin r → Fin k → ℝ => Matrix.of G * (Matrix.of G)ᵀ) :=
    Continuous.matrix_mul continuous_id (Continuous.matrix_transpose continuous_id)
  simp_rw [Matrix.inv_def, Ring.inverse_eq_inv']
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact (hc.matrix_det.measurable.inv).mul (hc.matrix_adjugate.matrix_elem i j).measurable

/-- The inverse Wishart matrix transforms by conjugation under a left orthogonal rotation. -/
lemma iwr_inv_conj {r k : ℕ} (U : Matrix (Fin r) (Fin r) ℝ) (hU : Uᵀ * U = 1)
    (G : Fin r → Fin k → ℝ) :
    (Matrix.of (Matrix.of.symm (U * Matrix.of G * (1 : Matrix (Fin k) (Fin k) ℝ))) *
        (Matrix.of (Matrix.of.symm (U * Matrix.of G * (1 : Matrix (Fin k) (Fin k) ℝ))))ᵀ)⁻¹
      = U * (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ * Uᵀ := by
  have hUinv : U⁻¹ = Uᵀ := Matrix.inv_eq_left_inv hU
  simp only [Equiv.apply_symm_apply, Matrix.mul_one, Matrix.transpose_mul]
  rw [show U * Matrix.of G * ((Matrix.of G)ᵀ * Uᵀ) = U * (Matrix.of G * (Matrix.of G)ᵀ) * Uᵀ by
    simp [Matrix.mul_assoc]]
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← Matrix.transpose_nonsing_inv, hUinv,
    Matrix.transpose_transpose, Matrix.mul_assoc]

/-- Invariance of the inverse-Wishart law under orthogonal conjugation. -/
lemma iwr_integral_conj {r k : ℕ} (U : Matrix (Fin r) (Fin r) ℝ) (hU : Uᵀ * U = 1)
    (F : Matrix (Fin r) (Fin r) ℝ → ℝ)
    (hF : Measurable (fun G : Fin r → Fin k → ℝ => F (Matrix.of G * (Matrix.of G)ᵀ)⁻¹)) :
    ∫ G, F (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ ∂(gaussianMatrix r k)
      = ∫ G, F (U * (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ * Uᵀ) ∂(gaussianMatrix r k) := by
  have hrot := rotation_invariance U (1 : Matrix (Fin k) (Fin k) ℝ) hU (by simp)
  have hmeas : Measurable (fun G : Fin r → Fin k → ℝ =>
      Matrix.of.symm (U * Matrix.of G * (1 : Matrix (Fin k) (Fin k) ℝ))) := by
    refine measurable_pi_lambda _ fun a => measurable_pi_lambda _ fun b => ?_
    simp only [Matrix.of_symm_apply, Matrix.mul_one, Matrix.mul_apply, Matrix.of_apply]
    fun_prop
  have h1 : ∫ G, F (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ ∂(gaussianMatrix r k) =
      ∫ G, F (Matrix.of G * (Matrix.of G)ᵀ)⁻¹
        ∂(Measure.map (fun G => Matrix.of.symm (U * Matrix.of G *
          (1 : Matrix (Fin k) (Fin k) ℝ))) (gaussianMatrix r k)) := by
    rw [hrot]
  rw [integral_map hmeas.aemeasurable hF.aestronglyMeasurable] at h1
  simp_rw [iwr_inv_conj U hU] at h1
  exact h1

/-- The sign flip of coordinate `j`. -/
noncomputable def iwrFlip {r : ℕ} (j : Fin r) : Matrix (Fin r) (Fin r) ℝ :=
  Matrix.diagonal fun a => if a = j then -1 else 1

lemma iwrFlip_orth {r : ℕ} (j : Fin r) : (iwrFlip j)ᵀ * iwrFlip j = 1 := by
  rw [iwrFlip, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext a; split_ifs <;> norm_num

lemma iwrFlip_conj_apply {r : ℕ} (j : Fin r) (N : Matrix (Fin r) (Fin r) ℝ) (a b : Fin r) :
    (iwrFlip j * N * (iwrFlip j)ᵀ) a b
      = (if a = j then -1 else 1) * N a b * (if b = j then -1 else 1) := by
  simp [iwrFlip, Matrix.diagonal_transpose, Matrix.diagonal_mul, Matrix.mul_diagonal]

lemma iwr_psd_inv {r k : ℕ} (G : Fin r → Fin k → ℝ) :
    ((Matrix.of G * (Matrix.of G)ᵀ)⁻¹).PosSemidef := by
  have := Matrix.posSemidef_self_mul_conjTranspose (Matrix.of G)
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  exact this.inv

lemma iwr_psd_offdiag {r : ℕ} (M : Matrix (Fin r) (Fin r) ℝ) (hM : M.PosSemidef) (i j : Fin r) :
    |M i j| ≤ M i i + M j j := by
  have hs : M j i = M i j := by
    have := hM.isHermitian.apply i j
    simpa using this
  by_cases hij : i = j
  · subst hij
    have := hM.diag_nonneg (i := i)
    rw [abs_of_nonneg this]; linarith
  have h1 := hM.dotProduct_mulVec_nonneg (Pi.single i 1 + Pi.single j 1)
  have h2 := hM.dotProduct_mulVec_nonneg (Pi.single i 1 - Pi.single j 1)
  simp [Matrix.mulVec_add, Matrix.mulVec_sub, add_dotProduct, dotProduct_add,
    sub_dotProduct, dotProduct_sub, Matrix.mulVec_single, single_dotProduct,
    hs] at h1 h2
  rw [abs_le]; constructor <;> linarith

lemma iwr_symm {r k : ℕ} (G : Fin r → Fin k → ℝ) (i j : Fin r) :
    (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ j i = (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i j := by
  have := (iwr_psd_inv G).isHermitian.apply i j
  simpa using this

/-- A product of two integrable-square functions is integrable. -/
lemma iwr_integrable_mul {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hf : Measurable f) (hg : Measurable g)
    (hf2 : Integrable (fun x => f x ^ 2) μ) (hg2 : Integrable (fun x => g x ^ 2) μ) :
    Integrable (fun x => f x * g x) μ := by
  refine (hf2.add hg2).mono' (hf.mul hg).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_le]
  simp only [Pi.add_apply]
  constructor <;> nlinarith [sq_nonneg (f x + g x), sq_nonneg (f x - g x)]

end GaussianMatrix

open GaussianMatrix

theorem solution {r k : ℕ} (hrk : r + 4 ≤ k) (i j : Fin r) (hij : i ≠ j) :
    ∫ G, (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i i ^ 2 ∂(gaussianMatrix r k)
      = ∫ G, (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i i * (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ j j
            ∂(gaussianMatrix r k)
        + 2 * ∫ G, (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i j ^ 2 ∂(gaussianMatrix r k) := by
  set μ := gaussianMatrix r k with hμ
  set M : (Fin r → Fin k → ℝ) → Matrix (Fin r) (Fin r) ℝ :=
    fun G => (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ with hM
  have hm : ∀ a b : Fin r, Measurable (fun G => M G a b) := fun a b => iwr_measurable_inv_entry a b
  obtain ⟨hx2, hxval⟩ := inverse_wishart_diag_sq_moment hrk i
  obtain ⟨hy2, hyval⟩ := inverse_wishart_diag_sq_moment hrk j
  have hz2 : Integrable (fun G => M G i j ^ 2) μ := by
    refine Integrable.mono' ((hx2.add hy2).const_mul 2)
      ((hm i j).pow_const 2).aestronglyMeasurable (Filter.Eventually.of_forall fun G => ?_)
    have h := iwr_psd_offdiag _ (iwr_psd_inv G) i j
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have : M G i j ^ 2 ≤ (M G i i + M G j j) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h 2
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (M G i i - M G j j)]
  have hxy := iwr_integrable_mul (hm i i) (hm j j) hx2 hy2
  have hxz := iwr_integrable_mul (hm i i) (hm i j) hx2 hz2
  have hyz := iwr_integrable_mul (hm j j) (hm i j) hy2 hz2
  -- sign flip of coordinate `j` kills the mixed moments
  have hflip : ∀ a : Fin r, a ≠ j → ∫ G, M G a a * M G i j ∂μ = 0 := by
    intro a haj
    have h := iwr_integral_conj (k := k) (iwrFlip j) (iwrFlip_orth j)
      (fun N => N a a * N i j) ((hm a a).mul (hm i j))
    simp only [iwrFlip_conj_apply] at h
    have h2 : ∫ G, M G a a * M G i j ∂μ = -∫ G, M G a a * M G i j ∂μ := by
      rw [← integral_neg]
      refine h.trans (integral_congr_ae (ae_of_all _ fun G => ?_))
      simp [haj, hij, hM]
    linarith
  have hflip' : ∫ G, M G j j * M G i j ∂μ = 0 := by
    have h := iwr_integral_conj (k := k) (iwrFlip i) (iwrFlip_orth i)
      (fun N => N j j * N i j) ((hm j j).mul (hm i j))
    simp only [iwrFlip_conj_apply] at h
    have h2 : ∫ G, M G j j * M G i j ∂μ = -∫ G, M G j j * M G i j ∂μ := by
      rw [← integral_neg]
      refine h.trans (integral_congr_ae (ae_of_all _ fun G => ?_))
      simp [Ne.symm hij, hM]
    linarith
  have hxz0 := hflip i hij
  -- the 45-degree rotation
  have hrot := iwr_integral_conj (k := k) (iwrRot i j) (iwrRot_orth i j hij)
    (fun N => N i i ^ 2) ((hm i i).pow_const 2)
  simp only [iwrRot_conj_apply i j] at hrot
  change ∫ G, M G i i ^ 2 ∂μ = ∫ G, ((M G i i + M G i j + M G j i + M G j j) / 2) ^ 2 ∂μ at hrot
  have hexp : (fun G => ((M G i i + M G i j + M G j i + M G j j) / 2) ^ 2)
      = fun G => (1 / 4 : ℝ) * (((((M G i i ^ 2 + M G j j ^ 2) + 4 * M G i j ^ 2)
          + 2 * (M G i i * M G j j)) + 4 * (M G i i * M G i j)) + 4 * (M G j j * M G i j)) := by
    funext G
    rw [show M G j i = M G i j from iwr_symm G i j]
    ring
  have hx2' : Integrable (fun G => M G i i ^ 2) μ := hx2
  have hy2' : Integrable (fun G => M G j j ^ 2) μ := hy2
  have h1 : Integrable (fun G => M G i i ^ 2 + M G j j ^ 2) μ := hx2'.add hy2'
  have h2 : Integrable (fun G => M G i i ^ 2 + M G j j ^ 2 + 4 * M G i j ^ 2) μ :=
    h1.add (hz2.const_mul 4)
  have h3 : Integrable (fun G => M G i i ^ 2 + M G j j ^ 2 + 4 * M G i j ^ 2
      + 2 * (M G i i * M G j j)) μ := h2.add (hxy.const_mul 2)
  have h4 : Integrable (fun G => M G i i ^ 2 + M G j j ^ 2 + 4 * M G i j ^ 2
      + 2 * (M G i i * M G j j) + 4 * (M G i i * M G i j)) μ := h3.add (hxz.const_mul 4)
  rw [hexp, integral_const_mul, integral_add h4 (hyz.const_mul 4),
    integral_add h3 (hxz.const_mul 4), integral_add h2 (hxy.const_mul 2),
    integral_add h1 (hz2.const_mul 4), integral_add hx2' hy2',
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    hxz0, hflip'] at hrot
  have hxy' : ∫ G, M G i i ^ 2 ∂μ = ∫ G, M G j j ^ 2 ∂μ := by
    change ∫ G, (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i i ^ 2 ∂μ
      = ∫ G, (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ j j ^ 2 ∂μ
    rw [hxval, hyval]
  change ∫ G, M G i i ^ 2 ∂μ = ∫ G, M G i i * M G j j ∂μ + 2 * ∫ G, M G i j ^ 2 ∂μ
  linarith
