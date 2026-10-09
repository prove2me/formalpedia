-- Prove2me | solution 1 for GaussianMatrix.inverse_wishart_diag_prod_moment
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T06:19:50.41611+00:00
-- url     : https://prove2.me/submissions/1eb63274-7806-47cf-bbb8-8e489cc7ad9b

import Definitions.Def_GaussianMatrix_basic
import Theorems.Thm_GaussianMatrix_inverse_wishart_diag_sq_moment
import Theorems.Thm_GaussianMatrix_inverse_wishart_offdiag_sq_moment
import Theorems.Thm_GaussianMatrix_inverse_wishart_rotation_relation

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

lemma iwp_measurable_inv_entry {r k : ℕ} (i j : Fin r) :
    Measurable (fun G : Fin r → Fin k → ℝ => (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i j) := by
  have hc : Continuous (fun G : Fin r → Fin k → ℝ => Matrix.of G * (Matrix.of G)ᵀ) :=
    Continuous.matrix_mul continuous_id (Continuous.matrix_transpose continuous_id)
  simp_rw [Matrix.inv_def, Ring.inverse_eq_inv']
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact (hc.matrix_det.measurable.inv).mul (hc.matrix_adjugate.matrix_elem i j).measurable

end GaussianMatrix

open GaussianMatrix

theorem solution {r k : ℕ} (hrk : r + 4 ≤ k) (i j : Fin r) (hij : i ≠ j) :
    Integrable (fun G : Fin r → Fin k → ℝ =>
        (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i i * (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ j j)
      (gaussianMatrix r k) ∧
    ∫ G, (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i i * (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ j j
        ∂(gaussianMatrix r k)
      = ((k : ℝ) - r - 2) / (((k : ℝ) - r) * ((k : ℝ) - r - 1) * ((k : ℝ) - r - 3)) := by
  obtain ⟨hx2, hxval⟩ := inverse_wishart_diag_sq_moment hrk i
  obtain ⟨hy2, -⟩ := inverse_wishart_diag_sq_moment hrk j
  obtain ⟨-, hzval⟩ := inverse_wishart_offdiag_sq_moment hrk i j hij
  have hrel := inverse_wishart_rotation_relation hrk i j hij
  constructor
  · -- `|ab| ≤ a² + b²`
    refine (hx2.add hy2).mono'
      ((iwp_measurable_inv_entry i i).mul (iwp_measurable_inv_entry j j)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun G => ?_)
    rw [Real.norm_eq_abs, abs_le]
    simp only [Pi.add_apply]
    constructor <;>
      nlinarith [sq_nonneg ((Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i i
          + (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ j j),
        sq_nonneg ((Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i i - (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ j j)]
  · rw [hxval, hzval] at hrel
    have hx : (4 : ℝ) ≤ (k : ℝ) - r := by
      have : ((r + 4 : ℕ) : ℝ) ≤ k := by exact_mod_cast hrk
      push_cast at this; linarith
    have h1 : (k : ℝ) - r ≠ 0 := by linarith
    have h2 : (k : ℝ) - r - 1 ≠ 0 := by linarith
    have h3 : (k : ℝ) - r - 3 ≠ 0 := by linarith
    have : ∫ G, (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i i * (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ j j
        ∂(gaussianMatrix r k)
        = 1 / (((k : ℝ) - r - 1) * ((k : ℝ) - r - 3))
          - 2 * (1 / (((k : ℝ) - r) * ((k : ℝ) - r - 1) * ((k : ℝ) - r - 3))) := by linarith
    rw [this]
    field_simp
