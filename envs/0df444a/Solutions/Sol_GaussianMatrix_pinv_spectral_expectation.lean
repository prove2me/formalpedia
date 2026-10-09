-- Prove2me | solution 1 for GaussianMatrix.pinv_spectral_expectation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T04:03:26.062287+00:00
-- url     : https://prove2.me/submissions/522a4c3f-f347-4061-991e-9812b497a3e7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_GaussianMatrix_basic
import Theorems.Thm_GaussianMatrix_pinv_spectral_tail
import Theorems.Thm_GaussianMatrix_integral_le_of_tail_bound

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

open scoped Matrix.Norms.L2Operator in
/-- Entries of `(G Gᵀ)⁻¹` are measurable functions of `G`. -/
theorem measurable_inv_gram_entry {r k : ℕ} (a b : Fin r) :
    Measurable (fun G : Fin r → Fin k → ℝ => (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ a b) := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  have hc : Continuous (fun G : Fin r → Fin k → ℝ => Matrix.of G * (Matrix.of G)ᵀ) := by
    fun_prop
  refine Measurable.mul ?_ ?_
  · exact (hc.matrix_det.measurable).inv
  · exact ((hc.matrix_adjugate).matrix_elem a b).measurable

open scoped Matrix.Norms.L2Operator in
/-- `G ↦ ‖G†‖` is measurable. -/
theorem measurable_specNorm_pinvR {r k : ℕ} :
    Measurable (fun G : Fin r → Fin k → ℝ => specNorm (pinvR (Matrix.of G))) := by
  have h1 : Measurable (fun G : Fin r → Fin k → ℝ => Matrix.of.symm (pinvR (Matrix.of G))) := by
    refine measurable_pi_lambda _ fun j => measurable_pi_lambda _ fun i => ?_
    simp only [Matrix.of_symm_apply, pinvR, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.of_apply]
    refine Finset.measurable_sum _ fun a _ => ?_
    refine Measurable.mul ?_ (measurable_inv_gram_entry a i)
    exact (measurable_pi_apply a).eval
  have h2 : Continuous (fun M : Fin k → Fin r → ℝ => ‖Matrix.of M‖) :=
    continuous_norm.comp continuous_id
  exact h2.measurable.comp h1

open scoped Matrix.Norms.L2Operator in
theorem specNorm_pinvR_nonneg {r k : ℕ} (G : Matrix (Fin r) (Fin k) ℝ) :
    0 ≤ specNorm (pinvR G) := norm_nonneg _

end GaussianMatrix

open GaussianMatrix

theorem solution {r k : ℕ} (hr : 2 ≤ r) (hrk : r + 1 ≤ k) :
    Integrable (fun G : Fin r → Fin k → ℝ => specNorm (pinvR (Matrix.of G))) (gaussianMatrix r k) ∧
    ∫ G, specNorm (pinvR (Matrix.of G)) ∂(gaussianMatrix r k)
      ≤ Real.exp 1 * Real.sqrt k / ((k : ℝ) - r) := by
  have hrk' : r ≤ k := by omega
  have hkR : (r : ℝ) + 1 ≤ k := by exact_mod_cast hrk
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  set m : ℝ := (k : ℝ) - r + 1 with hm_def
  have hm2 : 2 ≤ m := by rw [hm_def]; linarith
  have hm0 : 0 < m := by linarith
  have hk0 : 0 < Real.sqrt k := Real.sqrt_pos.2 (by linarith)
  set p : ℝ := 1 / Real.sqrt (2 * Real.pi * m) with hp_def
  set q : ℝ := Real.exp 1 * Real.sqrt k / m with hq_def
  have hq0 : 0 < q := div_pos (mul_pos (Real.exp_pos 1) hk0) hm0
  have hsq1 : 1 ≤ Real.sqrt (2 * Real.pi * m) := by
    rw [Real.one_le_sqrt]
    nlinarith [Real.pi_gt_three]
  have hp0 : 0 < p := by rw [hp_def]; exact div_pos one_pos (by linarith)
  have hp1 : p ≤ 1 := by rw [hp_def, div_le_one (by linarith)]; exact hsq1
  set C : ℝ := p * q ^ m with hC_def
  have hC : 0 < C := mul_pos hp0 (Real.rpow_pos_of_pos hq0 _)
  have hmeas := measurable_specNorm_pinvR (r := r) (k := k)
  have hnn : 0 ≤ᵐ[gaussianMatrix r k] fun G : Fin r → Fin k → ℝ => specNorm (pinvR (Matrix.of G)) :=
    Filter.Eventually.of_forall fun G => specNorm_pinvR_nonneg _
  have htail : ∀ t : ℝ, 0 < t → (gaussianMatrix r k) {G | t < specNorm (pinvR (Matrix.of G))}
      ≤ ENNReal.ofReal (C * t ^ (-m)) := fun t ht => pinv_spectral_tail hr hrk' t ht
  obtain ⟨hI, hle⟩ := integral_le_of_tail_bound (gaussianMatrix r k)
    (fun G : Fin r → Fin k → ℝ => specNorm (pinvR (Matrix.of G))) hmeas.aemeasurable hnn
    C m hC (by linarith) htail
  refine ⟨hI, hle.trans ?_⟩
  -- `C^(1/m) * m / (m-1) = p^(1/m) * e √k / (k - r) ≤ e √k / (k - r)`
  have hCm : C ^ (1 / m) = p ^ (1 / m) * q := by
    rw [hC_def, Real.mul_rpow hp0.le (Real.rpow_nonneg hq0.le _), one_div,
      Real.rpow_rpow_inv hq0.le hm0.ne']
  have hpm : p ^ (1 / m) ≤ 1 := Real.rpow_le_one hp0.le hp1 (by positivity)
  have hm1 : m - 1 = (k : ℝ) - r := by rw [hm_def]; ring
  have hkr : 0 < (k : ℝ) - r := by linarith
  rw [hCm, hm1]
  have hE : 0 ≤ Real.exp 1 * Real.sqrt k := (mul_pos (Real.exp_pos 1) hk0).le
  calc p ^ (1 / m) * q * m / ((k : ℝ) - r)
      = p ^ (1 / m) * (Real.exp 1 * Real.sqrt k / ((k : ℝ) - r)) := by
        rw [hq_def]; field_simp
    _ ≤ 1 * (Real.exp 1 * Real.sqrt k / ((k : ℝ) - r)) :=
        mul_le_mul_of_nonneg_right hpm (div_nonneg hE hkr.le)
    _ = Real.exp 1 * Real.sqrt k / ((k : ℝ) - r) := one_mul _
