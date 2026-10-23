-- Prove2me | solution 1 for DRMeanVar.Reform.thm1_proof_display_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T08:29:03.342001+00:00
-- url     : https://prove2.me/submissions/2781f32f-4cc4-4087-9148-b2f5790f141f

import Mathlib
import Definitions.Def_DRMeanVar_Reform_Setting

open MeasureTheory

namespace DRMeanVar.Reform

theorem empVar_eq_aux {d n : ℕ} [NeZero n] (R : Fin n → (Fin d → ℝ)) (φ : Fin d → ℝ) :
    empVar R φ = empSecond R φ - (empMean R φ) ^ 2 := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  unfold empVar empSecond
  have hm : ∑ i, φ ⬝ᵥ R i = n * empMean R φ := by
    unfold empMean; field_simp
  simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum, hm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

theorem empVar_nonneg_aux {d n : ℕ} (R : Fin n → (Fin d → ℝ)) (φ : Fin d → ℝ) :
    0 ≤ empVar R φ := by
  unfold empVar
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

end DRMeanVar.Reform

open DRMeanVar.Reform in
theorem solution {d n : ℕ} [NeZero n]
    (R : Fin n → (Fin d → ℝ)) (p : ENNReal) (δ α : ℝ) (φ : Fin d → ℝ)
    (hδ : 0 ≤ δ)
    (hfeas : (α - empMean R φ) ^ 2 - δ * ‖WithLp.toLp p φ‖ ^ 2 ≤ 0) :
    hFun p δ R α φ - α ^ 2 =
      (Real.sqrt (empVar R φ) +
        Real.sqrt (δ * ‖WithLp.toLp p φ‖ ^ 2 - (α - empMean R φ) ^ 2)) ^ 2 := by
  have hV := empVar_nonneg_aux R φ
  have hD : 0 ≤ δ * ‖WithLp.toLp p φ‖ ^ 2 - (α - empMean R φ) ^ 2 := by linarith
  have hvar := empVar_eq_aux R φ
  unfold hFun
  rw [add_sq, Real.sq_sqrt hV, Real.sq_sqrt hD]
  rw [hvar]
  ring
