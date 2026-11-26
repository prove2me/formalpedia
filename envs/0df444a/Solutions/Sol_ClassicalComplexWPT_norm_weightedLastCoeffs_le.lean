-- Prove2me | solution 1 for ClassicalComplexWPT.norm_weightedLastCoeffs_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:04:13.157808+00:00
-- url     : https://prove2.me/submissions/e8d37bd1-23c0-4c91-ad3e-901f53c35491

import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
import Mathlib.Analysis.Normed.Lp.lpSpace
import Definitions.Def_ClassicalComplexWPT_WeightedCoefficientMap
import Theorems.Thm_ClassicalComplexWPT_weightedLastCoeffs_apply
import Theorems.Thm_ClassicalComplexWPT_lastAxis_apply
import Theorems.Thm_ClassicalComplexWPT_lastSlice_zero
attribute [local simp] ClassicalComplexWPT.lastAxis_apply
attribute [local simp] ClassicalComplexWPT.lastSlice_zero


attribute [local simp] ClassicalComplexWPT.weightedLastCoeffs_apply

set_option autoImplicit true
open scoped NNReal ENNReal Topology
open ClassicalComplexWPT
set_option maxHeartbeats 800000
namespace ClassicalComplexWPT
theorem _root_.solution {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0) (x : Ambient n)
    (hr : (r : ℝ≥0∞) < (p.changeOrigin x).radius) :
    ‖weightedLastCoeffs p r x hr‖ ≤
      ∑' k : ℕ, ‖p.changeOrigin x k‖ * (r : ℝ) ^ k := by
  rw [lp.norm_eq_tsum_rpow (by norm_num)]
  simp only [ENNReal.toReal_one, one_div, inv_one, Real.rpow_one, weightedLastCoeffs_apply]
  apply Summable.tsum_le_tsum
  · intro k
    show ‖(r : ℂ) ^ k * ((p.changeOrigin x) k) (fun _ ↦ lastDirection n)‖ ≤
      ‖(p.changeOrigin x) k‖ * (r : ℝ) ^ k
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg r.coe_nonneg]
    have hv : ‖((p.changeOrigin x) k) (fun _ ↦ lastDirection n)‖ ≤
        ‖(p.changeOrigin x) k‖ := by
      simpa [norm_lastDirection] using
        ((p.changeOrigin x) k).le_opNorm (fun _ ↦ lastDirection n)
    calc
      (r : ℝ) ^ k * ‖((p.changeOrigin x) k) (fun _ ↦ lastDirection n)‖ ≤
          (r : ℝ) ^ k * ‖(p.changeOrigin x) k‖ :=
        mul_le_mul_of_nonneg_left hv (pow_nonneg r.coe_nonneg k)
      _ = ‖(p.changeOrigin x) k‖ * (r : ℝ) ^ k := mul_comm _ _
  · simpa only [ENNReal.toReal_one, Real.rpow_one, weightedLastCoeffs_apply] using
      (weightedLastCoeffs p r x hr).2.summable (by norm_num)
  · exact (p.changeOrigin x).summable_norm_mul_pow hr
end ClassicalComplexWPT
