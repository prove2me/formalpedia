-- Prove2me | solution 1 for ClassicalComplexWPT.exists_weightedLastCoeffs_on_baseBall
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:07:54.850837+00:00
-- url     : https://prove2.me/submissions/55985791-b9b3-4103-abe9-d536550e6cb1

import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
import Mathlib.Analysis.Normed.Lp.lpSpace
import Definitions.Def_ClassicalComplexWPT_WeightedCoefficientMap
import Theorems.Thm_ClassicalComplexWPT_radius_weightedLastCoeffs
import Theorems.Thm_ClassicalComplexWPT_weightedLastCoeffs_apply
import Theorems.Thm_ClassicalComplexWPT_norm_weightedLastCoeffs_le
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
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (s r : ℝ≥0)
    (hsr : (s + r : ℝ≥0∞) < p.radius) {z : Base n}
    (hz : z ∈ Metric.eball (0 : Base n) s) :
    ∃ c : WeightedSeq,
      (∀ k, c k = (r : ℂ) ^ k * lastTaylorCoefficient p k z) ∧
        ‖c‖ ≤ ∑' k : ℕ, ‖p.changeOrigin (z, 0) k‖ * (r : ℝ) ^ k := by
  have hz' : (‖z‖₊ : ℝ≥0∞) < s := mem_eball_zero_iff.mp hz
  have hx : (‖baseInclusion n z‖₊ + r : ℝ≥0∞) < p.radius := by
    calc
      (‖baseInclusion n z‖₊ + r : ℝ≥0∞) = ‖z‖₊ + r := by simp
      _ < s + r := ENNReal.add_lt_add_right (by simp) hz'
      _ < p.radius := hsr
  let hrx := radius_weightedLastCoeffs p r (baseInclusion n z) hx
  refine ⟨weightedLastCoeffs p r (baseInclusion n z) hrx, ?_, ?_⟩
  · intro k
    simp [lastTaylorCoefficient, weightedLastCoeffs_apply]
  · simpa using norm_weightedLastCoeffs_le p r (baseInclusion n z) hrx
end ClassicalComplexWPT
