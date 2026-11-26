-- Prove2me | solution 1 for ClassicalComplexWPT.weightedCoefficientSeries_sum_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:07:14.894418+00:00
-- url     : https://prove2.me/submissions/4e88e5fc-cf07-4ec0-8cda-96551a5b1efa

import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
import Mathlib.Analysis.Normed.Lp.lpSpace
import Definitions.Def_ClassicalComplexWPT_WeightedCoefficientMap
import Theorems.Thm_ClassicalComplexWPT_weightedCoefficientSeries_apply
import Theorems.Thm_ClassicalComplexWPT_lastAxis_apply
import Theorems.Thm_ClassicalComplexWPT_lastSlice_zero
attribute [local simp] ClassicalComplexWPT.lastAxis_apply
attribute [local simp] ClassicalComplexWPT.lastSlice_zero



set_option autoImplicit true
open scoped NNReal ENNReal Topology
open ClassicalComplexWPT
set_option maxHeartbeats 800000
namespace ClassicalComplexWPT
theorem _root_.solution {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0) (z : Base n) (j : ℕ)
    (hr : (r : ℝ≥0∞) < p.radius)
    (hzq : z ∈ Metric.eball (0 : Base n) (weightedCoefficientSeries p r).radius)
    (hzp : baseInclusion n z ∈ Metric.eball (0 : Ambient n) p.radius) :
    (weightedCoefficientSeries p r).sum z j =
      (r : ℂ) ^ j *
        p.changeOrigin (baseInclusion n z) j (fun _ ↦ lastDirection n) := by
  let coord : WeightedSeq →L[ℂ] ℂ := lp.evalCLM ℂ (fun _ : ℕ ↦ ℂ) 1 j
  have hqsum := ((weightedCoefficientSeries p r).summable hzq).hasSum.mapL coord
  have hzpj : baseInclusion n z ∈
      Metric.eball (0 : Ambient n) (p.changeOriginSeries j).radius := by
    exact mem_eball_zero_iff.mpr
      ((mem_eball_zero_iff.mp hzp).trans_le (p.le_changeOriginSeries_radius j))
  have hpsum : HasSum
      (fun l : ℕ ↦ (p.changeOriginSeries j l)
        (fun _ ↦ baseInclusion n z) (fun _ ↦ lastDirection n))
      (p.changeOrigin (baseInclusion n z) j (fun _ ↦ lastDirection n)) := by
    simpa [FormalMultilinearSeries.changeOrigin, FormalMultilinearSeries.sum, evalLast] using
      ((p.changeOriginSeries j).summable hzpj).hasSum.mapL (evalLast n j)
  change coord ((weightedCoefficientSeries p r).sum z) = _
  calc
    coord ((weightedCoefficientSeries p r).sum z) =
        ∑' l : ℕ, coord (weightedCoefficientSeries p r l (fun _ ↦ z)) :=
      hqsum.tsum_eq.symm
    _ = ∑' l : ℕ, (r : ℂ) ^ j * (p.changeOriginSeries j l)
        (fun _ ↦ baseInclusion n z) (fun _ ↦ lastDirection n) := by
      congr 1
      funext l
      change weightedCoefficientSeries p r l (fun _ ↦ z) j = _
      exact weightedCoefficientSeries_apply p r hr l (fun _ ↦ z) j
    _ = (r : ℂ) ^ j *
        p.changeOrigin (baseInclusion n z) j (fun _ ↦ lastDirection n) :=
      (hpsum.mul_left ((r : ℂ) ^ j)).tsum_eq
end ClassicalComplexWPT
