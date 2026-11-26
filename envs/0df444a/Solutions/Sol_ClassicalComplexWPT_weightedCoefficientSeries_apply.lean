-- Prove2me | solution 1 for ClassicalComplexWPT.weightedCoefficientSeries_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:06:36.270663+00:00
-- url     : https://prove2.me/submissions/2c2c0fc7-3e6c-4000-9b93-565dc7f66662

import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
import Mathlib.Analysis.Normed.Lp.lpSpace
import Definitions.Def_ClassicalComplexWPT_WeightedCoefficientMap
import Theorems.Thm_ClassicalComplexWPT_summable_weightedCoordinateSeries

set_option autoImplicit true
open scoped NNReal ENNReal Topology
open ClassicalComplexWPT
set_option maxHeartbeats 800000
namespace ClassicalComplexWPT
theorem _root_.solution {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (l : ℕ) (v : Fin l → Base n) (j : ℕ) :
    weightedCoefficientSeries p r l v j =
      (r : ℂ) ^ j * (p.changeOriginSeries j l)
        (fun i ↦ baseInclusion n (v i)) (fun _ ↦ lastDirection n) := by
  let ev : ((Base n)[×l]→L[ℂ] WeightedSeq) →L[ℂ] ℂ :=
    (lp.evalCLM ℂ (fun _ : ℕ ↦ ℂ) 1 j).comp
      (ContinuousMultilinearMap.apply ℂ (fun _ : Fin l ↦ Base n) WeightedSeq v)
  have hsum := (summable_weightedCoordinateSeries p r hr l).hasSum.mapL ev
  change ev (∑' k : ℕ, weightedCoordinateSeries p r k l) = _
  rw [← hsum.tsum_eq]
  change (∑' k : ℕ, (lp.single 1 k ((r : ℂ) ^ k *
    (p.changeOriginSeries k l) (fun i ↦ baseInclusion n (v i))
      (fun _ ↦ lastDirection n)) : WeightedSeq) j) = _
  rw [tsum_eq_single j]
  · exact Pi.single_eq_same _ _
  · intro k hkj
    exact Pi.single_eq_of_ne' hkj _
end ClassicalComplexWPT
