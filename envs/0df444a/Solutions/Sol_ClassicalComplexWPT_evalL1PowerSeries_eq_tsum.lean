-- Prove2me | solution 1 for ClassicalComplexWPT.evalL1PowerSeries_eq_tsum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:00:34.170865+00:00
-- url     : https://prove2.me/submissions/c7dd048f-9967-4c58-a62e-5e6f4f1a0e25

import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Mathlib.Analysis.Analytic.Constructions
import Definitions.Def_ClassicalComplexWPT_L1PowerSeries
import Theorems.Thm_ClassicalComplexWPT_monomial_zero
attribute [local simp] ClassicalComplexWPT.monomial_zero



set_option autoImplicit true
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution (a : L1Sequence) {w : ℂ} (hw : ‖w‖ < 1) :
    evalL1PowerSeries a w = ∑' k : ℕ, a k * w ^ k := by
  have hball : w ∈ Metric.eball (0 : ℂ) l1OperatorSeries.radius := by
    rw [Metric.mem_eball, edist_dist, dist_zero_right]
    exact (show ENNReal.ofReal ‖w‖ < 1 from ENNReal.ofReal_lt_one.mpr hw).trans_le
      one_le_radius_l1OperatorSeries
  let app : (L1Sequence →L[ℂ] ℂ) →L[ℂ] ℂ := ContinuousLinearMap.apply ℂ ℂ a
  have hsum := (l1OperatorSeries.summable hball).hasSum.mapL app
  calc
    evalL1PowerSeries a w = ∑' k : ℕ, l1OperatorSeries k (fun _ ↦ w) a := by
      simpa [evalL1PowerSeries, l1EvalOperator, FormalMultilinearSeries.sum, app] using
        hsum.tsum_eq.symm
    _ = ∑' k : ℕ, a k * w ^ k := by
      congr 1
      funext k
      rw [l1OperatorSeries]
      simp only [ContinuousMultilinearMap.smulRight_apply,
        ContinuousMultilinearMap.mkPiAlgebraFin_apply, List.ofFn_const, List.prod_replicate]
      change w ^ k • coefficientEval k a = a k * w ^ k
      rw [show coefficientEval k a = a k from rfl]
      simp [smul_eq_mul, mul_comm]
end ClassicalComplexWPT
