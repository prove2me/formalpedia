-- Prove2me | solution 1 for FunctionalInequalities.Probability.memLp_quadratic_of_memLp_four_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:37:24.547698+00:00
-- url     : https://prove2.me/submissions/8c3003fa-7796-4957-92fa-0f793d021a53

import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Positivity

open MeasureTheory
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities.Probability in
set_option maxHeartbeats 300000 in
theorem solution {alpha E : Type*} [MeasurableSpace alpha]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {mu : Measure alpha}
    {f : alpha → E} (hf : MemLp f 4 mu) (A : E →L[ℝ] E) :
    MemLp (fun x => ⟪A (f x), f x⟫) 2 mu := by
  have ht : ENNReal.HolderTriple (4 : ENNReal) 4 2 := by
    constructor
    rw [← ENNReal.coe_ofNat 4, ← ENNReal.coe_ofNat 2,
      ← ENNReal.coe_inv (by norm_num : (4 : NNReal) ≠ 0),
      ← ENNReal.coe_inv (by norm_num : (2 : NNReal) ≠ 0),
      ← ENNReal.coe_add]
    norm_num
  have hp := hf.norm.mul hf.norm (hpqr := ht)
  apply hp.of_le_mul (c := ‖A‖)
    ((hf.continuousLinearMap_comp A).aestronglyMeasurable.inner hf.aestronglyMeasurable)
  filter_upwards [] with x
  calc
    ‖⟪A (f x), f x⟫‖ ≤ ‖A (f x)‖ * ‖f x‖ := norm_inner_le_norm _ _
    _ ≤ (‖A‖ * ‖f x‖) * ‖f x‖ :=
      mul_le_mul_of_nonneg_right (A.le_opNorm (f x)) (norm_nonneg _)
    _ = ‖A‖ * ‖‖f x‖ * ‖f x‖‖ := by
      rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
      ring
