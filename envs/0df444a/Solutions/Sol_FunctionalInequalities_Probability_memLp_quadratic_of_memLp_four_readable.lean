-- Prove2me | solution 1 for FunctionalInequalities.Probability.memLp_quadratic_of_memLp_four_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:39:10.070355+00:00
-- url     : https://prove2.me/submissions/a1c7fa92-e2fe-4a49-834c-7dca14019fe1

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Moments

open MeasureTheory
noncomputable section
open scoped RealInnerProductSpace
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
