-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a249_Gaussian_HJB_factor_exponential_derivative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:51:23.034418+00:00
-- url     : https://prove2.me/submissions/b3421c5a-ca53-49ec-bbf6-32ab429d253e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section
set_option pp.explicit false
set_option pp.fullNames false
set_option pp.universes false

theorem solution
    (f fp : ℝ → ℝ) (fpp lambdaPlus lambdaMinus y : ℝ)
    (hf : HasDerivAt f (fp y) y)
    (hfp : HasDerivAt fp fpp y) :
    HasDerivAt (fun t => Real.exp (-lambdaMinus*t) *
      (fp t-lambdaPlus*f t))
      (Real.exp (-lambdaMinus*y) *
        (fpp-(lambdaPlus+lambdaMinus)*fp y+
          lambdaPlus*lambdaMinus*f y)) y := by
  have hlin : HasDerivAt (fun t : ℝ => -lambdaMinus*t)
      (-lambdaMinus) y := by
    simpa using (hasDerivAt_id y).const_mul (-lambdaMinus)
  have he := hlin.exp
  have hs := hfp.sub (hf.const_mul lambdaPlus)
  have hmul := he.mul hs
  convert hmul using 1
  all_goals first
    | rfl
    | (simp only [neg_mul, Pi.sub_apply]; ring)
    | (ext t; simp only [neg_mul, Pi.sub_apply]; ring)
