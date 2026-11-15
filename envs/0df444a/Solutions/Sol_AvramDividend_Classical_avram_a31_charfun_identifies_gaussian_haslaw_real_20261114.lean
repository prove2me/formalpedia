-- Prove2me | solution 1 for AvramDividend.Classical.avram_a31_charfun_identifies_gaussian_haslaw_real_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:50:23.602193+00:00
-- url     : https://prove2.me/submissions/adb2c61c-6d6a-4690-9691-53ecbca44f82

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section

/-- Exact characteristic function on the actual source measure identifies its centred Gaussian marginal law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (G : Ω → ℝ) (v : ℝ≥0)
    (hMeas : AEMeasurable G P)
    (hChar : ∀ u : ℝ,
      charFun (P.map G) u = charFun (gaussianReal 0 v) u) :
    HasLaw G (gaussianReal 0 v) P := by
  refine ⟨hMeas, ?_⟩
  apply Measure.ext_of_charFun
  exact funext hChar
