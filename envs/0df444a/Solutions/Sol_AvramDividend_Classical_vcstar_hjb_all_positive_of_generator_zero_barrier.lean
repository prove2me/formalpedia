-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_hjb_all_positive_of_generator_zero_barrier
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T14:53:48.065008+00:00
-- url     : https://prove2.me/submissions/70cbdacc-8507-4779-81d9-23a2b5fea4cc

import Theorems.Thm_AvramDividend_Classical_vcstar_hjb_above_cstar_of_generator
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- For a zero optimal barrier, every positive reserve lies in the affine
dividend region, so the above-barrier HJB lemma applies everywhere. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ)
    (hc0 : cstar W = 0)
    (hgen : ∀ y : ℝ, (cstar W).toReal < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        X.generator (vcstar W) y - q * vcstar W y ≤ 0) :
    ∀ y : ℝ, 0 < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        max (X.generator (vcstar W) y - q * vcstar W y)
          (1 - deriv (vcstar W) y) = 0 := by
  intro y hy
  have hyc : (cstar W).toReal < y := by simpa [hc0] using hy
  exact vcstar_hjb_above_cstar_of_generator X q W hgen y hyc
