-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_hjb_of_zero_cstar_and_generator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T21:14:33.280119+00:00
-- url     : https://prove2.me/submissions/96bd6aab-fc55-471a-8212-6a6bc4216958

import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_eq_one_above_cstar
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Mathlib.Order.Lattice
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Above a zero optimal barrier, the derivative HJB term is zero,
so a nonpositive generator residual yields the full HJB maximum. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
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
  have hyc : (cstar W).toReal < y := by
    simpa [hc0] using hy
  obtain ⟨hI, hG⟩ := hgen y hyc
  refine ⟨hI, ?_⟩
  have hd : deriv (vcstar W) y = 1 :=
    vcstar_deriv_eq_one_above_cstar W y hyc
  simpa [hd] using (max_eq_right hG)
