-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_hjb_above_cstar_of_generator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T22:38:26.228345+00:00
-- url     : https://prove2.me/submissions/8af93d4b-9e00-410f-8514-7890c148b1da

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_eq_one_above_cstar

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (W : ℝ → ℝ)
    (hgen : ∀ y : ℝ, (cstar W).toReal < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        X.generator (vcstar W) y - q * vcstar W y ≤ 0) :
    ∀ y : ℝ, (cstar W).toReal < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        max (X.generator (vcstar W) y - q * vcstar W y)
          (1 - deriv (vcstar W) y) = 0 := by
  intro y hy
  obtain ⟨h_integrable, hresidual⟩ := hgen y hy
  refine ⟨h_integrable, ?_⟩
  have hder : deriv (vcstar W) y = 1 :=
    vcstar_deriv_eq_one_above_cstar W y hy
  simpa [hder] using (max_eq_right hresidual)
