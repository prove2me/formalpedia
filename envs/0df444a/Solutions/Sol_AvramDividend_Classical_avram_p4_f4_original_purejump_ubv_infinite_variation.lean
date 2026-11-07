-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f4_original_purejump_ubv_infinite_variation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T06:32:20.426792+00:00
-- url     : https://prove2.me/submissions/a87d2255-a94a-4b70-beb0-b26044aef62e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation)
    (hσ : X.σ = 0) :
    (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂X.ν) = ⊤ := by
  by_contra hfin
  apply hBV
  change X.σ = 0 ∧
    (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂X.ν) < ⊤
  exact ⟨hσ, lt_top_iff_ne_top.mpr hfin⟩
