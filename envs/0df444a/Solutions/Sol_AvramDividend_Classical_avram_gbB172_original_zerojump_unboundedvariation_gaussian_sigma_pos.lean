-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB172_original_zerojump_unboundedvariation_gaussian_sigma_pos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T17:34:34.813421+00:00
-- url     : https://prove2.me/submissions/29ee27fe-006c-4471-8044-d185fda50e31

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
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0) :
    0 < X.σ := by
  have hne : X.σ ≠ 0 := by
    intro hz
    apply hBV
    exact ⟨hz, by simp [hν]⟩
  exact lt_of_le_of_ne X.σ_nonneg (Ne.symm hne)
