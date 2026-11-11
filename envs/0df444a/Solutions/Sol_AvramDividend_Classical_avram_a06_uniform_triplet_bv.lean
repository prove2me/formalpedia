-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_uniform_triplet_bv
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T17:33:23.261737+00:00
-- url     : https://prove2.me/submissions/9eb41d5d-ede0-422b-b714-d54e0a383139

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a06_uniform_negative_mark_bv_moments
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section

/-- The explicit finite-activity source triplet is of bounded variation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (L : SpectrallyNegativeLevy P 𝓕)
    (hσ : L.σ = 0)
    (hν : L.ν = (volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) :
    L.BoundedVariation := by
  change L.σ = 0 ∧
    (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂L.ν) < ⊤
  exact ⟨hσ, by simpa [hν] using
    AvramDividend.Classical.avram_a06_uniform_negative_mark_bv_moments.2⟩