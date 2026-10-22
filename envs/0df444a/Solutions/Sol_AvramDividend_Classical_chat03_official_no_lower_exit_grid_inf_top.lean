-- Prove2me | solution 1 for AvramDividend.Classical.chat03_official_no_lower_exit_grid_inf_top
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T06:45:35.982099+00:00
-- url     : https://prove2.me/submissions/a0d82939-facb-49fc-9294-1be745871974

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_extended_infimum_is_top_iff_no_exit
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-!
An infinite official strict lower passage clock forces every
uniform grid's strict lower first-passage infimum to be infinite.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (lower : ℝ) (h : ℝ≥0)
    (hDown : twoSidedExitDownTime X lower ω = ∞) :
    (⨅ k : ℕ,
      if X.X ((k : ℝ≥0) * h) ω < lower then
        (((k : ℝ≥0) * h) : ℝ≥0∞)
      else ∞) = ∞ := by
  have hNone : ¬ ∃ t : ℝ≥0, X.X t ω < lower := by
    apply (chat03_extended_infimum_is_top_iff_no_exit
      (fun t : ℝ≥0 => X.X t ω < lower)).mp
    exact hDown
  have hNo : ∀ t : ℝ≥0, ¬ X.X t ω < lower := by
    intro t ht
    exact hNone ⟨t, ht⟩
  simp [hNo]
