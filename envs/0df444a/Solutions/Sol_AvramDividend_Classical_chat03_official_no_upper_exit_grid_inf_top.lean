-- Prove2me | solution 1 for AvramDividend.Classical.chat03_official_no_upper_exit_grid_inf_top
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T21:29:03.301007+00:00
-- url     : https://prove2.me/submissions/1b526c25-4489-418a-83a2-a41491678f5c

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_extended_infimum_is_top_iff_no_exit
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-!
An infinite official strict upper passage clock forces every uniform
grid's strict upper first-passage infimum to be infinite.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (upper : ℝ) (h : ℝ≥0)
    (hUp : twoSidedExitUpTime X upper ω = ∞) :
    (⨅ k : ℕ,
      if upper < X.X ((k : ℝ≥0) * h) ω then
        (((k : ℝ≥0) * h) : ℝ≥0∞)
      else ∞) = ∞ := by
  have hNone : ¬ ∃ t : ℝ≥0, upper < X.X t ω := by
    apply (chat03_extended_infimum_is_top_iff_no_exit
      (fun t : ℝ≥0 => upper < X.X t ω)).mp
    exact hUp
  have hNo : ∀ t : ℝ≥0, ¬ upper < X.X t ω := by
    intro t ht
    exact hNone ⟨t, ht⟩
  simp [hNo]
