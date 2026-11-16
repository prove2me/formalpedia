-- Prove2me | solution 1 for AvramDividend.Classical.avram_b27_original_intrinsic_mark_map_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T08:36:52.786606+00:00
-- url     : https://prove2.me/submissions/f41ef0bb-6068-4f93-927f-435a17682533

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_all_original_levy_jump_times_countable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) :
    Measurable (fun u : ℝ≥0 =>
      (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) := by
  have hBase :
      Measurable (fun u : ℝ≥0 => (u, (0 : ℝ))) :=
    measurable_id.prodMk measurable_const
  have hJ :=
    avram_wave4_p2_all_original_levy_jump_times_countable X ω
  apply hBase.measurable_of_countable_ne
  have hSingleton : Set.Countable ({0} : Set ℝ≥0) :=
    Set.countable_singleton (0 : ℝ≥0)
  apply (hSingleton.union hJ).mono
  intro u hu
  by_cases h0 : u = 0
  · exact Or.inl (by simp [h0])
  · apply Or.inr
    have hpos : 0 < u := lt_of_le_of_ne (show (0 : ℝ≥0) ≤ u from bot_le) (Ne.symm h0)
    refine ⟨hpos, ?_⟩
    intro heq
    apply hu
    simp [heq]
