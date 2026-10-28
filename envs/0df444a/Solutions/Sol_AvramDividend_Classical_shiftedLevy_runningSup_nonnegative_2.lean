-- Prove2me | solution 2 for AvramDividend.Classical.shiftedLevy_runningSup_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:39:28.901919+00:00
-- url     : https://prove2.me/submissions/e21d6628-f74b-49f8-a8f9-3e621f5cb368

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Theorems.Thm_AvramDividend_Classical_levyPath_bddAbove_Icc
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (u t : ℝ≥0) :
    0 ≤ sSup ((fun v : ℝ≥0 => X.X (u + v) ω - X.X u ω) ''
        Set.Icc 0 t) := by
  classical
  let f : ℝ≥0 → ℝ := fun v => X.X (u + v) ω - X.X u ω
  have hb : BddAbove (f '' Set.Icc 0 t) := by
    rcases levyPath_bddAbove_Icc X ω (u + t) with ⟨K, hK⟩
    refine ⟨K - X.X u ω, ?_⟩
    rintro y ⟨v, hv, rfl⟩
    have hv' : u + v ∈ Set.Icc (0 : ℝ≥0) (u + t) := by
      exact ⟨bot_le, add_le_add_right hv.2 u⟩
    have hbound : X.X (u + v) ω ≤ K :=
      hK (Set.mem_image_of_mem (fun s : ℝ≥0 => X.X s ω) hv')
    exact sub_le_sub_right hbound _
  have hzero : (0 : ℝ) ∈ f '' Set.Icc 0 t := by
    refine ⟨0, ⟨le_rfl, bot_le⟩, ?_⟩
    simp [f]
  exact le_csSup hb hzero
