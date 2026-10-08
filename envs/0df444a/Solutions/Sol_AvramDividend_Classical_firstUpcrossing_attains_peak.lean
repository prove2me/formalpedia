-- Prove2me | solution 1 for AvramDividend.Classical.firstUpcrossing_attains_peak
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T23:02:13.046298+00:00
-- url     : https://prove2.me/submissions/99d398a6-13a4-486f-80b8-2f85351b75d8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_prethreshold_le
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_value_eq_threshold

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (hb : 0 ≤ b) (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (t : ℝ≥0) (_ : b < X.X t ω), (t : ℝ≥0∞))) :
    X.X u ω = b ∧
      sSup ((fun r : ℝ≥0 => X.X r ω) '' Set.Icc 0 u) =
        X.X u ω := by
  have hvalue : X.X u ω = b :=
    AvramDividend.Classical.firstUpcrossing_value_eq_threshold X b hb ω u hu
  have hpre : ∀ t : ℝ≥0, t < u → X.X t ω ≤ b :=
    AvramDividend.Classical.firstUpcrossing_prethreshold_le X b ω u hu
  have hbound : BddAbove
      ((fun r : ℝ≥0 => X.X r ω) '' Set.Icc 0 u) := by
    refine ⟨X.X u ω, ?_⟩
    rintro y ⟨t, ht, rfl⟩
    rcases lt_or_eq_of_le ht.2 with hlt | heq
    · rw [hvalue]
      exact hpre t hlt
    · subst t
      exact le_rfl
  have hne : ((fun r : ℝ≥0 => X.X r ω) '' Set.Icc 0 u).Nonempty :=
    ⟨X.X u ω, u, by simp, rfl⟩
  refine ⟨hvalue, le_antisymm ?_ ?_⟩
  · apply csSup_le hne
    rintro y ⟨t, ht, rfl⟩
    rcases lt_or_eq_of_le ht.2 with hlt | heq
    · rw [hvalue]
      exact hpre t hlt
    · subst t
      exact le_rfl
  · exact le_csSup hbound ⟨u, by simp, rfl⟩
