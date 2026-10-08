-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_after_attained_threshold_shift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T22:12:25.260172+00:00
-- url     : https://prove2.me/submissions/6a62db1c-575f-4f9f-9166-0e2a824fe013

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg
import Theorems.Thm_AvramDividend_Classical_runningSup_excess_after_peak

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hxa : x ≤ a) (u t : ℝ≥0) (ω : Ω)
    (hb : BddAbove ((fun r : ℝ≥0 => X.X r ω) '' Set.Icc 0 (u + t)))
    (hpeak : sSup ((fun r : ℝ≥0 => X.X r ω) '' Set.Icc 0 u) = X.X u ω)
    (hlevel : X.X u ω = a - x) :
    barrierStrategy X x a (u + t) ω =
      max 0
        (sSup ((fun r : ℝ≥0 => X.X (u + r) ω) '' Set.Icc 0 t) -
          X.X u ω) := by
  have hrange :
      Set.range (fun s : Set.Icc (0 : ℝ≥0) (u + t) => X.X s.1 ω) =
        (fun r : ℝ≥0 => X.X r ω) '' Set.Icc 0 (u + t) := by
    ext z
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨s.1, s.2, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨⟨s, hs⟩, rfl⟩
  have hb' : BddAbove
      (Set.range (fun s : Set.Icc (0 : ℝ≥0) (u + t) => X.X s.1 ω)) := by
    rwa [hrange]
  letI : Nonempty (Set.Icc (0 : ℝ≥0) (u + t)) :=
    ⟨⟨0, by simp⟩⟩
  have hne : ((fun r : ℝ≥0 => X.X r ω) '' Set.Icc 0 (u + t)).Nonempty :=
    (Set.nonempty_Icc.mpr (show (0 : ℝ≥0) ≤ u + t by positivity)).image _
  have hraw :
      (⨆ s : Set.Icc (0 : ℝ≥0) (u + t), X.X s.1 ω) =
        sSup ((fun r : ℝ≥0 => X.X r ω) '' Set.Icc 0 (u + t)) := by
    apply le_antisymm
    · apply ciSup_le
      intro s
      exact le_csSup hb ⟨s.1, s.2, rfl⟩
    · apply csSup_le hne
      rintro y ⟨s, hs, rfl⟩
      exact le_ciSup hb' (⟨s, hs⟩ : Set.Icc (0 : ℝ≥0) (u + t))
  by_cases hs : u + t = 0
  · have hu : u = 0 := by
      apply le_antisymm _ (by positivity)
      calc
        u ≤ u + t := le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ t by positivity)
        _ = 0 := hs
    have ht : t = 0 := by
      apply le_antisymm _ (by positivity)
      calc
        t ≤ u + t := by simpa [add_comm] using
          (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ u by positivity) : t ≤ t + u)
        _ = 0 := hs
    subst u
    subst t
    simp [barrierStrategy, X.X_zero]
  · simp only [barrierStrategy, hs, if_false]
    rw [hraw]
    have hdelta : x - a = -X.X u ω := by linarith [hlevel]
    rw [hdelta]
    have heq :=
      AvramDividend.Classical.runningSup_excess_after_peak
        (fun r : ℝ≥0 => X.X r ω) u t hb hpeak
    rw [show -X.X u ω +
        sSup ((fun r : ℝ≥0 => X.X r ω) '' Set.Icc 0 (u + t)) =
        sSup ((fun r : ℝ≥0 => X.X r ω) '' Set.Icc 0 (u + t)) -
          X.X u ω by ring, heq]
    simp [max_assoc]
