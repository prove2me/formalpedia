-- Prove2me | solution 1 for AvramDividend.Classical.rawRunningSup_interval_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T20:52:19.933111+00:00
-- url     : https://prove2.me/submissions/4f90f426-af85-49ea-ac67-6c152f2f77c1

import Mathlib


set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped NNReal

theorem solution
    (f : ℝ≥0 → ℝ) (u t : ℝ≥0)
    (hb : BddAbove
      (Set.range (fun s : Set.Icc (0 : ℝ≥0) (u + t) => f s.1))) :
    (⨆ s : Set.Icc (0 : ℝ≥0) (u + t), f s.1) =
      max (⨆ s : Set.Icc (0 : ℝ≥0) u, f s.1)
          (⨆ s : Set.Icc u (u + t), f s.1) := by
  classical
  have hu : u ≤ u + t := by
    exact le_add_of_nonneg_right (bot_le : (0 : ℝ≥0) ≤ t)
  haveI : Nonempty (Set.Icc (0 : ℝ≥0) (u + t)) :=
    ⟨⟨0, ⟨bot_le, bot_le⟩⟩⟩
  haveI : Nonempty (Set.Icc (0 : ℝ≥0) u) :=
    ⟨⟨0, ⟨bot_le, bot_le⟩⟩⟩
  haveI : Nonempty (Set.Icc u (u + t)) :=
    ⟨⟨u, ⟨le_rfl, hu⟩⟩⟩
  obtain ⟨M, hM⟩ := hb
  have hbL : BddAbove
      (Set.range (fun s : Set.Icc (0 : ℝ≥0) u => f s.1)) := by
    refine ⟨M, ?_⟩
    rintro z ⟨s, rfl⟩
    exact hM ⟨⟨s.1, ⟨s.2.1, s.2.2.trans hu⟩⟩, rfl⟩
  have hbR : BddAbove
      (Set.range (fun s : Set.Icc u (u + t) => f s.1)) := by
    refine ⟨M, ?_⟩
    rintro z ⟨s, rfl⟩
    exact hM ⟨⟨s.1, ⟨bot_le, s.2.2⟩⟩, rfl⟩
  have hleft :
      (⨆ s : Set.Icc (0 : ℝ≥0) u, f s.1) ≤
        (⨆ s : Set.Icc (0 : ℝ≥0) (u + t), f s.1) := by
    refine ciSup_le fun s => ?_
    exact le_ciSup ⟨M, hM⟩
      (⟨s.1, ⟨s.2.1, s.2.2.trans hu⟩⟩ :
        Set.Icc (0 : ℝ≥0) (u + t))
  have hright :
      (⨆ s : Set.Icc u (u + t), f s.1) ≤
        (⨆ s : Set.Icc (0 : ℝ≥0) (u + t), f s.1) := by
    refine ciSup_le fun s => ?_
    exact le_ciSup ⟨M, hM⟩
      (⟨s.1, ⟨bot_le, s.2.2⟩⟩ :
        Set.Icc (0 : ℝ≥0) (u + t))
  have hbig :
      (⨆ s : Set.Icc (0 : ℝ≥0) (u + t), f s.1) ≤
        max (⨆ s : Set.Icc (0 : ℝ≥0) u, f s.1)
            (⨆ s : Set.Icc u (u + t), f s.1) := by
    refine ciSup_le fun s => ?_
    by_cases hs : s.1 ≤ u
    · have hsmall :
          f s.1 ≤ (⨆ v : Set.Icc (0 : ℝ≥0) u, f v.1) :=
        le_ciSup hbL ⟨s.1, ⟨s.2.1, hs⟩⟩
      exact hsmall.trans (le_max_left _ _)
    · have hus : u ≤ s.1 := le_of_not_ge hs
      have hsmall :
          f s.1 ≤ (⨆ v : Set.Icc u (u + t), f v.1) :=
        le_ciSup hbR ⟨s.1, ⟨hus, s.2.2⟩⟩
      exact hsmall.trans (le_max_right _ _)
  exact le_antisymm hbig (max_le hleft hright)
