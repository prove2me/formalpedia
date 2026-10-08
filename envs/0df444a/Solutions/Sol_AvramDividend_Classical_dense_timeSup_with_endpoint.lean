-- Prove2me | solution 1 for AvramDividend.Classical.dense_timeSup_with_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T07:24:50.99201+00:00
-- url     : https://prove2.me/submissions/739926f6-0dc3-43fd-974f-8aa21a130abe

import Mathlib

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

theorem solution (f : ℝ≥0 → ℝ)
    (hr : ∀ u, ContinuousWithinAt f (Ici u) u)
    (S : Set ℝ≥0) (hS : Dense S) (h0 : (0 : ℝ≥0) ∈ S)
    (t : ℝ≥0)
    (hb : BddAbove (Set.range
      (fun s : Set.Icc (0 : ℝ≥0) t => f s.1))) :
    (⨆ s : Set.Icc (0 : ℝ≥0) t, f s.1) =
      max (⨆ s : {s : ℝ≥0 // s ∈ S ∧ s ≤ t}, f s.1) (f t) := by
  classical
  letI : Nonempty (Set.Icc (0 : ℝ≥0) t) :=
    ⟨⟨0, ⟨le_rfl, (zero_le : (0 : ℝ≥0) ≤ t)⟩⟩⟩
  letI : Nonempty {s : ℝ≥0 // s ∈ S ∧ s ≤ t} :=
    ⟨⟨0, ⟨h0, (zero_le : (0 : ℝ≥0) ≤ t)⟩⟩⟩
  have hsamp : BddAbove (Set.range
      (fun s : {s : ℝ≥0 // s ∈ S ∧ s ≤ t} => f s.1)) := by
    obtain ⟨M, hM⟩ := hb
    refine ⟨M, ?_⟩
    rintro y ⟨s, rfl⟩
    exact hM ⟨⟨s.1, ⟨(zero_le : (0 : ℝ≥0) ≤ s.1), s.2.2⟩⟩, rfl⟩
  let B : ℝ := ⨆ s : {s : ℝ≥0 // s ∈ S ∧ s ≤ t}, f s.1
  have hall (u : Set.Icc (0 : ℝ≥0) t) : f u.1 ≤ max B (f t) := by
    rcases eq_or_lt_of_le u.2.2 with heq | hlt
    · rw [heq]
      exact le_max_right _ _
    · obtain ⟨v, -, hv, hvlim⟩ :=
        hS.exists_seq_strictAnti_tendsto_of_lt hlt
      have hwithin : Tendsto v atTop (𝓝[Ici u.1] u.1) := by
        apply tendsto_nhdsWithin_iff.mpr
        refine ⟨hvlim, ?_⟩
        exact Filter.Eventually.of_forall
          (fun n => (hv n).1.1.le)
      have hflim : Tendsto (fun n => f (v n)) atTop (𝓝 (f u.1)) :=
        (hr u.1).tendsto.comp hwithin
      have hu_le_B : f u.1 ≤ B := by
        apply isClosed_Iic.mem_of_tendsto hflim
        exact Filter.Eventually.of_forall (fun n => by
          change f (v n) ≤ B
          exact le_ciSup hsamp
            ⟨v n, ⟨(hv n).2, (hv n).1.2.le⟩⟩)
      exact hu_le_B.trans (le_max_left _ _)
  apply le_antisymm
  · exact ciSup_le hall
  · refine max_le ?_ ?_
    · exact ciSup_le (fun s => le_ciSup hb
        ⟨s.1, ⟨(zero_le : (0 : ℝ≥0) ≤ s.1), s.2.2⟩⟩)
    · exact le_ciSup hb
        ⟨t, ⟨(zero_le : (0 : ℝ≥0) ≤ t), le_rfl⟩⟩
