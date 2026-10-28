-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_support_dense_timeInf_with_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T00:31:33.584955+00:00
-- url     : https://prove2.me/submissions/a94a3e83-3adc-4a64-be40-830bd5b0d6d8

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

/-- A right-continuous real path attains the same finite-horizon infimum
over a dense time schedule and the terminal endpoint. The explicit
endpoint handles its possible terminal jump. -/
theorem solution (f : ℝ≥0 → ℝ)
    (hr : ∀ u, ContinuousWithinAt f (Ici u) u)
    (S : Set ℝ≥0) (hS : Dense S) (h0 : (0 : ℝ≥0) ∈ S)
    (t : ℝ≥0)
    (hb : BddBelow (Set.range
      (fun s : Set.Icc (0 : ℝ≥0) t => f s.1))) :
    (⨅ s : Set.Icc (0 : ℝ≥0) t, f s.1) =
      min (⨅ s : {s : ℝ≥0 // s ∈ S ∧ s ≤ t}, f s.1) (f t) := by
  classical
  letI : Nonempty (Set.Icc (0 : ℝ≥0) t) :=
    ⟨⟨0, ⟨le_rfl, (zero_le : (0 : ℝ≥0) ≤ t)⟩⟩⟩
  letI : Nonempty {s : ℝ≥0 // s ∈ S ∧ s ≤ t} :=
    ⟨⟨0, ⟨h0, (zero_le : (0 : ℝ≥0) ≤ t)⟩⟩⟩
  have hsamp : BddBelow (Set.range
      (fun s : {s : ℝ≥0 // s ∈ S ∧ s ≤ t} => f s.1)) := by
    obtain ⟨M, hM⟩ := hb
    refine ⟨M, ?_⟩
    rintro y ⟨s, rfl⟩
    exact hM ⟨⟨s.1, ⟨(zero_le : (0 : ℝ≥0) ≤ s.1), s.2.2⟩⟩, rfl⟩
  let B : ℝ := ⨅ s : {s : ℝ≥0 // s ∈ S ∧ s ≤ t}, f s.1
  have hall (u : Set.Icc (0 : ℝ≥0) t) : min B (f t) ≤ f u.1 := by
    rcases eq_or_lt_of_le u.2.2 with heq | hlt
    · rw [heq]
      exact min_le_right _ _
    · obtain ⟨v, -, hv, hvlim⟩ :=
        hS.exists_seq_strictAnti_tendsto_of_lt hlt
      have hwithin : Tendsto v atTop (𝓝[Ici u.1] u.1) := by
        apply tendsto_nhdsWithin_iff.mpr
        refine ⟨hvlim, ?_⟩
        exact Filter.Eventually.of_forall
          (fun n => (hv n).1.1.le)
      have hflim : Tendsto (fun n => f (v n)) atTop (𝓝 (f u.1)) :=
        (hr u.1).tendsto.comp hwithin
      have hB_le_u : B ≤ f u.1 := by
        apply isClosed_Ici.mem_of_tendsto hflim
        exact Filter.Eventually.of_forall (fun n => by
          change B ≤ f (v n)
          exact ciInf_le hsamp
            ⟨v n, ⟨(hv n).2, (hv n).1.2.le⟩⟩)
      exact (min_le_left _ _).trans hB_le_u
  apply le_antisymm
  · refine le_min ?_ ?_
    · exact le_ciInf (fun s => ciInf_le hb
        ⟨s.1, ⟨(zero_le : (0 : ℝ≥0) ≤ s.1), s.2.2⟩⟩)
    · exact ciInf_le hb
        ⟨t, ⟨(zero_le : (0 : ℝ≥0) ≤ t), le_rfl⟩⟩
  · exact le_ciInf hall
