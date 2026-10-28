-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_dense_prefix_toReal_eq_genuine_sup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T17:42:14.288825+00:00
-- url     : https://prove2.me/submissions/db73c96c-f618-4b32-9885-7fa75e3a4381

import Mathlib.Data.ENNReal.Operations
import Mathlib.Topology.Defs.Filter
import Theorems.Thm_AvramDividend_Classical_dense_timeSup_with_endpoint
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal

theorem solution
    (f : ℝ≥0 → ℝ) (hr : ∀ u, ContinuousWithinAt f (Set.Ici u) u)
    (hfzero : f 0 = 0)
    (samples : ℕ → ℝ≥0) (hdense : Dense (Set.range samples))
    (hzero : (0 : ℝ≥0) ∈ Set.range samples)
    (t : ℝ≥0) (ht : t ∈ Set.range samples) (hb : BddAbove
      (Set.range (fun s : Set.Icc (0 : ℝ≥0) t => f s.1))) :
    (⨆ i : ℕ, if samples i ≤ t then
      ENNReal.ofReal (f (samples i)) else 0).toReal =
      ⨆ s : Set.Icc (0 : ℝ≥0) t, f s.1 := by
  classical
  letI : Nonempty (Set.Icc (0 : ℝ≥0) t) := ⟨⟨0, ⟨le_rfl, zero_le⟩⟩⟩
  letI : Nonempty {s : ℝ≥0 // s ∈ Set.range samples ∧ s ≤ t} := ⟨⟨0, ⟨hzero, zero_le⟩⟩⟩
  let g : ℕ → ℝ := fun i => if samples i ≤ t then max (f (samples i)) 0 else 0
  have hbC : BddAbove (Set.range g) := by
    have hb_saved := hb
    obtain ⟨M, hM⟩ := hb_saved
    refine ⟨max M 0, ?_⟩
    rintro y ⟨i, rfl⟩
    change (if samples i ≤ t then max (f (samples i)) 0 else 0) ≤ _
    split_ifs with hi
    · apply max_le
      · apply le_max_of_le_left
        exact hM ⟨⟨samples i, ⟨zero_le, hi⟩⟩, rfl⟩
      · exact le_max_right _ _
    · exact le_max_right _ _
  have hpathzero : (0 : ℝ) ≤ (⨆ s : Set.Icc (0 : ℝ≥0) t, f s.1) := by
    calc
      (0 : ℝ) = f 0 := hfzero.symm
      _ ≤ (⨆ s : Set.Icc (0 : ℝ≥0) t, f s.1) := le_ciSup hb ⟨0, ⟨zero_le, zero_le⟩⟩
  have hsample_le (i : ℕ) (hi : samples i ≤ t) : f (samples i) ≤ (⨆ j, g j) := by
    calc
      f (samples i) ≤ max (f (samples i)) 0 := le_max_left _ _
      _ = g i := by simp [g, hi]
      _ ≤ (⨆ j, g j) := le_ciSup hbC i
  have hC_le : (⨆ i, g i) ≤ (⨆ s : Set.Icc (0 : ℝ≥0) t, f s.1) := by
    apply ciSup_le
    intro i
    change (if samples i ≤ t then max (f (samples i)) 0 else 0) ≤ _
    split_ifs with hi
    · apply max_le
      · exact le_ciSup hb ⟨samples i, ⟨zero_le, hi⟩⟩
      · exact hpathzero
    · exact hpathzero
  have hpath_le : (⨆ s : Set.Icc (0 : ℝ≥0) t, f s.1) ≤ (⨆ i, g i) := by
    rw [dense_timeSup_with_endpoint f hr (Set.range samples) hdense hzero t hb]
    apply max_le
    · apply ciSup_le
      intro s
      obtain ⟨i, hi⟩ := s.2.1
      have hs : samples i ≤ t := hi ▸ s.2.2
      calc
        f s.1 = f (samples i) := congrArg f hi.symm
        _ ≤ (⨆ j, g j) := hsample_le i hs
    · obtain ⟨i, hi⟩ := ht
      have hs : samples i ≤ t := le_of_eq hi
      calc
        f t = f (samples i) := congrArg f hi.symm
        _ ≤ (⨆ j, g j) := hsample_le i hs
  calc
    (⨆ i : ℕ, if samples i ≤ t then
      ENNReal.ofReal (f (samples i)) else 0).toReal =
      (⨆ i : ℕ,
        (if samples i ≤ t then ENNReal.ofReal (f (samples i)) else 0).toReal) := by
        apply ENNReal.toReal_iSup
        intro i
        split_ifs <;> simp
    _ = (⨆ i, g i) := by
      apply iSup_congr
      intro i
      by_cases hi : samples i ≤ t
      · simp [g, hi, ENNReal.toReal_ofReal', max_comm]
      · simp [g, hi]
    _ = (⨆ s : Set.Icc (0 : ℝ≥0) t, f s.1) :=
      le_antisymm hC_le hpath_le
