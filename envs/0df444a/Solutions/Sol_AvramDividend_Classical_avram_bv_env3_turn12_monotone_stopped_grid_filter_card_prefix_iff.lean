-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_turn12_monotone_stopped_grid_filter_card_prefix_iff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T06:36:26.348962+00:00
-- url     : https://prove2.me/submissions/076bfa90-bbde-4622-8a8a-3b429325455b

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.SetSemiring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal
noncomputable section

/-- The true selected cells of a monotone physical mesh form a prefix;
counting them recovers the stopping threshold without future look-ahead. -/
theorem solution
    (u : ℕ → ℝ≥0) (hu : Monotone u) (m i : ℕ)
    (t : WithTop ℝ≥0) :
    i < ((Finset.range m).filter
      (fun j => (u j : WithTop ℝ≥0) < t)).card ↔
      i < m ∧ (u i : WithTop ℝ≥0) < t := by
  classical
  let A : Finset ℕ :=
    (Finset.range m).filter (fun j => (u j : WithTop ℝ≥0) < t)
  have hBound : A.card ≤ m := by
    have hs : A ⊆ Finset.range m := Finset.filter_subset _ _
    have h := Finset.card_le_card hs
    simpa [A] using h
  change i < A.card ↔ i < m ∧ (u i : WithTop ℝ≥0) < t
  constructor
  · intro hik
    have hi : i < m := lt_of_lt_of_le hik hBound
    refine ⟨hi, ?_⟩
    by_contra hn
    have hSubset : A ⊆ Finset.range i := by
      intro j hj
      have hlt : (u j : WithTop ℝ≥0) < t := (Finset.mem_filter.mp hj).2
      have hji : j < i := by
        by_contra hji
        have hij : i ≤ j := Nat.le_of_not_gt hji
        exact hn (lt_of_le_of_lt
          (WithTop.coe_le_coe.mpr (hu hij)) hlt)
      exact Finset.mem_range.mpr hji
    have hcard : A.card ≤ i := by
      simpa using (Finset.card_le_card hSubset)
    omega
  · rintro ⟨him, hit⟩
    have hSubset : Finset.range (i + 1) ⊆ A := by
      intro j hj
      have hji : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hjm : j < m := lt_of_le_of_lt hji him
      have hjt : (u j : WithTop ℝ≥0) < t :=
        lt_of_le_of_lt (WithTop.coe_le_coe.mpr (hu hji)) hit
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjm, hjt⟩
    have hcard : i + 1 ≤ A.card := by
      have h := Finset.card_le_card hSubset
      simpa using h
    omega
