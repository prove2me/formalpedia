-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_strict_mono_cell_selector
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:57:44.485803+00:00
-- url     : https://prove2.me/submissions/570870c6-e207-49d6-b5a5-172480b4c4cc

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem solution
    (u : ℕ → ℝ≥0) (hu : StrictMono u) (N : ℕ) (t : ℝ≥0)
    (h0 : u 0 < t) (hN : t ≤ u N) :
    ∃ k, k < N ∧ u k < t ∧ t ≤ u (k + 1) ∧
      ∀ j, u j < t → t ≤ u (j + 1) → j = k := by
  classical
  have hex : ∃ j, t ≤ u j := ⟨N, hN⟩
  let m := Nat.find hex
  have hm : t ≤ u m := Nat.find_spec hex
  have hmle : m ≤ N := Nat.find_min' hex hN
  have hmpos : 0 < m := by
    by_contra hh
    have hz : m = 0 := Nat.eq_zero_of_not_pos hh
    have hzero : t ≤ u 0 := by simpa only [hz] using hm
    exact (not_lt_of_ge hzero) h0
  let k := m - 1
  have hk : k + 1 = m := Nat.sub_add_cancel (Nat.succ_le_of_lt hmpos)
  have hkm : k < m := Nat.sub_lt hmpos (by decide)
  have hleft : u k < t := lt_of_not_ge (Nat.find_min hex hkm)
  have hright : t ≤ u (k + 1) := by simpa only [hk] using hm
  refine ⟨k, hkm.trans_le hmle, hleft, hright, ?_⟩
  intro j hj hnext
  apply le_antisymm
  · by_contra hh
    have hkj : k + 1 ≤ j := Nat.succ_le_of_lt (lt_of_not_ge hh)
    exact (not_lt_of_ge (hright.trans (hu.monotone hkj))) hj
  · by_contra hh
    have hjk : j + 1 ≤ k := Nat.succ_le_of_lt (lt_of_not_ge hh)
    exact (not_lt_of_ge (hnext.trans (hu.monotone hjk))) hleft
