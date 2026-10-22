-- Prove2me | solution 1 for AvramDividend.Classical.chat03_hittingBtwn_eq_terminal_of_no_observed_crossing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T14:52:39.067982+00:00
-- url     : https://prove2.me/submissions/4256cc9f-8094-4a4f-b081-b15ca1075365

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Probability.Process.HittingTime

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open AvramDividend.Classical

/-!
A bounded Mathlib hitting clock returns its terminal index if no
strict crossing was observed at any earlier sampled index.
-/
theorem solution
    {Ω β : Type*} [MeasurableSpace Ω]
    (u : ℕ → Ω → β) (s : Set β) (ω : Ω)
    (m : ℕ) (hnone : ∀ j : ℕ, j < m → u j ω ∉ s) :
    hittingBtwn u s 0 m ω = m := by
  have hle : hittingBtwn u s 0 m ω ≤ m :=
    hittingBtwn_le (u := u) (s := s) (n := 0) (m := m) ω
  apply le_antisymm hle
  by_contra h
  have hlt : hittingBtwn u s 0 m ω < m := Nat.lt_of_not_ge h
  obtain ⟨j, hj, hjhit⟩ :=
    (hittingBtwn_lt_iff (u := u) (s := s) (n := 0)
      (ω := ω) m (le_refl m)).mp hlt
  exact hnone j hj.2 hjhit
