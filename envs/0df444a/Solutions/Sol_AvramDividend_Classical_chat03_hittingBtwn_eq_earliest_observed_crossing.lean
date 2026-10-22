-- Prove2me | solution 1 for AvramDividend.Classical.chat03_hittingBtwn_eq_earliest_observed_crossing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T14:17:26.512209+00:00
-- url     : https://prove2.me/submissions/3f4a039d-72dd-472a-859a-e1749ed3c57b

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Probability.Process.HittingTime

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open AvramDividend.Classical

/-!
A bounded sampled hitting clock equals any first witnessed crossing index.
The index may be below the terminal cap and no earlier sample may cross.
This is the clock-identification interface for genuine first-grid Lévy exits.
-/
theorem solution
    {Ω β : Type*} [MeasurableSpace Ω]
    (u : ℕ → Ω → β) (s : Set β) (ω : Ω)
    (m k : ℕ) (hkm : k ≤ m)
    (hk : u k ω ∈ s)
    (hbefore : ∀ j : ℕ, j < k → u j ω ∉ s) :
    hittingBtwn u s 0 m ω = k := by
  have hle : hittingBtwn u s 0 k ω ≤ k :=
    hittingBtwn_le (u := u) (s := s) (n := 0) (m := k) ω
  have hcap : hittingBtwn u s 0 k ω = k := by
    apply le_antisymm hle
    by_contra h
    have hlt : hittingBtwn u s 0 k ω < k := Nat.lt_of_not_ge h
    obtain ⟨j, hj, hjhit⟩ :=
      (hittingBtwn_lt_iff (u := u) (s := s) (n := 0)
        (ω := ω) k (le_refl k)).mp hlt
    exact hbefore j hj.2 hjhit
  have heq :
      hittingBtwn u s 0 k ω = hittingBtwn u s 0 m ω :=
    hittingBtwn_eq_hittingBtwn_of_exists
      (u := u) (s := s) (n := 0) (ω := ω)
      hkm ⟨k, ⟨Nat.zero_le k, le_rfl⟩, hk⟩
  exact heq.symm.trans hcap
