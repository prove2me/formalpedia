-- Prove2me | solution 1 for AvramDividend.Classical.chat03_hittingBtwn_congr_before_terminal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T05:17:24.032242+00:00
-- url     : https://prove2.me/submissions/3c39b592-5e8c-45ff-9f4e-f0dc7e38bbe5

import Mathlib.Probability.Process.HittingTime

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-!
The first-hit time on the bounded index interval [0,m] depends only
on membership of sampled states at indices strictly before m.
The terminal sample never changes the returned clock, since both
a first hit at m and no hit return the same terminal index m.
-/
theorem solution
    {Ω β : Type*} (u v : ℕ → Ω → β) (s : Set β)
    (ω : Ω) (m : ℕ)
    (hpre : ∀ j : ℕ, j < m → (u j ω ∈ s ↔ v j ω ∈ s)) :
    hittingBtwn u s 0 m ω = hittingBtwn v s 0 m ω := by
  have hu : hittingBtwn u s 0 m ω ≤ m := hittingBtwn_le ω
  have hv : hittingBtwn v s 0 m ω ≤ m := hittingBtwn_le ω
  apply le_antisymm
  · by_contra hle
    have hlt : hittingBtwn v s 0 m ω < hittingBtwn u s 0 m ω :=
      lt_of_not_ge hle
    have hex :
        ∃ j ∈ Set.Ico 0 (hittingBtwn u s 0 m ω), v j ω ∈ s :=
      (hittingBtwn_lt_iff (hittingBtwn u s 0 m ω) hu).mp hlt
    obtain ⟨j, hj, hjv⟩ := hex
    have hju : u j ω ∈ s :=
      (hpre j (lt_of_lt_of_le hj.2 hu)).2 hjv
    have hfalse : hittingBtwn u s 0 m ω < hittingBtwn u s 0 m ω :=
      (hittingBtwn_lt_iff (hittingBtwn u s 0 m ω) hu).mpr
        ⟨j, hj, hju⟩
    exact (lt_irrefl _) hfalse
  · by_contra hle
    have hlt : hittingBtwn u s 0 m ω < hittingBtwn v s 0 m ω :=
      lt_of_not_ge hle
    have hex :
        ∃ j ∈ Set.Ico 0 (hittingBtwn v s 0 m ω), u j ω ∈ s :=
      (hittingBtwn_lt_iff (hittingBtwn v s 0 m ω) hv).mp hlt
    obtain ⟨j, hj, hju⟩ := hex
    have hjv : v j ω ∈ s :=
      (hpre j (lt_of_lt_of_le hj.2 hv)).1 hju
    have hfalse : hittingBtwn v s 0 m ω < hittingBtwn v s 0 m ω :=
      (hittingBtwn_lt_iff (hittingBtwn v s 0 m ω) hv).mpr
        ⟨j, hj, hjv⟩
    exact (lt_irrefl _) hfalse
