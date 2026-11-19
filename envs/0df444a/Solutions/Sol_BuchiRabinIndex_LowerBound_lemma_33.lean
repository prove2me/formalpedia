-- Prove2me | solution 1 for BuchiRabinIndex.LowerBound.lemma_33
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T16:31:28.089009+00:00
-- url     : https://prove2.me/submissions/795ae6cd-ce90-46cd-80bd-78cc2bb711f4

import Definitions.Def_BuchiRabinIndex_LowerBound_Rabin

open BuchiRabinIndex.LowerBound in
theorem solution (n : ℕ) (hn : 1 ≤ n)
    (p : RabinPair (Edge (Fin n) (Letter n)))
    (D1 D2 D : Set (Edge (Fin n) (Letter n)))
    (h1 : Cycle (fullBuchi n hn) D1) (h2 : Cycle (fullBuchi n hn) D2)
    (hD : Cycle (fullBuchi n hn) D) (hp1 : PairAccepts p D1) (hp2 : PairAccepts p D2)
    (hsub : D2 ⊆ D) (hsup : D ⊆ D1 ∪ D2) : PairAccepts p D := by
  obtain ⟨⟨e, he2, hep⟩, hE2⟩ := hp2
  refine ⟨⟨e, hsub he2, hep⟩, ?_⟩
  ext x
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro hx hx2
  rcases hsup hx with h | h
  · have : x ∈ D1 ∩ p.2 := ⟨h, hx2⟩
    rw [hp1.2] at this; exact this
  · have : x ∈ D2 ∩ p.2 := ⟨h, hx2⟩
    rw [hE2] at this; exact this
