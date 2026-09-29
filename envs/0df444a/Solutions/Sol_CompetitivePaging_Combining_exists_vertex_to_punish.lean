-- Prove2me | solution 1 for CompetitivePaging.Combining.exists_vertex_to_punish
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-27T21:52:50.250987+00:00
-- url     : https://prove2.me/submissions/3c132ea1-3852-418d-812c-c71eaae66e5f

import Mathlib

theorem solution {M : Type} [DecidableEq M] (k : ℕ) (SA SB : Finset M) (x : M)
    (hSA : SA.card = k) (hSB : SB.card ≤ k) (hxB : x ∈ SB) (hxA : x ∉ SA) :
    ∃ u ∈ SA, u ∉ SB := by
  by_contra h
  push_neg at h
  have hsub : SA ⊆ SB := fun u hu => h u hu
  have hss : SA ⊂ SB := ⟨hsub, fun hc => hxA (hc hxB)⟩
  have hlt := Finset.card_lt_card hss
  omega
