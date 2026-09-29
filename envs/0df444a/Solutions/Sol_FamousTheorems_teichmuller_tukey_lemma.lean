-- Prove2me | solution 1 for FamousTheorems.teichmuller_tukey_lemma
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T01:56:24.045889+00:00
-- url     : https://prove2.me/submissions/03e66ad8-b7f6-42c9-8e21-60e0631c1133

import Mathlib

theorem solution {α : Type*} {F : Set (Set α)} (hF : Order.IsOfFiniteCharacter F) {x : Set α} (hx : x ∈ F) :
    ∃ m : Set α, x ⊆ m ∧ Maximal (fun y => y ∈ F) m :=
  hF.exists_maximal hx
