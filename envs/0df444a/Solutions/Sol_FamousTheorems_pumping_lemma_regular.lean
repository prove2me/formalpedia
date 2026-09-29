-- Prove2me | solution 1 for FamousTheorems.pumping_lemma_regular
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:16:31.643623+00:00
-- url     : https://prove2.me/submissions/d75ab5e5-fc53-46c0-a1ee-f4cb51472934

import Mathlib

theorem solution {α σ : Type*} (M : DFA α σ) [Fintype σ] {x : List α} (hx : x ∈ M.accepts) (hlen : Fintype.card σ ≤ x.length) :
    ∃ a b c : List α, x = a ++ b ++ c ∧ a.length + b.length ≤ Fintype.card σ ∧ b ≠ [] ∧
      ({a} : Language α) * KStar.kstar ({b} : Language α) * ({c} : Language α) ≤ M.accepts :=
  M.pumping_lemma hx hlen
