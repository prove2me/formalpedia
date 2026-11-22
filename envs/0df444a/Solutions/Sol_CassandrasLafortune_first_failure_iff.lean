-- Prove2me | solution 1 for CassandrasLafortune.first_failure_iff
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T19:56:15.231811+00:00
-- url     : https://prove2.me/submissions/5fec358b-f8ad-436e-a7a3-b74d9f313eb7

import Definitions.Def_CassandrasLafortune_Parallel

open CassandrasLafortune RamadgeWonham.Shared

variable {α A B C : Type}

theorem run_append_event (G : Generator α) (w : List α) (a : α) :
    G.run (w ++ [a]) = (G.run w).bind (G.δ a) := by
  simp [Generator.run, Generator.runFrom, List.foldl_append]

theorem solution (G : Generator (A ⊕ C)) (H : Generator (B ⊕ C))
    (pre : List (Event A B C)) (e : Event A B C) (q : G.Q) (r : H.Q)
    (hpre : (parallel G H).run pre = some (q, r)) :
    (parallel G H).run (pre ++ [e]) = none ↔
      (∃ a, e.left = some a ∧ G.δ a q = none) ∨ (∃ b, e.right = some b ∧ H.δ b r = none) := by
  rw [run_append_event, hpre]
  cases e with
  | leftOnly a =>
    cases h : G.δ (.inl a) q <;> simp [parallel, localStep, Event.left, Event.right, h]
  | rightOnly b =>
    cases h : H.δ (.inl b) r <;> simp [parallel, localStep, Event.left, Event.right, h]
  | shared c =>
    cases hg : G.δ (.inr c) q <;> cases hh : H.δ (.inr c) r <;>
      simp [parallel, localStep, Event.left, Event.right, hg, hh]
