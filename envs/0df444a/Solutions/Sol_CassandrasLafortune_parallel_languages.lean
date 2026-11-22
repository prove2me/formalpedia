-- Prove2me | solution 1 for CassandrasLafortune.parallel_languages
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T19:57:34.759767+00:00
-- url     : https://prove2.me/submissions/a6dd1c55-2f6e-4be0-b91d-f546fa0756eb

import Definitions.Def_CassandrasLafortune_Parallel
import Theorems.Thm_CassandrasLafortune_parallel_run_iff

open CassandrasLafortune RamadgeWonham.Shared

variable {α A B C : Type}

theorem solution (G : Generator (A ⊕ C)) (H : Generator (B ⊕ C))
    (w : List (Event A B C)) :
    (w ∈ (parallel G H).L ↔ w.filterMap Event.left ∈ G.L ∧ w.filterMap Event.right ∈ H.L) ∧
    (w ∈ (parallel G H).Lm ↔ w.filterMap Event.left ∈ G.Lm ∧ w.filterMap Event.right ∈ H.Lm) := by
  constructor
  · simp only [Generator.L, Set.mem_ofPred_eq, Option.isSome_iff_exists]
    constructor
    · rintro ⟨⟨q, r⟩, h⟩
      obtain ⟨hq, hr⟩ := (parallel_run_iff G H w q r).mp h
      exact ⟨⟨q, hq⟩, ⟨r, hr⟩⟩
    · rintro ⟨⟨q, hq⟩, ⟨r, hr⟩⟩
      exact ⟨(q, r), (parallel_run_iff G H w q r).mpr ⟨hq, hr⟩⟩
  · constructor
    · rintro ⟨⟨q, r⟩, h, hq, hr⟩
      obtain ⟨l, k⟩ := (parallel_run_iff G H w q r).mp h
      exact ⟨⟨q, l, hq⟩, ⟨r, k, hr⟩⟩
    · rintro ⟨⟨q, hq, mq⟩, ⟨r, hr, mr⟩⟩
      exact ⟨(q, r), (parallel_run_iff G H w q r).mpr ⟨hq, hr⟩, mq, mr⟩
