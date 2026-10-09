-- Prove2me | solution 1 for BookProof.ComputableScarcity.exists_infinitely_often_ne
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:41:11.602974+00:00
-- url     : https://prove2.me/submissions/a2a8cf1b-cac8-4519-ae15-962491ebb345

-- Generated from ChapterComputableScarcity.lean — solution of BookProof.ComputableScarcity.exists_infinitely_often_ne
import Mathlib
import Definitions.Def_ChapterComputableScarcity
open BookProof.ComputableScarcity




open Nat.Partrec

open Classical

set_option maxHeartbeats 1000000 in
theorem solution (e : ℕ → (ℕ → ℕ)) :
    ∃ f : ℕ → ℕ, ∀ k, {n | f n ≠ e k n}.Infinite := by

  refine ⟨fun n => e n.unpair.1 n + 1, fun k => ?_⟩
  apply Set.Infinite.mono (s := Set.range (fun m => Nat.pair k m))
  · rintro n ⟨m, rfl⟩
    simp [Set.mem_setOf_eq, Nat.unpair_pair]
  · apply Set.infinite_range_of_injective
    intro a b hab
    simpa using hab
