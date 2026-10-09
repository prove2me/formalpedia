-- Prove2me | solution 1 for BookProof.ChapterEntropy.exists_injective_not_surjective
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:40:20.590889+00:00
-- url     : https://prove2.me/submissions/6999e07b-03c3-495d-a82f-4dc0040be27c

-- Generated from ChapterEntropy.lean — solution of BookProof.ChapterEntropy.exists_injective_not_surjective
import Mathlib
import Definitions.Def_ChapterEntropy
open BookProof.ChapterEntropy




open Filter Asymptotics
open scoped Topology

set_option maxHeartbeats 1000000 in
theorem solution :
    ∃ f : ℕ → ℕ, Function.Injective f ∧ ¬ Function.Surjective f :=
  ⟨Nat.succ, Nat.succ_injective, fun h => by
      obtain ⟨x, hx⟩ := h 0
      exact (Nat.succ_ne_zero x) hx⟩
