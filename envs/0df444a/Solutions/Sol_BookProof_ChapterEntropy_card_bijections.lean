-- Prove2me | solution 1 for BookProof.ChapterEntropy.card_bijections
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:39:14.136982+00:00
-- url     : https://prove2.me/submissions/e6ffc9cf-a362-4142-aff8-08257ddc6a09

-- Generated from ChapterEntropy.lean — solution of BookProof.ChapterEntropy.card_bijections
import Mathlib
import Definitions.Def_ChapterEntropy
open BookProof.ChapterEntropy




open Filter Asymptotics
open scoped Topology

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) : Fintype.card (Equiv.Perm (Fin n)) = Nat.factorial n := by

  simp [Fintype.card_perm]
