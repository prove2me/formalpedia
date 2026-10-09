-- Prove2me | solution 1 for BookProof.ChapterEntropy.card_selfMaps
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:39:12.825981+00:00
-- url     : https://prove2.me/submissions/5cd3a6bd-abe9-4fd5-81a9-3b96bd821501

-- Generated from ChapterEntropy.lean — solution of BookProof.ChapterEntropy.card_selfMaps
import Mathlib
import Definitions.Def_ChapterEntropy
open BookProof.ChapterEntropy




open Filter Asymptotics
open scoped Topology

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) : Fintype.card (Fin n → Fin n) = n ^ n := by

  simp
