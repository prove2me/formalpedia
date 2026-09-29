-- Prove2me | solution 1 for BookProof.NavierStokesFlow.nsWord_length_le_three
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T11:38:06.383982+00:00
-- url     : https://prove2.me/submissions/401aae41-66af-403c-85ad-72d4ec924e18

-- Generated from ChapterNavierStokesFlow.lean — solution of BookProof.NavierStokesFlow.nsWord_length_le_three
import Mathlib
import Definitions.Def_ChapterNavierStokesFlow
open BookProof.NavierStokesFlow



open scoped BigOperators Matrix Kronecker ComplexOrder TensorProduct

set_option maxHeartbeats 1000000 in
theorem solution (a : NSWordIndex) : (nsWord a).length ≤ 3 := by

  rcases a with ⟨i, j, b⟩ | ⟨i, b⟩ <;> cases b <;> simp [nsWord]
