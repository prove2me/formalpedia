-- Prove2me | solution 1 for BookProof.SymmetryEntropy.entropy_pointMass
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:10:35.070074+00:00
-- url     : https://prove2.me/submissions/8920ab96-5085-4913-88b3-9d7dacab5a55

-- Generated from ChapterSymmetryEntropy.lean — solution of BookProof.SymmetryEntropy.entropy_pointMass
import Mathlib
import Definitions.Def_ChapterSymmetryEntropy
import Definitions.Def_ChapterMarkovEntropy
import Definitions.Def_ChapterReconstruct
import Definitions.Def_ChapterIrreversible
open BookProof.SymmetryEntropy




open Finset
open BookProof.ChapterMarkovEntropy (entropy)
open BookProof.ChapterReconstruct (IsDeterministicCol)

variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (a : Fin n) :
    entropy (fun k => if k = a then (1 : ℝ) else 0) = 0 := by

  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : k = a <;> simp [hk, Real.negMulLog]
