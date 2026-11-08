-- Prove2me | solution 1 for BookProof.CarlemanSimplex.apply_le_deg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-07T23:03:25.947812+00:00
-- url     : https://prove2.me/submissions/9792aa8c-83b2-4a0b-a8bc-c0a2e9539d14

-- Generated from ChapterCarlemanSimplex.lean — solution of BookProof.CarlemanSimplex.apply_le_deg
import Mathlib
import Definitions.Def_ChapterCarlemanSimplexPromoted
import Definitions.Def_ChapterHermiteCarlemanEsaPromoted
import Definitions.Def_ChapterCarlemanTwoStepPromoted
open BookProof.CarlemanSimplex




open Finset
open BookProof.HermiteCarleman BookProof.CarlemanTwoStep

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in

theorem solution (a : Fin d →₀ ℕ) (i : Fin d) : a i ≤ deg a :=
  Finset.single_le_sum (f := fun j => a j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
