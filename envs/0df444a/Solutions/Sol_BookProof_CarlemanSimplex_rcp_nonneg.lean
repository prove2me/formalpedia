-- Prove2me | solution 1 for BookProof.CarlemanSimplex.rcp_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-07T23:09:32.867773+00:00
-- url     : https://prove2.me/submissions/3f30ddb4-cfc4-4777-9f5d-9e7b8cb77090

-- Generated from ChapterCarlemanSimplex.lean — solution of BookProof.CarlemanSimplex.rcp_nonneg
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
variable {u : (Fin d →₀ ℕ) → ℂ}

set_option maxHeartbeats 1000000 in

theorem solution (a : Fin d →₀ ℕ) (i j : Fin d) : 0 ≤ rcp a i j :=
  mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
