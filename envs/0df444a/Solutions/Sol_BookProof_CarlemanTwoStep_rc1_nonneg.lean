-- Prove2me | solution 1 for BookProof.CarlemanTwoStep.rc1_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T06:51:16.221482+00:00
-- url     : https://prove2.me/submissions/3e3cd9bd-a616-455e-a02e-0d32c5fa3517

-- Generated from ChapterCarlemanTwoStep.lean — solution of BookProof.CarlemanTwoStep.rc1_nonneg
import Mathlib
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Definitions.Def_ChapterHermiteCarlemanEsaPromoted
open BookProof.CarlemanTwoStep




open Finset
open BookProof.HermiteCarleman

noncomputable section

variable {d : ℕ}

variable {d : ℕ}
variable {u : (Fin d →₀ ℕ) → ℂ}

set_option maxHeartbeats 1000000 in

theorem solution (a : Fin d →₀ ℕ) (i : Fin d) : 0 ≤ rc1 a i := Real.sqrt_nonneg _
