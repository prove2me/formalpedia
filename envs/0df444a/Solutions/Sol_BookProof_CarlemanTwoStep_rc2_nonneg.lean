-- Prove2me | solution 1 for BookProof.CarlemanTwoStep.rc2_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T06:51:20.319015+00:00
-- url     : https://prove2.me/submissions/ccdeafd3-7e6c-481d-bcf8-b5cf3854d182

-- Generated from ChapterCarlemanTwoStep.lean — solution of BookProof.CarlemanTwoStep.rc2_nonneg
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

theorem solution (a : Fin d →₀ ℕ) (i : Fin d) : 0 ≤ rc2 a i := Real.sqrt_nonneg _
