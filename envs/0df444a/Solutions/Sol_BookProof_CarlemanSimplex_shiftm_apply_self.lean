-- Prove2me | solution 1 for BookProof.CarlemanSimplex.shiftm_apply_self
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-07T23:08:08.42295+00:00
-- url     : https://prove2.me/submissions/09861734-7673-44f5-90e5-b72e53031682

-- Generated from ChapterCarlemanSimplex.lean — solution of BookProof.CarlemanSimplex.shiftm_apply_self
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

theorem solution {a : Fin d →₀ ℕ} {i j : Fin d} :
    (shiftm a i j) i = (a - Finsupp.single j 1 : Fin d →₀ ℕ) i + 1 := by
  simp [shiftm]
