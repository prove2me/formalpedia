-- Prove2me | solution 1 for BookProof.CarlemanSimplex.rcm_of_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-07T23:07:01.922513+00:00
-- url     : https://prove2.me/submissions/682e3f79-7d83-4d1f-b990-4c0a410886c4

-- Generated from ChapterCarlemanSimplex.lean — solution of BookProof.CarlemanSimplex.rcm_of_zero
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

theorem solution {a : Fin d →₀ ℕ} {i j : Fin d} (h : a j = 0) : rcm a i j = 0 := by
  rw [rcm, h]
  simp
