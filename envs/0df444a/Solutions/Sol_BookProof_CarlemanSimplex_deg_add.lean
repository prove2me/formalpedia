-- Prove2me | solution 1 for BookProof.CarlemanSimplex.deg_add
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-07T23:03:13.77452+00:00
-- url     : https://prove2.me/submissions/d5a88f71-ec1c-4487-8539-445fed377bc7

-- Generated from ChapterCarlemanSimplex.lean — solution of BookProof.CarlemanSimplex.deg_add
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


theorem solution (a b : Fin d →₀ ℕ) : deg (a + b) = deg a + deg b := by
  simp [deg, Finsupp.add_apply, Finset.sum_add_distrib]
