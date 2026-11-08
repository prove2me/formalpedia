-- Prove2me | solution 1 for BookProof.CarlemanSimplex.deg_single
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-07T23:03:27.072485+00:00
-- url     : https://prove2.me/submissions/b8286555-a629-496a-aff9-a066a42de752

-- Generated from ChapterCarlemanSimplex.lean — solution of BookProof.CarlemanSimplex.deg_single
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

theorem solution (i : Fin d) (k : ℕ) : deg (Finsupp.single i k) = k := by
  simp [deg]
