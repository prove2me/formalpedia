-- Prove2me | solution 1 for BookProof.CarlemanSimplex.mem_sBd
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-07T23:04:05.793464+00:00
-- url     : https://prove2.me/submissions/bc78b3ab-1a5c-464d-8e35-362939995a3c

-- Generated from ChapterCarlemanSimplex.lean — solution of BookProof.CarlemanSimplex.mem_sBd
import Mathlib
import Definitions.Def_ChapterCarlemanSimplexPromoted
import Theorems.Thm_BookProof_CarlemanSimplex_mem_simplexF
import Definitions.Def_ChapterHermiteCarlemanEsaPromoted
import Definitions.Def_ChapterCarlemanTwoStepPromoted
open BookProof.CarlemanSimplex




open Finset
open BookProof.HermiteCarleman BookProof.CarlemanTwoStep

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {d N k : ℕ} {a : Fin d →₀ ℕ} :
    a ∈ sBd d N k ↔ deg a ≤ N ∧ N < deg a + k := by

  classical
  rw [sBd, Finset.mem_filter, mem_simplexF]
