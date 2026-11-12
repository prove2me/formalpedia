-- Prove2me | solution 1 for BookProof.CarlemanTwoStep.mem_faceK
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-11T06:19:36.735198+00:00
-- url     : https://prove2.me/submissions/7fcdf565-57c4-4df4-93bc-d5aa99e63aef

-- Generated from ChapterCarlemanTwoStep.lean — solution of BookProof.CarlemanTwoStep.mem_faceK
import Mathlib
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Theorems.Thm_BookProof_HermiteCarleman_mem_cube_inc
import Definitions.Def_ChapterHermiteCarlemanEsaPromoted
open BookProof.CarlemanTwoStep




open Finset
open BookProof.HermiteCarleman

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {d N : ℕ} {i : Fin d} {k : ℕ} {a : Fin d →₀ ℕ} :
    a ∈ faceK d N i k ↔ (∀ j, a j ≤ N) ∧ N < a i + k := by

  classical
  rw [faceK, Finset.mem_filter, mem_cube_inc]
