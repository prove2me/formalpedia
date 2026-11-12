-- Prove2me | solution 1 for BookProof.CarlemanTwoStep.mem_innK
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-11T06:24:25.828017+00:00
-- url     : https://prove2.me/submissions/1970de1e-6bad-4cd7-ad7b-e138341cd05c

-- Generated from ChapterCarlemanTwoStep.lean — solution of BookProof.CarlemanTwoStep.mem_innK
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
    a ∈ innK d N i k ↔ (∀ j, a j ≤ N) ∧ a i + k ≤ N := by

  classical
  rw [innK, Finset.mem_filter, mem_cube_inc]
