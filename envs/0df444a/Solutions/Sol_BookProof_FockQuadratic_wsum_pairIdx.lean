-- Prove2me | solution 1 for BookProof.FockQuadratic.wsum_pairIdx
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-06T00:55:15.427142+00:00
-- url     : https://prove2.me/submissions/34131973-d593-4350-b814-f9e0969343f6

-- Generated from ChapterFockQuadraticEsa.lean — solution of BookProof.FockQuadratic.wsum_pairIdx
import Mathlib
import Definitions.Def_ChapterFockQuadraticEsa
import Theorems.Thm_BookProof_FockQuadratic_wsum_add
import Theorems.Thm_BookProof_FockQuadratic_wsum_single
open BookProof.FockQuadratic



open scoped ENNReal


open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.LpNat BookProof.OperatorSeries

noncomputable section

variable {ι : Type*}

variable {ι : Type*}
variable {ω : ι → ℝ}
variable {κ : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (ω : ι → ℝ) (m n : ι) : wsum ω (pairIdx m n) = ω m + ω n := by

  rw [pairIdx, wsum_add, wsum_single, wsum_single]
  push_cast
  ring
