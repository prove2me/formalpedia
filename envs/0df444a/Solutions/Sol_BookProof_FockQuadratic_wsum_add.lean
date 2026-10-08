-- Prove2me | solution 1 for BookProof.FockQuadratic.wsum_add
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-06T00:31:31.321851+00:00
-- url     : https://prove2.me/submissions/19a693c5-e920-4d6b-aa4a-66a9a3beae16

-- Generated from ChapterFockQuadraticEsa.lean — solution of BookProof.FockQuadratic.wsum_add
import Mathlib
import Definitions.Def_ChapterFockQuadraticEsa
open BookProof.FockQuadratic



open scoped ENNReal


open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.LpNat BookProof.OperatorSeries

noncomputable section

variable {ι : Type*}

variable {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (ω : ι → ℝ) (a b : Idx ι) : wsum ω (a + b) = wsum ω a + wsum ω b := by

  simp only [wsum]
  rw [Finsupp.sum_add_index' (by intro i; simp) (by intro i m n; push_cast; ring)]
