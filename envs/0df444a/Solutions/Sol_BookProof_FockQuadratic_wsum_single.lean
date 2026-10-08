-- Prove2me | solution 1 for BookProof.FockQuadratic.wsum_single
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-06T00:53:55.105393+00:00
-- url     : https://prove2.me/submissions/53160633-9a35-48ab-9014-2879f53004e5

-- Generated from ChapterFockQuadraticEsa.lean — solution of BookProof.FockQuadratic.wsum_single
import Mathlib
import Definitions.Def_ChapterFockQuadraticEsa
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
theorem solution (ω : ι → ℝ) (i : ι) (k : ℕ) : wsum ω (Finsupp.single i k) = ω i * k := by

  simp [wsum, Finsupp.sum_single_index]
