-- Prove2me | solution 1 for BookProof.FockQuadratic.freeOp_symmetricOn
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-06T00:46:48.044746+00:00
-- url     : https://prove2.me/submissions/f4baa28c-b6b6-4f8c-8bb3-1965e87f2278

-- Generated from ChapterFockQuadraticEsa.lean — solution of BookProof.FockQuadratic.freeOp_symmetricOn
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

set_option maxHeartbeats 1000000 in
theorem solution (hω : ∀ i, 0 ≤ ω i) :
    SymmetricOn (maxDom (sig ω)) (freeOp hω) := by

  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun b => ?_
  simp only [RCLike.inner_apply, freeOp_coe, map_mul, Complex.conj_ofReal]
  ring
