-- Prove2me | solution 1 for BookProof.OperatorSeries.seriesOp_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-06T00:56:14.672499+00:00
-- url     : https://prove2.me/submissions/a0fa95f2-0697-40d6-b03b-6f774904b77e

-- Generated from ChapterOperatorSeriesEsa.lean — solution of BookProof.OperatorSeries.seriesOp_apply
import Mathlib
import Definitions.Def_ChapterOperatorSeriesEsa
open BookProof.OperatorSeries




open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.LpNat

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable {ι κ : Type*} {c : ι → ℝ}
variable (T : κ → (maxDom c →ₗ[ℂ] L2I ι)) (a : κ → ℝ)
variable {T} {a}

set_option maxHeartbeats 1000000 in
theorem solution
    (hnorm : ∀ (k : κ) (x : maxDom c), ‖(T k x : L2I ι)‖ ≤ a k * ‖(diagMax c x : L2I ι)‖)
    (ha : Summable a) (x : maxDom c) :
    (seriesOp T a hnorm ha x : L2I ι) = ∑' k, (T k x : L2I ι) := rfl
