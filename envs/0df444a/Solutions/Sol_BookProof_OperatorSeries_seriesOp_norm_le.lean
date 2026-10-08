-- Prove2me | solution 1 for BookProof.OperatorSeries.seriesOp_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-06T00:58:04.096589+00:00
-- url     : https://prove2.me/submissions/1c603d66-3f27-499e-8c48-91c4b2fc4edb

-- Generated from ChapterOperatorSeriesEsa.lean — solution of BookProof.OperatorSeries.seriesOp_norm_le
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
    ‖(seriesOp T a hnorm ha x : L2I ι)‖ ≤ (∑' k, a k) * ‖(diagMax c x : L2I ι)‖ := by

  have hnormsum : Summable fun k => ‖(T k x : L2I ι)‖ :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => hnorm k x) (ha.mul_right _)
  calc ‖(seriesOp T a hnorm ha x : L2I ι)‖ = ‖∑' k, (T k x : L2I ι)‖ := rfl
    _ ≤ ∑' k, ‖(T k x : L2I ι)‖ := norm_tsum_le_tsum_norm hnormsum
    _ ≤ ∑' k, a k * ‖(diagMax c x : L2I ι)‖ :=
        Summable.tsum_le_tsum (fun k => hnorm k x) hnormsum (ha.mul_right _)
    _ = (∑' k, a k) * ‖(diagMax c x : L2I ι)‖ := by rw [tsum_mul_right]
