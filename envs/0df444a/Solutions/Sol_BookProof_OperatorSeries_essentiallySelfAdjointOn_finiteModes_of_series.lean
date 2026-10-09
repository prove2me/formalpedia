-- Prove2me | solution 1 for BookProof.OperatorSeries.essentiallySelfAdjointOn_finiteModes_of_series
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:26:29.286989+00:00
-- url     : https://prove2.me/submissions/b98ea4a4-2b02-4099-9bbd-d1f3997dfd15
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterOperatorSeriesEsa.lean — solution of BookProof.OperatorSeries.essentiallySelfAdjointOn_finiteModes_of_series
import Mathlib
import Definitions.Def_ChapterOperatorSeriesEsa
import Theorems.Thm_BookProof_OperatorSeries_seriesOp_symmetricOn
import Theorems.Thm_BookProof_OperatorSeries_seriesOp_norm_le
import Theorems.Thm_BookProof_OperatorSeries_seriesOp_commForm_le
import Theorems.Thm_BookProof_OperatorSeries_essentiallySelfAdjointOn_finiteModes_of_bounds
import Theorems.Thm_BookProof_NavierStokesFlow_IkebeKato_diagMax_quadForm_nonneg
import Definitions.Def_ChapterNavierStokesIkebeKato
open BookProof.OperatorSeries




open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.LpNat

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable {ι κ : Type*} {c : ι → ℝ}
variable (T : κ → (maxDom c →ₗ[ℂ] L2I ι)) (a : κ → ℝ)
variable {T} {a}
variable {ι : Type*} {c : ι → ℝ}

set_option maxHeartbeats 1000000 in
theorem solution {κ : Type*} (c : ι → ℝ)
    (hc : ∀ k, 0 ≤ c k) (T : κ → (maxDom c →ₗ[ℂ] L2I ι)) (a b : κ → ℝ)
    (hnorm : ∀ (k : κ) (x : maxDom c), ‖(T k x : L2I ι)‖ ≤ a k * ‖(diagMax c x : L2I ι)‖)
    (ha : Summable a) (hb : Summable b) (hb0 : ∀ k, 0 ≤ b k)
    (hsym : ∀ k, SymmetricOn (maxDom c) (T k))
    (hcomm : ∀ (k : κ) (x : maxDom c),
      |commForm (T k) (diagMax c) x| ≤ b k * quadForm (diagMax c) x) :
    EssentiallySelfAdjointOn (lpFiniteModes ι)
      ((seriesOp T a hnorm ha).comp (Submodule.inclusion (finiteModes_le_maxDom c))) := by

  refine essentiallySelfAdjointOn_finiteModes_of_bounds c hc _ (∑' k, a k) (∑' k, b k)
    (tsum_nonneg hb0) (seriesOp_symmetricOn hnorm ha hsym) (seriesOp_norm_le hnorm ha) ?_
  intro x
  exact seriesOp_commForm_le hnorm ha hb hcomm (fun y => diagMax_quadForm_nonneg c hc y) x
