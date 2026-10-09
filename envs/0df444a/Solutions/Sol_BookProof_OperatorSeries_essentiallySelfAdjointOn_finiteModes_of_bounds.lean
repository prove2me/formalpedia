-- Prove2me | solution 1 for BookProof.OperatorSeries.essentiallySelfAdjointOn_finiteModes_of_bounds
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T22:52:24.006409+00:00
-- url     : https://prove2.me/submissions/9ac326d4-3f09-45d6-9632-83974e0ab7f8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterOperatorSeriesEsa.lean — solution of BookProof.OperatorSeries.essentiallySelfAdjointOn_finiteModes_of_bounds
import Mathlib
import Definitions.Def_ChapterOperatorSeriesEsa
import Theorems.Thm_BookProof_NavierStokesFlow_IkebeKato_essentiallySelfAdjointOn_finiteModes_of_farisLavine_bounds
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
theorem solution (c : ι → ℝ) (hc : ∀ k, 0 ≤ c k)
    (H : maxDom c →ₗ[ℂ] L2I ι) (A B : ℝ) (hB : 0 ≤ B) (hsym : SymmetricOn (maxDom c) H)
    (hA : ∀ x : maxDom c, ‖(H x : L2I ι)‖ ≤ A * ‖(diagMax c x : L2I ι)‖)
    (hcomm : ∀ x : maxDom c, |commForm H (diagMax c) x| ≤ B * quadForm (diagMax c) x) :
    EssentiallySelfAdjointOn (lpFiniteModes ι)
      (H.comp (Submodule.inclusion (finiteModes_le_maxDom c))) := by

  refine essentiallySelfAdjointOn_finiteModes_of_farisLavine_bounds c hc H (A ^ 2) 0 B
    hsym hB ?_ hcomm
  intro x
  have h := hA x
  have h0 : 0 ≤ ‖(H x : L2I ι)‖ := norm_nonneg _
  have hn : 0 ≤ ‖(diagMax c x : L2I ι)‖ := norm_nonneg _
  nlinarith [h, h0, hn, sq_nonneg (A * ‖(diagMax c x : L2I ι)‖)]
