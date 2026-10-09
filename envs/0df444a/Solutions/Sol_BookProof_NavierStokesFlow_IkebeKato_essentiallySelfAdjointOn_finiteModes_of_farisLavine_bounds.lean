-- Prove2me | solution 1 for BookProof.NavierStokesFlow.IkebeKato.essentiallySelfAdjointOn_finiteModes_of_farisLavine_bounds
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:26:24.574699+00:00
-- url     : https://prove2.me/submissions/4b12e01c-5f75-4a08-b4a5-fb2525418fc3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterNavierStokesIkebeKato.lean — solution of BookProof.NavierStokesFlow.IkebeKato.essentiallySelfAdjointOn_finiteModes_of_farisLavine_bounds
import Mathlib
import Definitions.Def_ChapterNavierStokesIkebeKato
import Theorems.Thm_BookProof_NavierStokesFlow_IkebeKato_diagMax_symmetricOn
import Theorems.Thm_BookProof_NavierStokesFlow_IkebeKato_diagMax_quadForm_nonneg
import Theorems.Thm_BookProof_NavierStokesFlow_IkebeKato_diagMax_add_one_surjective
import Theorems.Thm_BookProof_NavierStokesFlow_IkebeKato_exists_finiteModes_graph_approx
import Theorems.Thm_BookProof_FarisLavine_essentiallySelfAdjointOn_core_of_farisLavine
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.IkebeKato



open scoped ENNReal



open LpNat BookProof.FarisLavine

variable {ι : Type*}

variable {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution
    (c : ι → ℝ) (hc : ∀ k, 0 ≤ c k) (H : maxDom c →ₗ[ℂ] L2I ι) (a b cst : ℝ)
    (hH : SymmetricOn (maxDom c) H) (hcst : 0 ≤ cst)
    (hrel : ∀ x : maxDom c, ‖H x‖ ^ 2 ≤ a * ‖diagMax c x‖ ^ 2 + b * ‖(x : L2I ι)‖ ^ 2)
    (hcomm : ∀ x : maxDom c, |commForm H (diagMax c) x| ≤ cst * quadForm (diagMax c) x) :
    EssentiallySelfAdjointOn (lpFiniteModes ι)
      (H.comp (Submodule.inclusion (finiteModes_le_maxDom c))) := by

  refine essentiallySelfAdjointOn_core_of_farisLavine (finiteModes_le_maxDom c)
    H (diagMax c) a b cst hH (diagMax_symmetricOn c) hcst (diagMax_quadForm_nonneg c hc)
    (diagMax_add_one_surjective c hc) hcomm hrel ?_
  intro x ε hε
  obtain ⟨y, hy1, hy2, hy3⟩ := exists_finiteModes_graph_approx c x ε hε
  exact ⟨y, hy1, hy2, hy3⟩
