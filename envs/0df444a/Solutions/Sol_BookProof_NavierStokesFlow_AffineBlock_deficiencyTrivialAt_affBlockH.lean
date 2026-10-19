-- Prove2me | solution 1 for BookProof.NavierStokesFlow.AffineBlock.deficiencyTrivialAt_affBlockH
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:23:43.458802+00:00
-- url     : https://prove2.me/submissions/8992ca62-2fdd-4da8-a651-349e16ec52c1

-- Generated from ChapterNavierStokesAffineBlockEsa.lean — solution of BookProof.NavierStokesFlow.AffineBlock.deficiencyTrivialAt_affBlockH
import Mathlib
import Definitions.Def_ChapterNavierStokesAffineBlockEsa
import Theorems.Thm_BookProof_NavierStokesFlow_AffineBlock_affFun_embFun
import Theorems.Thm_BookProof_NavierStokesFlow_BilinearEsa_inner_of_block_supported
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesIkebeKato
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.AffineBlock



open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine ShiftHamiltonian AffineFiber BilinearEsa
open BookProof.NavierStokesFlow.AffineFiber.PairShift

variable {J : Type*}

variable {J : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (κ c : J → ℝ) (hκ : ∀ j, 0 ≤ κ j) (hc : ∀ j, 0 ≤ c j)
    (z : ℂ)
    (hblk : ∀ j, DeficiencyTrivialAt (lpFiniteModes ℕ)
      ((affH (hκ j) (hc j)).comp
        (Submodule.inclusion (finiteModes_le_maxDom (oscSymbol (affMu (κ j) (c j)))))) z) :
    DeficiencyTrivialAt (lpFiniteModes (ℕ × J)) (affBlockH κ c hκ hc) z := by

  intro w hw
  have hb : ∀ j, blockVec w j = 0 := by
    intro j
    refine hblk j (blockVec w j) ?_
    intro u
    have hv := hw (blockEmb j u)
    have hHcoe : ∀ p : ℕ × J,
        ((affBlockH κ c hκ hc (blockEmb j u) : L2I (ℕ × J)) : ℕ × J → ℂ) p
          = embFun j (((((affH (hκ j) (hc j))
              (Submodule.inclusion
                (finiteModes_le_maxDom (oscSymbol (affMu (κ j) (c j)))) u) :
                L2I ℕ)) : ℕ → ℂ)) p := by
      intro p
      have hb0 : ((affBlockH κ c hκ hc (blockEmb j u) : L2I (ℕ × J)) : ℕ × J → ℂ)
          = affFun κ c hκ hc (embFun j (((u : L2I ℕ)) : ℕ → ℂ)) := rfl
      rw [hb0, affFun_embFun]
      congr 1
    have h1 := inner_of_block_supported j
      ((affBlockH κ c hκ hc (blockEmb j u) : L2I (ℕ × J)))
      (((affH (hκ j) (hc j))
        (Submodule.inclusion
          (finiteModes_le_maxDom (oscSymbol (affMu (κ j) (c j)))) u) : L2I ℕ)) hHcoe w
    have h2 := inner_of_block_supported j
      (((blockEmb j u : lpFiniteModes (ℕ × J)) : L2I (ℕ × J))) ((u : L2I ℕ))
      (fun _ => rfl) w
    rw [h1, h2] at hv
    exact hv
  refine lp.ext (funext fun p => ?_)
  obtain ⟨n, j⟩ := p
  have hz := congrArg (fun v : L2I ℕ => ((v : ℕ → ℂ)) n) (hb j)
  simpa using hz
