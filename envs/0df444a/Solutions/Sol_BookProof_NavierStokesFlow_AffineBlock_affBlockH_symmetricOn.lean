-- Prove2me | solution 1 for BookProof.NavierStokesFlow.AffineBlock.affBlockH_symmetricOn
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T04:36:25.007881+00:00
-- url     : https://prove2.me/submissions/19384451-edbf-4742-96bb-7f12d6f373ca

import Mathlib
import Definitions.Def_ChapterNavierStokesAffineBlockEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesIkebeKato
import Theorems.Thm_BookProof_NavierStokesFlow_AffineBlock_blockVec_mem_maxDom_prime
import Theorems.Thm_BookProof_NavierStokesFlow_BilinearEsa_hasSum_inner_blocks
import Theorems.Thm_BookProof_NavierStokesFlow_AffineFiber_affH_symmetricOn
-- Generated from ChapterNavierStokesAffineBlockEsa.lean — theorem BookProof.NavierStokesFlow.AffineBlock.affBlockH_symmetricOn
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.AffineFiber.PairShift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.AffineBlock


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine ShiftHamiltonian AffineFiber BilinearEsa

variable {J : Type*}


theorem solution (κ c : J → ℝ) (hκ : ∀ j, 0 ≤ κ j) (hc : ∀ j, 0 ≤ c j) :
    SymmetricOn (lpFiniteModes (ℕ × J)) (affBlockH κ c hκ hc) := by
  intro x y
  have hx := hasSum_inner_blocks (affBlockH κ c hκ hc x : L2I (ℕ × J)) (y : L2I (ℕ × J))
  have hy := hasSum_inner_blocks (x : L2I (ℕ × J)) (affBlockH κ c hκ hc y : L2I (ℕ × J))
  let xj : ∀ j, maxDom (oscSymbol (affMu (κ j) (c j))) := fun j =>
    ⟨blockVec (x : L2I (ℕ × J)) j, blockVec_mem_maxDom_prime _ x j⟩
  let yj : ∀ j, maxDom (oscSymbol (affMu (κ j) (c j))) := fun j =>
    ⟨blockVec (y : L2I (ℕ × J)) j, blockVec_mem_maxDom_prime _ y j⟩
  have ex : ∀ j, blockVec (affBlockH κ c hκ hc x : L2I (ℕ × J)) j = affH (hκ j) (hc j) (xj j) :=
    fun j => lp.ext (funext fun n => rfl)
  have ey : ∀ j, blockVec (affBlockH κ c hκ hc y : L2I (ℕ × J)) j = affH (hκ j) (hc j) (yj j) :=
    fun j => lp.ext (funext fun n => rfl)
  have heq : (fun j => (inner ℂ (blockVec (affBlockH κ c hκ hc x : L2I (ℕ × J)) j)
      (blockVec (y : L2I (ℕ × J)) j) : ℂ))
      = (fun j => (inner ℂ (blockVec (x : L2I (ℕ × J)) j)
      (blockVec (affBlockH κ c hκ hc y : L2I (ℕ × J)) j) : ℂ)) := by
    funext j
    rw [ex, ey]
    exact affH_symmetricOn (hκ j) (hc j) (xj j) (yj j)
  rw [heq] at hx
  exact hx.unique hy

