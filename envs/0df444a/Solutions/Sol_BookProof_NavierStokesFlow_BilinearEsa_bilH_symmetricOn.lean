-- Prove2me | solution 1 for BookProof.NavierStokesFlow.BilinearEsa.bilH_symmetricOn
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T04:36:57.700286+00:00
-- url     : https://prove2.me/submissions/c2b16e51-3716-43f8-b8b4-e42526e64dec

import Mathlib
import Definitions.Def_ChapterNavierStokesBilinearEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Theorems.Thm_BookProof_NavierStokesFlow_BilinearEsa_blockVec_mem_maxDom
import Theorems.Thm_BookProof_NavierStokesFlow_BilinearEsa_hasSum_inner_blocks
import Theorems.Thm_BookProof_NavierStokesFlow_HermiteFarisLavine_nsH_symmetricOn
import Theorems.Thm_BookProof_NavierStokesFlow_HermiteFarisLavine_nsH_coe
import Theorems.Thm_BookProof_NavierStokesFlow_BilinearEsa_blockVec_bilH_apply
-- Generated from ChapterNavierStokesBilinearEsa.lean — theorem BookProof.NavierStokesFlow.BilinearEsa.bilH_symmetricOn
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.BilinearEsa


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine

variable {J : Type*}


theorem solution (κ : J → ℝ) (hκ : ∀ j, 0 ≤ κ j) :
    SymmetricOn (lpFiniteModes (ℕ × J)) (bilH κ) := by
  intro x y
  have hx := hasSum_inner_blocks (bilH κ x : L2I (ℕ × J)) (y : L2I (ℕ × J))
  have hy := hasSum_inner_blocks (x : L2I (ℕ × J)) (bilH κ y : L2I (ℕ × J))
  let xj : ∀ j, maxDom (oscSymbol (κ j)) := fun j =>
    ⟨blockVec (x : L2I (ℕ × J)) j, blockVec_mem_maxDom κ x j⟩
  let yj : ∀ j, maxDom (oscSymbol (κ j)) := fun j =>
    ⟨blockVec (y : L2I (ℕ × J)) j, blockVec_mem_maxDom κ y j⟩
  have ex : ∀ j, blockVec (bilH κ x : L2I (ℕ × J)) j = nsH (κ j) (hκ j) (xj j) :=
    fun j => lp.ext (funext fun n => by
      rw [blockVec_coe, blockVec_bilH_apply, nsH_coe]; rfl)
  have ey : ∀ j, blockVec (bilH κ y : L2I (ℕ × J)) j = nsH (κ j) (hκ j) (yj j) :=
    fun j => lp.ext (funext fun n => by
      rw [blockVec_coe, blockVec_bilH_apply, nsH_coe]; rfl)
  have heq : (fun j => (inner ℂ (blockVec (bilH κ x : L2I (ℕ × J)) j)
      (blockVec (y : L2I (ℕ × J)) j) : ℂ))
      = (fun j => (inner ℂ (blockVec (x : L2I (ℕ × J)) j)
      (blockVec (bilH κ y : L2I (ℕ × J)) j) : ℂ)) := by
    funext j
    rw [ex, ey]
    exact nsH_symmetricOn (hκ j) (xj j) (yj j)
  rw [heq] at hx
  exact hx.unique hy

