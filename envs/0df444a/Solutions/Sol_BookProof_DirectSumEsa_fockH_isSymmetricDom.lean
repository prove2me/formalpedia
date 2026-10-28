-- Prove2me | solution 1 for BookProof.DirectSumEsa.fockH_isSymmetricDom
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T06:11:58.354453+00:00
-- url     : https://prove2.me/submissions/a23ab735-cf33-4589-a97f-322a2ed60464

-- Generated from ChapterDirectSumEsa.lean — theorem BookProof.DirectSumEsa.fockH_isSymmetricDom
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Theorems.Thm_BookProof_DirectSumEsa_dsOpD_isSymmetricDom
import Theorems.Thm_BookProof_NavierStokesFlow_FockContinuum_multOp_isSymmetricDom
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterLinftyMultiplication
import Definitions.Def_ChapterNavierStokesFockContinuum
import Definitions.Def_ChapterNavierStokesFullEsa
import Theorems.Thm_BookProof_NavierStokesFlow_FullEsa_IsSymmetricDom_sub
import Definitions.Def_ChapterAbelianGelfandModel
import Definitions.Def_ChapterBddBelowFiberSumEsa
open BookProof.ChapterLinftyMultiplication
open BookProof.NavierStokesFlow.FockContinuum
open BookProof.NavierStokesFlow.FullEsa
open BookProof.NavierStokesFlow.FullEsa.NSFullData
open BookProof.DirectSumEsa


open scoped ENNReal


open BookProof.FarisLavine

noncomputable section

variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)]

variable {D : ∀ i, Submodule ℂ (G i)}
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
open BookProof.DirectSumEsa in
theorem solution {w : ℝ → ℝ} (hw : Measurable w) :
    IsSymmetricDom (fockH hw) := by
  exact BookProof.DirectSumEsa.dsOpD_isSymmetricDom _ (fun n => BookProof.NavierStokesFlow.FockContinuum.multOp_isSymmetricDom _ _)
