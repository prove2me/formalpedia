-- Prove2me | solution 1 for BookProof.TwoParticleSector.restrictOp_sectorOp_swapH
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-09T22:16:15.669224+00:00
-- url     : https://prove2.me/submissions/dec9ecc3-0c90-43a2-8fff-64beb1b00cf8

-- Generated from ChapterTwoParticleSectorEsa.lean — solution of BookProof.TwoParticleSector.restrictOp_sectorOp_swapH
import Mathlib
import Definitions.Def_ChapterTwoParticleSectorEsa
import Theorems.Thm_BookProof_TwoParticleSector_sectorOp_swapH
import Theorems.Thm_BookProof_TwoParticleSector_swapH_mem_sectorCore
import Theorems.Thm_BookProof_TensorCore_sectorCore_le_sectorDom
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterTensorGraphCore
open BookProof.TwoParticleSector




open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore
open BookProof.DirectSumEsa
open BookProof.GraphCore
open BookProof.TensorCore

noncomputable section

variable (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X]
variable {X}
variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier)
variable (A : D₂ →ₗ[ℂ] Hs.carrier)
variable (D : Submodule ℂ Hs.carrier)

set_option maxHeartbeats 1000000 in
theorem solution (x : sectorCore Hs D₂ D 2) :
    restrictOp (sectorOp Hs D₂ A 2) (sectorCore_le_sectorDom Hs D₂ D 2)
        ⟨swapH Hs (x : (Hs.pow 2).carrier), swapH_mem_sectorCore Hs D₂ D x.2⟩
      = swapH Hs (restrictOp (sectorOp Hs D₂ A 2) (sectorCore_le_sectorDom Hs D₂ D 2) x) := by

  -- `restrictOp_apply` is not in the served bundle (only `restrictOp`, a def
  -- equal to `T ∘ₗ Submodule.inclusion h`, is), so let the elaborator use the
  -- definitional equality instead of a simp lemma.
  exact
    sectorOp_swapH Hs D₂ A ⟨(x : (Hs.pow 2).carrier), sectorCore_le_sectorDom Hs D₂ D 2 x.2⟩
