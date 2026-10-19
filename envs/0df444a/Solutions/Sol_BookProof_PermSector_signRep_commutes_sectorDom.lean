-- Prove2me | solution 1 for BookProof.PermSector.signRep_commutes_sectorDom
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T20:19:11.30205+00:00
-- url     : https://prove2.me/submissions/912885c6-a140-4506-90ec-1feb6f6f2bc9

-- Generated from ChapterPermutationSectorEsa.lean — solution of BookProof.PermSector.signRep_commutes_sectorDom
import Mathlib
import Definitions.Def_ChapterPermutationSectorEsa
import Theorems.Thm_BookProof_PermSector_permOp_mem_sectorDom
import Theorems.Thm_BookProof_PermSector_sectorOp_permOp
import Theorems.Thm_BookProof_PermSector_signRep_mem_sectorDom
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterTensorPermutation
import Definitions.Def_ChapterGaugeUnconstrainedSpectrum
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterWignerLittleGroup
open BookProof.PermSector




open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore
open BookProof.GroupAverage BookProof.TensorPerm
open BookProof.ChapterGaugeUnconstrainedSpectrum
open BookProof.TensorCore
open BookProof.ChapterWignerLittleGroup

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (A : D₂ →ₗ[ℂ] Hs.carrier)
  (D : Submodule ℂ Hs.carrier)

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) (σ : Equiv.Perm (Fin n))
    (x : sectorDom Hs D₂ n) :
    sectorOp Hs D₂ A n ⟨(signRep Hs n).act σ (x : (Hs.pow n).carrier),
        signRep_mem_sectorDom Hs D₂ n σ _ x.2⟩
      = (signRep Hs n).act σ (sectorOp Hs D₂ A n x) := by

  have hsplit : (⟨(signRep Hs n).act σ (x : (Hs.pow n).carrier),
        signRep_mem_sectorDom Hs D₂ n σ _ x.2⟩ : sectorDom Hs D₂ n)
      = ((Equiv.Perm.sign σ : ℤ) : ℂ) •
        (⟨permOp Hs n σ⁻¹ (x : (Hs.pow n).carrier),
          permOp_mem_sectorDom Hs D₂ n σ⁻¹ x.2⟩ : sectorDom Hs D₂ n) := by
    apply Subtype.ext
    rfl
  rw [hsplit, map_smul, sectorOp_permOp Hs D₂ A n σ⁻¹ x]
  rfl
