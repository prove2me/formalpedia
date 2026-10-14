-- Prove2me | solution 1 for BookProof.PermSector.permRep_commutes_sectorDom
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T20:19:10.062023+00:00
-- url     : https://prove2.me/submissions/c1180a5e-6951-4bb5-a57f-ac2dbf45f698
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterPermutationSectorEsa.lean — solution of BookProof.PermSector.permRep_commutes_sectorDom
import Mathlib
import Definitions.Def_ChapterPermutationSectorEsa
import Theorems.Thm_BookProof_PermSector_sectorOp_permOp
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterTensorPermutation
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterWignerLittleGroup
import Theorems.Thm_BookProof_PermSector_permRep_mem_sectorDom
open BookProof.PermSector




open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore
open BookProof.GroupAverage BookProof.TensorPerm
open BookProof.TensorCore
open BookProof.ChapterWignerLittleGroup

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (A : D₂ →ₗ[ℂ] Hs.carrier)
  (D : Submodule ℂ Hs.carrier)

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) (σ : Equiv.Perm (Fin n))
    (x : sectorDom Hs D₂ n) :
    sectorOp Hs D₂ A n ⟨(permRep Hs n).act σ (x : (Hs.pow n).carrier),
        permRep_mem_sectorDom Hs D₂ n σ _ x.2⟩
      = (permRep Hs n).act σ (sectorOp Hs D₂ A n x) := sectorOp_permOp Hs D₂ A n σ⁻¹ x
