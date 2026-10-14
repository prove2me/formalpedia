-- Prove2me | solution 1 for BookProof.PermSector.permRep_mem_sectorCore
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T17:17:12.453633+00:00
-- url     : https://prove2.me/submissions/a3b9f49d-be3d-4549-9e76-e665a7541ab6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterPermutationSectorEsa.lean — solution of BookProof.PermSector.permRep_mem_sectorCore
import Mathlib
import Definitions.Def_ChapterPermutationSectorEsa
import Theorems.Thm_BookProof_PermSector_permOp_mem_sectorCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterTensorPermutation
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterWignerLittleGroup
open BookProof.PermSector




open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore
open BookProof.GroupAverage BookProof.TensorPerm

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (A : D₂ →ₗ[ℂ] Hs.carrier)
  (D : Submodule ℂ Hs.carrier)

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) (σ : Equiv.Perm (Fin n)) (x : (Hs.pow n).carrier)
    (hx : x ∈ sectorCore Hs D₂ D n) : (permRep Hs n).act σ x ∈ sectorCore Hs D₂ D n := permOp_mem_sectorCore Hs D₂ D n σ⁻¹ hx
