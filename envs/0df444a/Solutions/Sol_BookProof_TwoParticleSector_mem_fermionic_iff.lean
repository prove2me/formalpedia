-- Prove2me | solution 1 for BookProof.TwoParticleSector.mem_fermionic_iff
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:35:07.291931+00:00
-- url     : https://prove2.me/submissions/62836454-14ae-4624-92e2-75fe19bbde59
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterTwoParticleSectorEsa.lean — solution of BookProof.TwoParticleSector.mem_fermionic_iff
import Mathlib
import Definitions.Def_ChapterTwoParticleSectorEsa
import Theorems.Thm_BookProof_TwoParticleSector_swapH_involutive
import Theorems.Thm_BookProof_ReducedEsa_mem_sector_asymProj_iff
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterTensorGraphCore
open BookProof.TwoParticleSector




open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore

noncomputable section

variable (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X]
variable {X}
variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier)
variable (A : D₂ →ₗ[ℂ] Hs.carrier)
variable (D : Submodule ℂ Hs.carrier)

set_option maxHeartbeats 1000000 in
theorem solution {x : (Hs.pow 2).carrier} :
    x ∈ sector (fermionicProj Hs) ↔ swapH Hs x = -x := mem_sector_asymProj_iff (swapH_involutive Hs)
