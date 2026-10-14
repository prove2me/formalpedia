-- Prove2me | solution 1 for BookProof.TwoParticleSector.mem_bosonic_iff
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:35:05.727705+00:00
-- url     : https://prove2.me/submissions/6f26441a-7b41-4af9-81ec-7c01ba0e3863

-- Generated from ChapterTwoParticleSectorEsa.lean — solution of BookProof.TwoParticleSector.mem_bosonic_iff
import Mathlib
import Definitions.Def_ChapterTwoParticleSectorEsa
import Theorems.Thm_BookProof_TwoParticleSector_swapH_involutive
import Theorems.Thm_BookProof_ReducedEsa_mem_sector_symProj_iff
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
    x ∈ sector (bosonicProj Hs) ↔ swapH Hs x = x := mem_sector_symProj_iff (swapH_involutive Hs)
