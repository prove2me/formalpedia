-- Prove2me | solution 1 for BookProof.TwoParticleSector.swapH_mem_sectorCore
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:35:04.452909+00:00
-- url     : https://prove2.me/submissions/b1f61cad-e9ba-4dfc-b437-64426731ece7

-- Generated from ChapterTwoParticleSectorEsa.lean — solution of BookProof.TwoParticleSector.swapH_mem_sectorCore
import Mathlib
import Definitions.Def_ChapterTwoParticleSectorEsa
import Theorems.Thm_BookProof_TwoParticleSector_inclPow_swapDom
import Theorems.Thm_BookProof_TwoParticleSector_swapDom_mem_corePow
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterDirectSumEsa
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
theorem solution {x : (Hs.pow 2).carrier} (hx : x ∈ sectorCore Hs D₂ D 2) :
    swapH Hs x ∈ sectorCore Hs D₂ D 2 := by

  obtain ⟨t, ht, rfl⟩ := hx
  exact ⟨swapDom Hs D₂ t, swapDom_mem_corePow Hs D₂ D ht, inclPow_swapDom Hs D₂ t⟩
