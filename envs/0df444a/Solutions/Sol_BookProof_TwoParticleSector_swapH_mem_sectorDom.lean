-- Prove2me | solution 1 for BookProof.TwoParticleSector.swapH_mem_sectorDom
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T08:49:16.447112+00:00
-- url     : https://prove2.me/submissions/f78dfbfa-9370-4892-8512-6ded5fe47bcb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterTwoParticleSectorEsa.lean — solution of BookProof.TwoParticleSector.swapH_mem_sectorDom
import Mathlib
import Definitions.Def_ChapterTwoParticleSectorEsa
import Theorems.Thm_BookProof_TwoParticleSector_inclPow_swapDom
open BookProof.TwoParticleSector




open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore

noncomputable section

variable (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X]
variable {X}
variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier)
variable (A : D₂ →ₗ[ℂ] Hs.carrier)

set_option maxHeartbeats 1000000 in
theorem solution {x : (Hs.pow 2).carrier} (hx : x ∈ sectorDom Hs D₂ 2) :
    swapH Hs x ∈ sectorDom Hs D₂ 2 := by

  obtain ⟨t, rfl⟩ := hx
  exact ⟨swapDom Hs D₂ t, inclPow_swapDom Hs D₂ t⟩
