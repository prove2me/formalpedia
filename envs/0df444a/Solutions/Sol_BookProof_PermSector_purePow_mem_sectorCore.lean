-- Prove2me | solution 1 for BookProof.PermSector.purePow_mem_sectorCore
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T17:17:16.651702+00:00
-- url     : https://prove2.me/submissions/b623039b-9e60-4bb6-9154-7eb5cf4dacfb

-- Generated from ChapterPermutationSectorEsa.lean — solution of BookProof.PermSector.purePow_mem_sectorCore
import Mathlib
import Definitions.Def_ChapterPermutationSectorEsa
import Theorems.Thm_BookProof_PermSector_inclPow_purePow
import Theorems.Thm_BookProof_PermSector_purePow_mem_corePow
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterTensorPermutation
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterTensorGraphCore
open BookProof.PermSector




open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore
open BookProof.GroupAverage BookProof.TensorPerm

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (A : D₂ →ₗ[ℂ] Hs.carrier)
  (D : Submodule ℂ Hs.carrier)

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) (f : Fin n → Hs.carrier) (hD : D ≤ D₂)
    (hf : ∀ i, f i ∈ D) : purePow Hs n f ∈ sectorCore Hs D₂ D n := by

  refine ⟨purePow (domSpace Hs D₂) n (fun i => ⟨f i, hD (hf i)⟩),
    purePow_mem_corePow Hs D₂ D n _ (fun i => hf i), ?_⟩
  simpa using inclPow_purePow Hs D₂ n (fun i => ⟨f i, hD (hf i)⟩)
