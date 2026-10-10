-- Prove2me | solution 1 for BookProof.PermSector.permRep_mem_sectorDom
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T10:37:17.573215+00:00
-- url     : https://prove2.me/submissions/619282a2-c7de-4a7e-a01c-a9e829e54892

-- Generated from ChapterPermutationSectorEsa.lean — solution of BookProof.PermSector.permRep_mem_sectorDom
import Mathlib
import Definitions.Def_ChapterPermutationSectorEsa
import Theorems.Thm_BookProof_PermSector_permOp_mem_sectorDom
open BookProof.PermSector




open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore
open BookProof.GroupAverage BookProof.TensorPerm

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (A : D₂ →ₗ[ℂ] Hs.carrier)
  (D : Submodule ℂ Hs.carrier)

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) (σ : Equiv.Perm (Fin n)) (x : (Hs.pow n).carrier)
    (hx : x ∈ sectorDom Hs D₂ n) : (permRep Hs n).act σ x ∈ sectorDom Hs D₂ n := permOp_mem_sectorDom Hs D₂ n σ⁻¹ hx
