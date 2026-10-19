-- Prove2me | solution 1 for BookProof.PermSector.sectorOp_permOp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T19:54:54.657043+00:00
-- url     : https://prove2.me/submissions/c9cb61ba-9089-49df-ad5e-e102cf243056

-- Generated from ChapterPermutationSectorEsa.lean — solution of BookProof.PermSector.sectorOp_permOp
import Mathlib
import Definitions.Def_ChapterPermutationSectorEsa
import Theorems.Thm_BookProof_PermSector_inclPow_permOp
import Theorems.Thm_BookProof_PermSector_derPow_permOp
import Theorems.Thm_BookProof_PermSector_permOp_mem_sectorDom
import Theorems.Thm_BookProof_TensorCore_sectorOp_apply
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterTensorPermutation
import Definitions.Def_ChapterGaugeUnconstrainedSpectrum
import Definitions.Def_ChapterTensorGraphCore
open BookProof.PermSector




open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore
open BookProof.GroupAverage BookProof.TensorPerm

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (A : D₂ →ₗ[ℂ] Hs.carrier)
  (D : Submodule ℂ Hs.carrier)

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) (σ : Equiv.Perm (Fin n)) (x : sectorDom Hs D₂ n) :
    sectorOp Hs D₂ A n ⟨permOp Hs n σ (x : (Hs.pow n).carrier),
        permOp_mem_sectorDom Hs D₂ n σ x.2⟩
      = permOp Hs n σ (sectorOp Hs D₂ A n x) := by

  obtain ⟨t, ht⟩ := x.2
  have hx : (x : (Hs.pow n).carrier) = inclPow Hs D₂ n t := ht.symm
  have hsw : permOp Hs n σ (x : (Hs.pow n).carrier)
      = inclPow Hs D₂ n (permOp (domSpace Hs D₂) n σ t) := by
    rw [inclPow_permOp, hx]
  rw [sectorOp_apply Hs D₂ A n _ _ hsw, sectorOp_apply Hs D₂ A n x t hx, derPow_permOp]
