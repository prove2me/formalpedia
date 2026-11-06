-- Prove2me | solution 1 for BookProof.PermSector.signRep_commutes_sectorCore
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:18:05.89864+00:00
-- url     : https://prove2.me/submissions/eca84d28-9fc5-4116-8748-ee0b2acd973c

import Definitions.Def_ChapterPermutationSectorEsa
import Theorems.Thm_BookProof_PermSector_signRep_mem_sectorCore
import Theorems.Thm_BookProof_TensorCore_sectorCore_le_sectorDom
import Theorems.Thm_BookProof_PermSector_signRep_commutes_sectorDom

open BookProof.GraphCore
open BookProof.TensorCore
open BookProof.PermSector

open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore
open BookProof.TensorPerm

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (A : D₂ →ₗ[ℂ] Hs.carrier)
  (D : Submodule ℂ Hs.carrier)

theorem solution (n : ℕ) (σ : Equiv.Perm (Fin n))
    (x : sectorCore Hs D₂ D n) :
    restrictOp (sectorOp Hs D₂ A n) (sectorCore_le_sectorDom Hs D₂ D n)
        ⟨(signRep Hs n).act σ (x : (Hs.pow n).carrier),
          signRep_mem_sectorCore Hs D₂ D n σ _ x.2⟩
      = (signRep Hs n).act σ
          (restrictOp (sectorOp Hs D₂ A n) (sectorCore_le_sectorDom Hs D₂ D n) x) := by
  exact BookProof.PermSector.signRep_commutes_sectorDom Hs D₂ A n σ
    ⟨x.1, sectorCore_le_sectorDom Hs D₂ D n x.2⟩
