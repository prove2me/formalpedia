-- Prove2me | solution 1 for BookProof.PermSector.permRep_commutes_sectorCore
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:17:34.04622+00:00
-- url     : https://prove2.me/submissions/d080d2a4-f97a-414a-bc89-f767ff63df42

import Definitions.Def_ChapterPermutationSectorEsa
import Theorems.Thm_BookProof_PermSector_permRep_mem_sectorCore
import Theorems.Thm_BookProof_TensorCore_sectorCore_le_sectorDom
import Theorems.Thm_BookProof_PermSector_permRep_commutes_sectorDom

open BookProof.GraphCore BookProof.TensorCore BookProof.PermSector BookProof.TensorPerm

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (A : D₂ →ₗ[ℂ] Hs.carrier)
  (D : Submodule ℂ Hs.carrier)

theorem solution (n : ℕ) (σ : Equiv.Perm (Fin n))
    (x : sectorCore Hs D₂ D n) :
    restrictOp (sectorOp Hs D₂ A n) (sectorCore_le_sectorDom Hs D₂ D n)
        ⟨(permRep Hs n).act σ (x : (Hs.pow n).carrier),
          permRep_mem_sectorCore Hs D₂ D n σ _ x.2⟩
      = (permRep Hs n).act σ
          (restrictOp (sectorOp Hs D₂ A n) (sectorCore_le_sectorDom Hs D₂ D n) x) := by
  exact permRep_commutes_sectorDom Hs D₂ A n σ
    ⟨x, sectorCore_le_sectorDom Hs D₂ D n x.2⟩
