-- Prove2me | solution 1 for BookProof.TensorCore.sectorCore_le_sectorDom
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T10:38:40.328711+00:00
-- url     : https://prove2.me/submissions/0eff2707-f765-4aa3-9b80-7408660a07c2

-- Generated from ChapterTensorGraphCore.lean — solution of BookProof.TensorCore.sectorCore_le_sectorDom
import Mathlib
import Definitions.Def_ChapterTensorGraphCore
open BookProof.TensorCore




open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier)
variable (A : D₂ →ₗ[ℂ] Hs.carrier)
variable (D : Submodule ℂ Hs.carrier)

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) :
    sectorCore Hs D₂ D n ≤ sectorDom Hs D₂ n := by

  rintro x ⟨y, -, rfl⟩
  exact ⟨y, rfl⟩
