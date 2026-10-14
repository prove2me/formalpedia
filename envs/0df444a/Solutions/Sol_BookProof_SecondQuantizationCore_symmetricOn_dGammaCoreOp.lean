-- Prove2me | solution 1 for BookProof.SecondQuantizationCore.symmetricOn_dGammaCoreOp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T20:19:17.975069+00:00
-- url     : https://prove2.me/submissions/2a087ef6-7d88-46a5-a4e1-b29f6e68c6a7

-- Generated from ChapterSecondQuantizationCoreEsa.lean — solution of BookProof.SecondQuantizationCore.symmetricOn_dGammaCoreOp
import Mathlib
import Definitions.Def_ChapterSecondQuantizationCoreEsa
import Theorems.Thm_BookProof_SecondQuantizationCore_symmetricOn_fockSectorOp
import Theorems.Thm_BookProof_DirectSumEsa_dsOp_symmetricOn
import Theorems.Thm_BookProof_GraphCore_symmetricOn_restrictOp
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterTensorGraphCore
open BookProof.SecondQuantizationCore




open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.TensorCore BookProof.DirectSumEsa
open BookProof.DirectSumEsa
open BookProof.GraphCore
open BookProof.TensorCore

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (A : D₂ →ₗ[ℂ] Hs.carrier)
  (D : Submodule ℂ Hs.carrier)

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (A : D₂ →ₗ[ℂ] Hs.carrier)
  (D : Submodule ℂ Hs.carrier)

set_option maxHeartbeats 1000000 in
theorem solution (hA : SymmetricOn D₂ A) :
    SymmetricOn (dsCore (fun n : ℕ => fockSectorCore Hs D₂ D n)) (dGammaCoreOp Hs D₂ A D) :=
  dsOp_symmetricOn _
      (fun n => symmetricOn_restrictOp _ _ (symmetricOn_fockSectorOp Hs D₂ A hA n))
