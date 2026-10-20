-- Prove2me | solution 1 for BookProof.SecondQuantizationCore.isGraphCore_fockSectorCore
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T19:55:11.778352+00:00
-- url     : https://prove2.me/submissions/41251602-20e3-493b-b3c1-c5f7b890aaf1

-- Generated from ChapterSecondQuantizationCoreEsa.lean — solution of BookProof.SecondQuantizationCore.isGraphCore_fockSectorCore
import Mathlib
import Definitions.Def_ChapterSecondQuantizationCoreEsa
import Theorems.Thm_BookProof_GraphCore_isGraphCore_pushOp
import Theorems.Thm_BookProof_TensorCore_isGraphCore_sectorCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterDirectSumEsa
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
theorem solution (hcore : IsGraphCore D A) (n : ℕ) :
    IsGraphCore (fockSectorCore Hs D₂ D n) (fockSectorOp Hs D₂ A n) := isGraphCore_pushOp _ _ (isGraphCore_sectorCore Hs D₂ A D hcore n)
