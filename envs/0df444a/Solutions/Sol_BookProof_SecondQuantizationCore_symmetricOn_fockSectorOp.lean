-- Prove2me | solution 1 for BookProof.SecondQuantizationCore.symmetricOn_fockSectorOp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T19:55:12.94902+00:00
-- url     : https://prove2.me/submissions/71e04cd1-6a7a-4448-b420-8e94d7fdf027

-- Generated from ChapterSecondQuantizationCoreEsa.lean — solution of BookProof.SecondQuantizationCore.symmetricOn_fockSectorOp
import Mathlib
import Definitions.Def_ChapterSecondQuantizationCoreEsa
import Theorems.Thm_BookProof_GraphCore_symmetricOn_pushOp
import Theorems.Thm_BookProof_TensorCore_symmetricOn_sectorOp
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterTensorGraphCore
open BookProof.SecondQuantizationCore




open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.TensorCore BookProof.DirectSumEsa
open BookProof.TensorCore

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (A : D₂ →ₗ[ℂ] Hs.carrier)
  (D : Submodule ℂ Hs.carrier)

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (A : D₂ →ₗ[ℂ] Hs.carrier)
  (D : Submodule ℂ Hs.carrier)

set_option maxHeartbeats 1000000 in
theorem solution (hA : SymmetricOn D₂ A) (n : ℕ) :
    SymmetricOn (fockSectorDom Hs D₂ n) (fockSectorOp Hs D₂ A n) := symmetricOn_pushOp _ _ (symmetricOn_sectorOp Hs D₂ A hA n)
