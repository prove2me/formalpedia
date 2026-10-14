-- Prove2me | solution 1 for BookProof.SecondQuantizationCore.essentiallySelfAdjointOn_fockSectorCore
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T20:19:15.766977+00:00
-- url     : https://prove2.me/submissions/ec6cef6f-4dde-415d-8612-771c860ad1d3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterSecondQuantizationCoreEsa.lean — solution of BookProof.SecondQuantizationCore.essentiallySelfAdjointOn_fockSectorCore
import Mathlib
import Definitions.Def_ChapterSecondQuantizationCoreEsa
import Theorems.Thm_BookProof_SecondQuantizationCore_isGraphCore_fockSectorCore
import Theorems.Thm_BookProof_GraphCore_essentiallySelfAdjointOn_of_graphCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterTensorGraphCore
open BookProof.SecondQuantizationCore




open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.TensorCore BookProof.DirectSumEsa
open BookProof.GraphCore
open BookProof.TensorCore

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (A : D₂ →ₗ[ℂ] Hs.carrier)
  (D : Submodule ℂ Hs.carrier)

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (A : D₂ →ₗ[ℂ] Hs.carrier)
  (D : Submodule ℂ Hs.carrier)

set_option maxHeartbeats 1000000 in
theorem solution (hcore : IsGraphCore D A) (n : ℕ)
    (hesa : EssentiallySelfAdjointOn (fockSectorDom Hs D₂ n) (fockSectorOp Hs D₂ A n)) :
    EssentiallySelfAdjointOn (fockSectorCore Hs D₂ D n)
      (restrictOp (fockSectorOp Hs D₂ A n) (fockSectorCore_le_fockSectorDom Hs D₂ D n)) := essentiallySelfAdjointOn_of_graphCore _ _ (isGraphCore_fockSectorCore Hs D₂ A D hcore n) hesa
