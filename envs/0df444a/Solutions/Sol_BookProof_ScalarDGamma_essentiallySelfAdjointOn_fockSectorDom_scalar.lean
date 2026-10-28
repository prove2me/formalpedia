-- Prove2me | solution 1 for BookProof.ScalarDGamma.essentiallySelfAdjointOn_fockSectorDom_scalar
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-25T02:19:26.669475+00:00
-- url     : https://prove2.me/submissions/7b47f379-db65-49b2-b336-0c8c0a54c559

-- Generated from ChapterScalarDGammaEsa.lean — solution of BookProof.ScalarDGamma.essentiallySelfAdjointOn_fockSectorDom_scalar
import Mathlib
import Definitions.Def_ChapterScalarDGammaEsa
import Theorems.Thm_BookProof_ScalarDGamma_dense_fockSectorDom
import Theorems.Thm_BookProof_ScalarDGamma_norm_fockSectorOp_scalar_le
import Theorems.Thm_BookProof_GraphCore_essentiallySelfAdjointOn_of_bounded_dense
import Theorems.Thm_BookProof_SecondQuantizationCore_symmetricOn_fockSectorOp
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterSecondQuantizationCoreEsa
open BookProof.ScalarDGamma




open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.TensorCore
open BookProof.TensorCore
open BookProof.SecondQuantizationCore

noncomputable section

variable (Hs : IPSpace) (c : ℝ)

variable (Hs : IPSpace) (c : ℝ)

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) :
    EssentiallySelfAdjointOn (fockSectorDom Hs ⊤ n) (fockSectorOp Hs ⊤ (scalarOp Hs c) n) :=
  essentiallySelfAdjointOn_of_bounded_dense _
      (symmetricOn_fockSectorOp Hs ⊤ (scalarOp Hs c) (symmetricOn_scalarOp Hs c) n)
      (by positivity) (norm_fockSectorOp_scalar_le Hs c n) (dense_fockSectorDom Hs n)
