-- Prove2me | solution 1 for BookProof.ScalarDGamma.dGamma_scalar_essentiallySelfAdjointOn_fockCore
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-02T13:24:55.278937+00:00
-- url     : https://prove2.me/submissions/431a76b0-7f4c-4a0e-9a7e-5ec7f929b318

-- Generated from ChapterScalarDGammaEsa.lean — solution of BookProof.ScalarDGamma.dGamma_scalar_essentiallySelfAdjointOn_fockCore
import Mathlib
import Definitions.Def_ChapterScalarDGammaEsa
import Theorems.Thm_BookProof_ScalarDGamma_essentiallySelfAdjointOn_fockSectorDom_scalar
import Theorems.Thm_BookProof_SecondQuantizationCore_dGamma_essentiallySelfAdjointOn_fockCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterSecondQuantizationCoreEsa
open BookProof.ScalarDGamma




open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.TensorCore
open BookProof.DirectSumEsa
open BookProof.TensorCore
open BookProof.SecondQuantizationCore

noncomputable section

variable (Hs : IPSpace) (c : ℝ)

variable (Hs : IPSpace) (c : ℝ)

set_option maxHeartbeats 1000000 in
theorem solution {D : Submodule ℂ Hs.carrier}
    (hdense : Dense (D : Set Hs.carrier)) :
    EssentiallySelfAdjointOn (dsCore (fun n : ℕ => fockSectorCore Hs ⊤ D n))
      (dGammaCoreOp Hs ⊤ (scalarOp Hs c) D) :=
  dGamma_essentiallySelfAdjointOn_fockCore Hs ⊤ (scalarOp Hs c) D
      (isGraphCore_scalarOp Hs c hdense)
      (essentiallySelfAdjointOn_fockSectorDom_scalar Hs c)
