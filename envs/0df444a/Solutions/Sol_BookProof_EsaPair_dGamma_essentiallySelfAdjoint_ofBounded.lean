-- Prove2me | solution 1 for BookProof.EsaPair.dGamma_essentiallySelfAdjoint_ofBounded
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-06T15:11:57.657627+00:00
-- url     : https://prove2.me/submissions/9e11a47a-f07b-4fa9-b06b-d1298688a04d

-- Generated from ChapterEsaPairDGamma.lean — solution of BookProof.EsaPair.dGamma_essentiallySelfAdjoint_ofBounded
import Mathlib
import Definitions.Def_ChapterEsaPairDGamma
import Theorems.Thm_BookProof_EsaPair_ESAPair_dGamma_essentiallySelfAdjoint
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterSirkTrotterKatoGalerkin
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterSecondQuantizationCoreEsa
open BookProof.EsaPair




open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.TensorCore
open BookProof.DirectSumEsa
open BookProof.TensorCore
-- `fockSectorCore` lives in `BookProof.SecondQuantizationCore`
-- (`Definitions.Def_ChapterSecondQuantizationCoreEsa`); the published bundle was
-- compiled from its published text on 2026-11-06 and does declare it.
open BookProof.SecondQuantizationCore

noncomputable section

variable {Hs : IPSpace} (P : ESAPair Hs)

set_option maxHeartbeats 1000000 in
theorem solution (Hs : IPSpace)
    (B : (⊤ : Submodule ℂ Hs.carrier) →ₗ[ℂ] Hs.carrier) (hB : SymmetricOn ⊤ B) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ a : (⊤ : Submodule ℂ Hs.carrier), ‖B a‖ ≤ C * ‖(a : Hs.carrier)‖)
    (D : Submodule ℂ Hs.carrier) (hdense : Dense (D : Set Hs.carrier)) :
    EssentiallySelfAdjointOn (dsCore (fun n : ℕ => fockSectorCore Hs ⊤ D n))
      (dGammaCoreOp Hs ⊤ B D) := (ESAPair.ofBounded Hs B hB hC0 hC D hdense).dGamma_essentiallySelfAdjoint
