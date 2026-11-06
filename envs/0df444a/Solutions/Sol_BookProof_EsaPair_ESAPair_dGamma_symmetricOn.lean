-- Prove2me | solution 1 for BookProof.EsaPair.ESAPair.dGamma_symmetricOn
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T18:56:06.923031+00:00
-- url     : https://prove2.me/submissions/ad04844d-cae9-45ea-978a-3c13ae07f3b8

import Definitions.Def_ChapterEsaPairDGamma
import Theorems.Thm_BookProof_SecondQuantizationCore_symmetricOn_dGammaCoreOp

open BookProof.DirectSumEsa
open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.TensorCore
open BookProof.EsaPair
open BookProof.SecondQuantizationCore

noncomputable section

variable {Hs : IPSpace} (P : ESAPair Hs)

theorem solution :
    SymmetricOn (dsCore (fun n : ℕ => fockSectorCore Hs P.closureDomain P.coreDomain n))
      P.dGammaOp := by
  exact symmetricOn_dGammaCoreOp Hs P.closureDomain P.closureOp P.coreDomain P.symmetric
