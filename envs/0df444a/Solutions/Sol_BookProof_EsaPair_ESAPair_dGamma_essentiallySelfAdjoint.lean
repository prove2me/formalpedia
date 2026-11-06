-- Prove2me | solution 1 for BookProof.EsaPair.ESAPair.dGamma_essentiallySelfAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:01:04.365208+00:00
-- url     : https://prove2.me/submissions/56985bc8-2735-441b-9064-ba7ab9b2eaf7

import Definitions.Def_ChapterEsaPairDGamma
import Theorems.Thm_BookProof_SecondQuantizationCore_dGamma_essentiallySelfAdjointOn_fockCore

open BookProof.FarisLavine BookProof.TensorCore
open BookProof.DirectSumEsa
open BookProof.SecondQuantizationCore
open BookProof.EsaPair

noncomputable section

variable {Hs : IPSpace} (P : ESAPair Hs)

theorem solution :
    EssentiallySelfAdjointOn
      (dsCore (fun n : ℕ => fockSectorCore Hs P.closureDomain P.coreDomain n)) P.dGammaOp :=
  BookProof.SecondQuantizationCore.dGamma_essentiallySelfAdjointOn_fockCore
    Hs P.closureDomain P.closureOp P.coreDomain P.is_core P.sector_esa
