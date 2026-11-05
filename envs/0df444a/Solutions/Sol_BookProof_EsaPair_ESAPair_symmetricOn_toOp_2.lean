-- Prove2me | solution 2 for BookProof.EsaPair.ESAPair.symmetricOn_toOp
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:14:18.731687+00:00
-- url     : https://prove2.me/submissions/94fc58d8-2949-43ec-96e5-4fa318d38fd4

-- Generated from ChapterEsaPairDGamma.lean — solution of BookProof.EsaPair.ESAPair.symmetricOn_toOp
import Mathlib
import Definitions.Def_ChapterEsaPairDGamma
import Theorems.Thm_BookProof_FriedrichsSquare_IsFriedrichsSqExtension_symmetric
import Theorems.Thm_BookProof_GraphCore_symmetricOn_restrictOp
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterStoneConverse
import Definitions.Def_ChapterTensorGraphCore
open BookProof.EsaPair

open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.TensorCore
open BookProof.ChapterStoneMeasurable
open BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup
open BookProof.TensorCore

noncomputable section

variable {Hs : IPSpace} (P : ESAPair Hs)

set_option maxHeartbeats 1000000 in
theorem solution : SymmetricOn P.coreDomain P.toOp := symmetricOn_restrictOp _ _ P.symmetric
