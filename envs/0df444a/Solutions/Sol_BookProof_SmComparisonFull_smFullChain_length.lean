-- Prove2me | solution 1 for BookProof.SmComparisonFull.smFullChain_length
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:56:16.904929+00:00
-- url     : https://prove2.me/submissions/b6c5f7b4-7b06-4a3a-8d96-988bb1382b1f

import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterTensorSumChain
import Definitions.Def_ChapterSmComparison
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterEsaClosureCore
import Mathlib
import Definitions.Def_ChapterSmComparisonFull
import Definitions.Def_ChapterBddBelowFiberSumEsa

open BookProof.FarisLavine
open BookProof.ScalaronEsa
open BookProof.StoneBridge BookProof.ChapterStoneResolvent BookProof.EsaClosure
open MeasureTheory

noncomputable section

theorem solution : BookProof.SmComparisonFull.smFullFactors.length + 1 = 160 := by
  simp [BookProof.SmComparisonFull.smFullFactors]
