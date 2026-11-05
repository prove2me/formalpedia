-- Prove2me | solution 1 for BookProof.SmComparisonFull.deriv_coordinate_esa
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-04T23:24:16.0272+00:00
-- url     : https://prove2.me/submissions/9c269097-8943-46c7-82f7-b0bd58364cae

-- Generated from ChapterSmComparisonFull.lean — solution of BookProof.SmComparisonFull.deriv_coordinate_esa
import Mathlib
import Definitions.Def_ChapterSmComparisonFull
import Theorems.Thm_BookProof_ScalaronEsa_smoothPotential_essentiallySelfAdjoint
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterTensorSumChain
import Definitions.Def_ChapterSmComparison
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterScalaronCoreEsa
open BookProof.SmComparisonFull




open BookProof.FarisLavine BookProof.TensorSumChain
open BookProof.SmComparison BookProof.ScalaronEsa
open BookProof.StoneBridge BookProof.ChapterStoneResolvent BookProof.EsaClosure
open MeasureTheory
open BookProof.ScalaronEsa

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution :
    EssentiallySelfAdjointOn (ccDomain ℝ) (opCc (fun x : ℝ => x ^ 2) contDiff_pow2) := smoothPotential_essentiallySelfAdjoint _ _
