-- Prove2me | solution 1 for BookProof.QgTruncationResolvent.secHam_esa_core
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T18:50:52.991836+00:00
-- url     : https://prove2.me/submissions/bd8b264e-027a-4b5e-b759-9dc7a301d435

-- Generated from ChapterQgTruncationResolvent.lean — theorem BookProof.QgTruncationResolvent.secHam_esa_core
import Definitions.Def_ChapterScalaronOuterFockFL
import Theorems.Thm_BookProof_QgTruncationResolvent_esa_core_of_ext
open BookProof.ScalaronFiberFL
open BookProof.ScalaronFiberFL.WallPot
open BookProof.QgTruncationResolvent



open Filter Topology
open BookProof.FarisLavine BookProof.EsaClosure BookProof.StoneBridge
open BookProof.ChapterStoneResolvent BookProof.ChapterSirkTrotterKato
open BookProof.QgOuterFockCoreFL BookProof.ScalaronFiberFL BookProof.ScalaronOuterFockFL
open BookProof.ScalaronEsa BookProof.DirectSumEsa

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

variable {ι : Type*}
variable (W : WallPot) (Q : QgModeData ι)

theorem solution : EssentiallySelfAdjointOn (secCore (ι := ι)) (secHam W Q) := by
  exact esa_core_of_ext (secData W Q) (secHam_essentiallySelfAdjointOn W Q)
