-- Prove2me | solution 1 for BookProof.WallEsaBddBelow.constOp_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-18T06:01:59.568919+00:00
-- url     : https://prove2.me/submissions/034b322a-e8e3-4809-a67e-79023b3c3fb1

-- Generated from ChapterWallEsaBddBelow.lean — solution of BookProof.WallEsaBddBelow.constOp_symmetric
import Mathlib
import Definitions.Def_ChapterWallEsaBddBelow
import Definitions.Def_ChapterKatoRellichDeficiencyCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterScalaronWallEsa
import Definitions.Def_ChapterKatoRellichDeficiency
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
open BookProof.WallEsaBddBelow




open MeasureTheory SchwartzMap Set
open BookProof.FarisLavine BookProof.ScalaronEsa BookProof.ScalaronWallEsa
open BookProof.KatoRellich BookProof.StoneBridge BookProof.EsaClosure
open BookProof.ChapterStoneResolvent

noncomputable section

set_option maxHeartbeats 1000000 in

theorem solution (c : ℝ) (x y : Lp ℂ 2 (volume : Measure ℝ)) :
    (inner ℂ (constOp c x) y : ℂ) = inner ℂ x (constOp c y) := by
  simp only [constOp, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    inner_smul_left, inner_smul_right, Complex.conj_ofReal]
