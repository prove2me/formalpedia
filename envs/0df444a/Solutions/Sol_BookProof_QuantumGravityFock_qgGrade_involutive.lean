-- Prove2me | solution 1 for BookProof.QuantumGravityFock.qgGrade_involutive
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:08:08.911992+00:00
-- url     : https://prove2.me/submissions/a7ddaa8c-6a08-4b64-8c41-c1b3f841a955

-- Generated from ChapterQuantumGravityFock.lean — solution of BookProof.QuantumGravityFock.qgGrade_involutive
import Mathlib
import Definitions.Def_ChapterQuantumGravityFock
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesFockSpace
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.QuantumGravityFock




open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.FockOfFock BookProof.NavierStokesFlow.FullEsa
open BookProof.FarisLavine BookProof.StoneBridge BookProof.EsaClosure
open BookProof.ChapterStoneResolvent BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.HashimotoShiftInvert
open BookProof.FockSecondQuantization

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (z : QGGraded) : qgGrade (qgGrade z) = z := by

  induction z using TensorProduct.induction_on with
  | zero => simp [qgGrade]
  | tmul x y => simp [qgGrade, fermGrade_involutive]
  | add z w hz hw => rw [map_add, map_add, hz, hw]
