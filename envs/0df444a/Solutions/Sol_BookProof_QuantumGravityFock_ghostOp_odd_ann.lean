-- Prove2me | solution 1 for BookProof.QuantumGravityFock.ghostOp_odd_ann
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T07:50:27.463992+00:00
-- url     : https://prove2.me/submissions/47b5ae03-5b1f-4d52-a787-31d9ae6ea329

-- Generated from ChapterQuantumGravityFock.lean — solution of BookProof.QuantumGravityFock.ghostOp_odd_ann
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
theorem solution (j : ℕ) (z : QGGraded) :
    qgGrade (ghostOp (fermAnn j) z) = - ghostOp (fermAnn j) (qgGrade z) := by

  induction z using TensorProduct.induction_on with
  | zero => simp [qgGrade]; abel
  | tmul x y =>
      simp only [qgGrade, ghostOp_tmul, fermGrade_fermAnn]
      rw [TensorProduct.tmul_neg]
  | add z w hz hw =>
      simp only [map_add, hz, hw]
      abel
