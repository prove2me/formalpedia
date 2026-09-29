-- Prove2me | solution 1 for BookProof.YangMillsHermite.CoreRep.op_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T01:47:27.220973+00:00
-- url     : https://prove2.me/submissions/7057bfe3-a311-4d61-9225-84dee25bfdab

-- Generated from ChapterYangMillsHermite.lean — solution of BookProof.YangMillsHermite.CoreRep.op_apply
import Mathlib
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsHermite
open BookProof.YangMillsHermite.CoreRep








open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension BookProof.HashimotoShiftInvert

noncomputable section

variable {d : ℕ}

















































variable {D : Submodule ℂ (L2d d)}

set_option maxHeartbeats 1000000 in
theorem solution (Φ : CoreRep d D) (T : Module.End ℂ (MvPolynomial (Fin d) ℂ)) (x : D) :
    Φ.op T x = Φ.equiv (T (Φ.equiv.symm x)) := rfl
