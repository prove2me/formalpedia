-- Prove2me | solution 1 for BookProof.YangMillsHermite.CoreRep.coe_op
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T02:24:27.810416+00:00
-- url     : https://prove2.me/submissions/8bcc4063-38e4-4673-8d68-e4279e94c59b

-- Generated from ChapterYangMillsHermite.lean — solution of BookProof.YangMillsHermite.CoreRep.coe_op
import Mathlib
import Definitions.Def_ChapterYangMillsHermite
import Theorems.Thm_BookProof_YangMillsHermite_CoreRep_op_apply
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
    ((Φ.op T x : D) : L2d d) = pgLp (T (Φ.equiv.symm x)) := by

  rw [CoreRep.op_apply, Φ.coe_equiv]
