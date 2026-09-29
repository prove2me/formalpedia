-- Prove2me | solution 1 for BookProof.YangMillsHermite.CoreRep.coe_symm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T01:45:46.872527+00:00
-- url     : https://prove2.me/submissions/ca1aa94d-99f8-4573-a94c-c62dd37cf40d

-- Generated from ChapterYangMillsHermite.lean — solution of BookProof.YangMillsHermite.CoreRep.coe_symm
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
theorem solution (Φ : CoreRep d D) (x : D) : ((x : D) : L2d d) = pgLp (Φ.equiv.symm x) := by

  rw [← Φ.coe_equiv (Φ.equiv.symm x), LinearEquiv.apply_symm_apply]
