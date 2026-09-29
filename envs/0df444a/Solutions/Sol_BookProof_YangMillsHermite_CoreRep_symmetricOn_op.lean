-- Prove2me | solution 1 for BookProof.YangMillsHermite.CoreRep.symmetricOn_op
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T02:34:41.286637+00:00
-- url     : https://prove2.me/submissions/a34f812b-53bd-48be-9b83-9c78d2cbd815

-- Generated from ChapterYangMillsHermite.lean — solution of BookProof.YangMillsHermite.CoreRep.symmetricOn_op
import Mathlib
import Definitions.Def_ChapterYangMillsHermite
import Theorems.Thm_BookProof_YangMillsHermite_inner_pgLp_pgLp
import Theorems.Thm_BookProof_YangMillsHermite_CoreRep_coe_op
import Theorems.Thm_BookProof_YangMillsHermite_CoreRep_coe_symm
open BookProof.YangMillsHermite
open BookProof.YangMillsHermite.CoreRep








open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension BookProof.HashimotoShiftInvert

noncomputable section

variable {d : ℕ}

















































variable {D : Submodule ℂ (L2d d)}

set_option maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
-- the `L²` coercions in the rewrite chain need more than the default budget
theorem solution (Φ : CoreRep d D) {T : Module.End ℂ (MvPolynomial (Fin d) ℂ)}
    (hT : PolySym T) : SymmetricOn D (D.subtype.comp (Φ.op T)) := by

  intro x y
  have hx : ((D.subtype.comp (Φ.op T)) x) = pgLp (T (Φ.equiv.symm x)) := Φ.coe_op T x
  have hy : ((D.subtype.comp (Φ.op T)) y) = pgLp (T (Φ.equiv.symm y)) := Φ.coe_op T y
  have hcx : ((x : D) : L2d d) = pgLp (Φ.equiv.symm x) := Φ.coe_symm x
  have hcy : ((y : D) : L2d d) = pgLp (Φ.equiv.symm y) := Φ.coe_symm y
  have e1 := inner_pgLp_pgLp (T (Φ.equiv.symm x)) (Φ.equiv.symm y)
  have e2 := inner_pgLp_pgLp (Φ.equiv.symm x) (T (Φ.equiv.symm y))
  rw [hx, hy, hcx, hcy, e1, e2]
  exact hT _ _
