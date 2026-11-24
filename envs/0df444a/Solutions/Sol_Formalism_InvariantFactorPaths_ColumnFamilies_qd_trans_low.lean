-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qd_trans_low
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:57:19.171225+00:00
-- url     : https://prove2.me/submissions/06e120e4-25ed-4db4-9f7e-132518eb6320

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_FiltrationTheoremOfClauses
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalB
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_EqSmulCanonicalOfUnipotentInvariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility
variable {n : ℕ}
variable [NeZero n]
omit [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {R : Type} [CommRing R] (a b : Fin n) (hab : a < b) (t : R) (i j : Fin n) (hji : j < i) :
    (qd_trans a b hab.ne t).val i j = 0 := by
  have : (qd_trans a b hab.ne t).val = Matrix.transvection a b t := rfl
  rw [this, Matrix.transvection, Matrix.add_apply, Matrix.one_apply_ne hji.ne', Matrix.single_apply]
  rw [if_neg (by rintro ⟨rfl, rfl⟩; exact absurd hab (not_lt.mpr hji.le)), add_zero]
end Formalism.InvariantFactorPaths.ColumnFamilies
