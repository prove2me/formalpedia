-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qd_mul_trans
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:36:36.997985+00:00
-- url     : https://prove2.me/submissions/555eba98-77e2-4444-bc2f-b2956c06e093

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
theorem _root_.solution {R : Type} [CommRing R] (x : GL (Fin n) R) (a b : Fin n) (hab : a ≠ b) (t : R) (i j : Fin n) :
    (x * qd_trans a b hab t).val i j = x.val i j + if j = b then t * x.val i a else 0 := by
  have : (x * qd_trans a b hab t).val = x.val * Matrix.transvection a b t := rfl
  rw [this]
  split_ifs with h
  · subst h; rw [Matrix.mul_transvection_apply_same]
  · rw [Matrix.mul_transvection_apply_of_ne _ _ _ _ h, add_zero]
end Formalism.InvariantFactorPaths.ColumnFamilies
