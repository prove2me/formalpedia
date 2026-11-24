-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qd_trans_diag
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:57:19.073898+00:00
-- url     : https://prove2.me/submissions/1a7c06e1-3691-4863-b65a-2356bd77b252

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
theorem _root_.solution {R : Type} [CommRing R] (a b : Fin n) (hab : a ≠ b) (t : R) (i : Fin n) :
    (qd_trans a b hab t).val i i = 1 := by
  have : (qd_trans a b hab t).val = Matrix.transvection a b t := rfl
  rw [this, Matrix.transvection, Matrix.add_apply, Matrix.one_apply_eq, Matrix.single_apply]
  rw [if_neg (by rintro ⟨rfl, h⟩; exact hab h.symm), add_zero]
end Formalism.InvariantFactorPaths.ColumnFamilies
