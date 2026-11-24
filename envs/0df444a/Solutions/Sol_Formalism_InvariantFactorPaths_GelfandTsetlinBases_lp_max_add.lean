-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.lp_max_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:47:50.656292+00:00
-- url     : https://prove2.me/submissions/a4ac823c-4af6-4ccb-b10e-5922e0764c29

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
variable {A : Type*} [CommRing A] [IsDomain A]
omit [IsDomain A]
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
theorem _root_.solution (x y : LaurentPolynomial A) :
    (x + y).coeff.support.max ≤ max x.coeff.support.max y.coeff.support.max := by
  classical
  apply Finset.max_le
  intro c hc
  rw [AddMonoidAlgebra.coeff_add] at hc
  rcases Finset.mem_union.mp (Finsupp.support_add hc) with h | h
  · exact le_max_of_le_left (Finset.le_max h)
  · exact le_max_of_le_right (Finset.le_max h)
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
