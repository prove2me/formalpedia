-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.lp_coeff_TC
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:47:50.44142+00:00
-- url     : https://prove2.me/submissions/0a3a5d42-89a6-49c0-952a-df365fe7af82

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
theorem _root_.solution (p : A) (m j : ℤ) :
    (LaurentPolynomial.T m * LaurentPolynomial.C p).coeff j = if m = j then p else 0 := by
  rw [LaurentPolynomial.T_mul, ← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single,
    Finsupp.single_apply]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
