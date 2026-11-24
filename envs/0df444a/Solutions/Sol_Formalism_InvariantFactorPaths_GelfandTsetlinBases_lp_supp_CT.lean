-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.lp_supp_CT
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:47:50.561891+00:00
-- url     : https://prove2.me/submissions/86fb4066-0f79-4fe7-bc13-64633acbbf26

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
theorem _root_.solution {p : A} (hp : p ≠ 0) (m : ℤ) :
    (LaurentPolynomial.C p * LaurentPolynomial.T m).coeff.support = {m} :=
  LaurentPolynomial.support_coeff_C_mul_T_of_ne_zero hp m
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
