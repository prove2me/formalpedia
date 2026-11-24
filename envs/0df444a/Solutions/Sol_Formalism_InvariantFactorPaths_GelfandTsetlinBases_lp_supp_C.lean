-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.lp_supp_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:41:50.783556+00:00
-- url     : https://prove2.me/submissions/be28754c-24f7-4b9c-a887-5aecfc6db926

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_lp_supp_CT

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
theorem _root_.solution {p : A} (hp : p ≠ 0) :
    (LaurentPolynomial.C p).coeff.support = {0} := by
  have := lp_supp_CT hp 0
  simpa using this
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
