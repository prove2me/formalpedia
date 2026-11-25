-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.lemmaA3field_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:05:07.631196+00:00
-- url     : https://prove2.me/submissions/63c4591c-8cb4-4947-ac27-ffd7ef73fec9

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_CorA3primeB
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ValuationProductsComponents
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_NormIndexCountBound
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_UnitAndFieldPowerLemmas
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_ExponentSetCounting_a3field_of_a2indep_of_a3one

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
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
theorem _root_.solution : LemmaA2indep → LemmaA3one → LemmaA3field :=
  ExponentSetCounting.a3field_of_a2indep_of_a3one
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
