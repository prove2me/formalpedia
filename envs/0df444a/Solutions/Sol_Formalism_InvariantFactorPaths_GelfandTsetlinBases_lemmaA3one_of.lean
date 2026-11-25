-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.lemmaA3one_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:05:13.690826+00:00
-- url     : https://prove2.me/submissions/a8fd7ce7-3bff-467a-8683-8addfa28ddee

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_CorA3primeB
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ValuationProductsComponents
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_NormIndexCountBound
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_UnitAndFieldPowerLemmas
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_ExponentSetCounting_a3one_of_factSplit_of_countCont

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
theorem _root_.solution : LemmaA2indep → PathIdxFinite → PolBRank → LemmaA3top → FactSplit → CountCont →
    StdCountGT → LemmaA3one :=
  fun hI hfin hR hT hF hC _ => ExponentSetCounting.a3one_of_factSplit_of_countCont hI hfin hR hT hF hC
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
