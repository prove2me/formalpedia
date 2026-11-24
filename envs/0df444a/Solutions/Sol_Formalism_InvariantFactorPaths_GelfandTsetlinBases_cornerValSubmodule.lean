-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.cornerValSubmodule
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:11:50.994605+00:00
-- url     : https://prove2.me/submissions/a4097cbf-d37f-4f7c-8917-e82284a3b73f

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_val_add
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_lam_add
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_val_smul_le
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_lam_smul_le

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
theorem _root_.solution : PropVdSub := by
  intro k _ ι ζ n isVec S _ θ M c G H
  constructor
  · intro h1 h2
    exact le_trans (le_min (val_smul_le isVec S θ c G h1) h2) (val_add isVec S _ _)
  · intro h1 h2
    exact le_trans (lam_add isVec S _ _) (max_le (lam_smul_le isVec S M c G h1) h2)
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
