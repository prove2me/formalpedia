-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A0.gH_out
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:46:35.485931+00:00
-- url     : https://prove2.me/submissions/3a6737a4-31d1-4bfc-a7dc-7204f1d84b02

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_ValuationProductsComponents
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ValuationProductsComponents

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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.A0
variable (k : Type) [Field k] {n : ℕ} (isVec : ℕ → Bool) (S : Set ℕ) [DecidablePred (· ∈ S)]
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.A0
theorem _root_.solution {j : ℕ} (hj : j ∉ S) (a : Fin n) :
    gH k isVec S (X (j, a)) = X (Sum.inl (j, a)) := by
  simp [gH, sharpHom, hj]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A0
