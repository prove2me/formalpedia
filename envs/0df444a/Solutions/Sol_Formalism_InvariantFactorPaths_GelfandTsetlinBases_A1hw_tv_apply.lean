-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1hw.tv_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:16:51.41206+00:00
-- url     : https://prove2.me/submissions/0ccc2e8a-f6a4-4f97-ba89-59635c3e926d

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight

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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1hw
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1hw
theorem _root_.solution {A : Type*} [CommRing A] {n : ℕ} (a b : Fin n) (t : A) (i j : Fin n) :
    Matrix.transvection a b t i j = (if i = j then 1 else 0) + if a = i ∧ b = j then t else 0 := by
  simp [Matrix.transvection, Matrix.one_apply, Matrix.single_apply]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1hw
