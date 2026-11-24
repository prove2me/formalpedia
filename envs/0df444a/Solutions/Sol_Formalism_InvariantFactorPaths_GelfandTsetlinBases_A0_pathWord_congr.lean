-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A0.pathWord_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:46:33.885953+00:00
-- url     : https://prove2.me/submissions/4937f783-b38f-4dea-9a0c-adbba7772789

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
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.A0
theorem _root_.solution {R : Type*} [CommRing R] {n : ℕ} (isVec : ℕ → Bool) (μ : ℕ → Fin n → ℤ) (c : ℤ)
    (Xr Xr' : ℕ → Fin n → R) : ∀ j : ℕ, (∀ l < j, Xr l = Xr' l) →
      pathWord isVec μ c Xr j = pathWord isVec μ c Xr' j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro h
    rw [pathWord, pathWord, ih fun l hl => h l (by omega), h j (by omega)]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A0
