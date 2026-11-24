-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1.isPath_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:46:35.694799+00:00
-- url     : https://prove2.me/submissions/aaec7000-c986-41c3-8820-eda3dd4f2935

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IsWeightedHomogeneousZeroStripPathWord

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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1
theorem _root_.solution {n N : ℕ} {isVec : ℕ → Bool} {B : ℕ → ℕ} {μ μ' : ℕ → Fin n → ℤ}
    (h : ∀ i ≤ N, μ i = μ' i) (hp : IsPath n isVec B μ N) : IsPath n isVec B μ' N := by
  obtain ⟨h0, h1, h2⟩ := hp
  refine ⟨by rw [← h 0 (Nat.zero_le _)]; exact h0, fun i hi => by rw [← h i hi]; exact h1 i hi, fun i hi => ?_⟩
  rw [← h i hi.le, ← h (i + 1) hi]
  exact h2 i hi
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1
