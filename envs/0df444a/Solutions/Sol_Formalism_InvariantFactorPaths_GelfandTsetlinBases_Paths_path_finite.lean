-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.Paths.path_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:55:28.961027+00:00
-- url     : https://prove2.me/submissions/6e3a0fa0-6a84-4fb1-b7c3-2a9beb87e5d6

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Paths_changed_finite

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
open Paths
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.Paths
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.Paths
theorem _root_.solution {n N : ℕ} {isVec : ℕ → Bool} {B : ℕ → ℕ} {μ : ℕ → Fin n → ℤ}
    (hp : IsPath n isVec B μ N) {i : ℕ} (hi : i < N) :
    {c : ℤ | colHeight (μ (i + 1)) c ≠ colHeight (μ i) c}.Finite := by
  obtain ⟨-, ha, hs⟩ := hp
  have h := hs i hi
  by_cases hv : isVec i = true
  · rw [if_pos hv] at h
    exact changed_finite (ha _ hi) (ha _ hi.le) h
  · rw [if_neg hv] at h
    have := changed_finite (ha _ hi.le) (ha _ hi) h
    simp only [ne_comm] at this ⊢
    exact this
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.Paths
