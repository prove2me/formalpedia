-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri.Lo_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:47:58.517486+00:00
-- url     : https://prove2.me/submissions/8b235b9c-24be-4b1a-92cb-72e5c5edc2aa

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementP
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_AntitoneOfMemGtBox
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Pieri_Lo_castSucc
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Pieri_Lo_last

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
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri
theorem _root_.solution {n : ℕ} (μ ν : Fin (n + 1) → ℤ) (l : Fin n → ℤ) :
    (∀ j, Lo μ l j ≤ ν j) ↔ (∀ j, μ j ≤ ν j) ∧ (∀ i : Fin n, l i ≤ ν i.castSucc) := by
  constructor
  · intro h
    refine ⟨fun j => le_trans (le_max_left _ _) (h j), fun i => ?_⟩
    have := h i.castSucc
    rw [Lo_castSucc] at this
    exact le_trans (le_max_right _ _) this
  · rintro ⟨h1, h2⟩ j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · rw [Lo_last]; exact h1 _
    · rw [Lo_castSucc]; exact max_le (h1 _) (h2 i)
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri
