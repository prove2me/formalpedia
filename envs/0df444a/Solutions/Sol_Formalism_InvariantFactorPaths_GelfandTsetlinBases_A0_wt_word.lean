-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A0.wt_word
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:02:49.625745+00:00
-- url     : https://prove2.me/submissions/dca3f3f8-1535-4a82-9556-1000849b5afe

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_ValuationProductsComponents
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ValuationProductsComponents
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1hw_wt_step


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
theorem _root_.solution {L : Type*} [CommRing L] {n i : ℕ} (isVec : ℕ → Bool) (S : Set ℕ) [DecidablePred (· ∈ S)]
    (hS : ∀ j, j < i → j ∈ S) (μ : ℕ → Fin n → ℤ) (c : ℤ) (last : Bool) (m : Fin n)
    (hm : ∀ a : Fin n, (if last then a.val + 1 = n else a.val = 0) ↔ a = m) :
    ∀ j ≤ i, ∀ J : Finset (Fin n), IsWeightedHomogeneous (wtX (ζ := Empty) isVec S last)
      (pathWord isVec μ c (fun l a => (X (Sum.inl (l, a)) : MvPolynomial (LVar ℕ Empty n) L)) j J)
      (if m ∈ J then (if 1 ≤ c then 1 else -1) else 0) := by
  intro j
  induction j with
  | zero =>
    intro _ J
    show IsWeightedHomogeneous _ (if J = ∅ then 1 else 0) _
    split
    · rename_i h
      subst h
      simpa using isWeightedHomogeneous_one _ _
    · exact isWeightedHomogeneous_zero _ _ _
  | succ j ih =>
    intro hj J
    by_cases hch : colHeight (μ (j + 1)) c = colHeight (μ j) c
    · rw [pathWord, if_pos hch]
      exact ih (by omega) J
    · rw [pathWord, if_neg hch]
      refine A1hw.wt_step _ _ m _ _ _ (ih (by omega)) (fun m' => ?_) J
      have := isWeightedHomogeneous_X L (wtX (ζ := Empty) (n := n) isVec S last) (Sum.inl (j, m'))
      convert this using 1
      have hjS : j ∈ S := hS j (by omega)
      by_cases h1 : 1 ≤ c <;> cases hv : isVec j <;> by_cases h2 : m' = m <;>
        simp [wtX, hjS, hm, h1, hv, h2]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A0
