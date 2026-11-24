-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A0.col_all
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:11:55.913512+00:00
-- url     : https://prove2.me/submissions/2454f4d5-3767-48d5-8a41-d6e15607367a

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_ValuationProductsComponents
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ValuationProductsComponents
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A0_wge_sum
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A0_wge_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A0_wge_int
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A0_wge_X
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A0_gH_out

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
variable {k isVec S}
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.A0
theorem _root_.solution {i : ℕ} {μ : ℕ → Fin n → ℤ} (hS : ∀ j, j ∈ S ↔ j < i) (c : ℤ) (last : Bool) (s a : ℤ)
    (h0 : ∀ J : Finset (Fin n), WGe isVec S last s
      (gH k isVec S (pathWord isVec μ c (fun j a => (X (j, a) : MvPolynomial (ℕ × Fin n) k)) i J)) a)
    (N : ℕ) (hN : i ≤ N) : ∀ J : Finset (Fin n), WGe isVec S last s
      (gH k isVec S (pathWord isVec μ c (fun j a => (X (j, a) : MvPolynomial (ℕ × Fin n) k)) N J)) a := by
  induction N, hN using Nat.le_induction with
  | base => exact h0
  | succ N hN ih =>
    intro J
    by_cases hch : colHeight (μ (N + 1)) c = colHeight (μ N) c
    · rw [pathWord, if_pos hch]
      exact ih J
    · rw [pathWord, if_neg hch]
      have hout : N ∉ S := fun h => by have := (hS N).1 h; omega
      have hX : ∀ b : Fin n, WGe isVec S last s (gH k isVec S (X (N, b))) 0 := by
        intro b
        rw [gH_out k isVec S hout]
        exact wge_X _ (by simp [wtX, hout])
      unfold stepF
      split
      · unfold wedgeF
        rw [map_sum]
        refine wge_sum _ _ fun b _ => ?_
        rw [map_mul, map_mul, map_intCast]
        have := wge_mul (wge_mul (wge_int (isVec := isVec) (S := S) (last := last) (s := s)
          (L := GenField k n) (ζ := Empty) (n := n) (sg J b)) (ih (J.erase b))) (hX b)
        simpa using this
      · unfold contrF
        rw [map_sum]
        refine wge_sum _ _ fun b _ => ?_
        rw [map_mul, map_mul, map_intCast]
        have := wge_mul (wge_mul (wge_int (isVec := isVec) (S := S) (last := last) (s := s)
          (L := GenField k n) (ζ := Empty) (n := n) (sg J b)) (hX b)) (ih (insert b J))
        simpa using this
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A0
