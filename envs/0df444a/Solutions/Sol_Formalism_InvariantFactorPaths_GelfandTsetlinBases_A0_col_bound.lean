-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A0.col_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:54:13.19544+00:00
-- url     : https://prove2.me/submissions/fc8dd677-5893-407f-a8af-b236b183c563

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_ValuationProductsComponents
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ValuationProductsComponents
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A0_height_full
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A0_height_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A0_idx_univ

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
theorem _root_.solution {n : ℕ} {ν : Fin n → ℤ} (hν : Antitone ν) (c : ℤ) (last : Bool) (m : Fin n)
    (hm : if last then m.val + 1 = n else m.val = 0) (J : Finset (Fin n))
    (hJ : J.card = if 1 ≤ c then colHeight ν c else n - colHeight ν c) :
    sgn last * bc c (ν m) ≤ sgn last * (if m ∈ J then (if 1 ≤ c then 1 else -1) else 0) := by
  cases last
  · simp only [Bool.false_eq_true, if_false] at hm
    by_cases h1 : 1 ≤ c
    · by_cases h2 : c ≤ ν m
      · simp only [sgn, bc, h1, h2, if_true, Bool.false_eq_true, if_false]
        split_ifs <;> norm_num
      · rw [if_pos h1, height_zero hν hm (not_le.1 h2), Finset.card_eq_zero] at hJ
        subst hJ
        simp [sgn, bc, h1, h2]
    · by_cases h2 : ν m < c
      · rw [if_neg h1, height_zero hν hm h2, Nat.sub_zero] at hJ
        rw [idx_univ hJ]
        simp [sgn, bc, h1, h2]
      · simp only [sgn, bc, h1, h2, Bool.false_eq_true, if_false]
        split_ifs <;> norm_num
  · simp only [if_true] at hm
    by_cases h1 : 1 ≤ c
    · by_cases h2 : c ≤ ν m
      · rw [if_pos h1, height_full hν hm h2] at hJ
        rw [idx_univ hJ]
        simp [sgn, bc, h1, h2]
      · simp only [sgn, bc, h1, h2, if_true, if_false]
        split_ifs <;> norm_num
    · by_cases h2 : ν m < c
      · simp only [sgn, bc, h1, h2, if_true, if_false]
        split_ifs <;> norm_num
      · rw [if_neg h1, height_full hν hm (not_lt.1 h2), Nat.sub_self, Finset.card_eq_zero] at hJ
        subst hJ
        simp [sgn, bc, h1, h2]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A0
