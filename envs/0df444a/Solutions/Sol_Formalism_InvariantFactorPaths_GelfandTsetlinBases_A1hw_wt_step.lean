-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1hw.wt_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:54:44.9746+00:00
-- url     : https://prove2.me/submissions/5ff9c900-fae0-4021-851a-a5b26875bd14

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1hw_hom_int

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
theorem _root_.solution {σ R : Type*} [CommRing R] {n : ℕ} (w : σ → ℤ) (up : Bool) (m : Fin n) (s : ℤ)
    (Kf : Form (MvPolynomial σ R) n) (Xv : Fin n → MvPolynomial σ R)
    (hK : ∀ J, IsWeightedHomogeneous w (Kf J) (if m ∈ J then s else 0))
    (hX : ∀ m', IsWeightedHomogeneous w (Xv m') (if m' = m then (if up then s else -s) else 0))
    (J : Finset (Fin n)) : IsWeightedHomogeneous w (stepF up Kf Xv J) (if m ∈ J then s else 0) := by
  unfold stepF
  cases up
  · simp only [Bool.false_eq_true, if_false] at hX ⊢
    unfold contrF
    refine IsWeightedHomogeneous.sum _ _ _ fun m' hm' => ?_
    have := ((hom_int (R := R) w (sg J m')).mul (hX m')).mul (hK (insert m' J))
    convert this using 1
    rw [Finset.mem_compl] at hm'
    by_cases h : m' = m
    · subst h; simp [hm']
    · have h2 : m ∈ insert m' J ↔ m ∈ J := by simp [Finset.mem_insert, Ne.symm h]
      simp [h, h2]
  · simp only [if_true] at hX ⊢
    unfold wedgeF
    refine IsWeightedHomogeneous.sum _ _ _ fun m' hm' => ?_
    have := ((hom_int (R := R) w (sg J m')).mul (hK (J.erase m'))).mul (hX m')
    convert this using 1
    by_cases h : m' = m
    · subst h; simp [hm']
    · have h2 : m ∈ J.erase m' ↔ m ∈ J := by simp [Finset.mem_erase, Ne.symm h]
      simp [h, h2]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1hw
