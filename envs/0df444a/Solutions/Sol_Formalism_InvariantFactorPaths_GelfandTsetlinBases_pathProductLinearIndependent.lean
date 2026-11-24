-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.pathProductLinearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:29:32.175004+00:00
-- url     : https://prove2.me/submissions/aad06cf1-e7ad-49cf-804c-728da92792e7

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IsWeightedHomogeneousZeroStripPathWord
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1_LeadAt_comp_eq_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1_isPath_trunc
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1_psi_lead
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1_li_of_lead
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1_psiPath_congr
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1_isPath_congr
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1_end_determined
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1_psi_lead_unit

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
open A1
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
theorem _root_.solution : PathProductLinearIndependent := by
  intro k _ n N isVec B ν
  induction N generalizing ν with
  | zero =>
    by_cases hne : Nonempty (A1.Idx n isVec B 0 ν)
    swap
    · haveI := not_nonempty_iff.mp hne
      exact linearIndependent_empty_type
    obtain ⟨P0⟩ := hne
    have hν : ν = 0 := by
      obtain ⟨μ0, ⟨h00, -, -⟩, h01, -⟩ := P0
      exact h01.symm.trans h00
    subst hν
    have hall : ∀ P : A1.Idx n isVec B 0 0, P = P0 := by
      intro P
      obtain ⟨μ, ⟨hμ0, -, -⟩, -, hz⟩ := P
      obtain ⟨μ0, ⟨hμ00, -, -⟩, -, hz0⟩ := P0
      apply Subtype.ext
      funext i
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · exact hμ0.trans hμ00.symm
      · exact (hz i hi).trans (hz0 i hi).symm
    haveI : Unique (A1.Idx n isVec B 0 0) := ⟨⟨P0⟩, hall⟩
    have hcan : ∀ c : ℤ, canIdx (0 : Fin n → ℤ) c = ∅ := by
      intro c
      unfold Formalism.InvariantFactorPaths.GelfandTsetlinBases.canIdx
      by_cases hc : 1 ≤ c
      · rw [if_pos hc, Finset.filter_eq_empty_iff]
        intro m _ hm
        have h0 : colHeight (0 : Fin n → ℤ) c = 0 := by
          unfold Formalism.InvariantFactorPaths.GelfandTsetlinBases.colHeight
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro x _ hx
          have : c ≤ 0 := hx
          omega
        omega
      · rw [if_neg hc, Finset.filter_eq_empty_iff]
        intro m _ hm
        have hn : colHeight (0 : Fin n → ℤ) c = n := by
          unfold Formalism.InvariantFactorPaths.GelfandTsetlinBases.colHeight
          have hc0 : c ≤ 0 := by omega
          simp [hc0]
        have := m.isLt
        omega
    have hone : psiPath k isVec P0.1 0 (canIdx (0 : Fin n → ℤ)) = 1 := by
      unfold Formalism.InvariantFactorPaths.GelfandTsetlinBases.psiPath
      refine (finprod_congr fun c => ?_).trans finprod_one
      rw [hcan c]
      show (if (∅ : Finset (Fin n)) = ∅ then (1 : MvPolynomial (ℕ × Fin n) k) else 0) = 1
      rw [if_pos rfl]
    refine linearIndependent_unique_iff.mpr ?_
    show psiPath k isVec P0.1 0 (canIdx (0 : Fin n → ℤ)) ≠ 0
    rw [hone]
    exact one_ne_zero
  | succ N ih =>
    refine A1.li_of_lead (k := k) (fun P : A1.Idx n isVec B (N + 1) ν => psiPath k isVec P.1 (N + 1) (canIdx ν))
      (fun P : A1.Idx n isVec B (N + 1) ν => A1.rho n N (isVec N) (A1.DD P.1 N))
      (fun γ => weightedHomogeneousComponent (A1.wt n N (isVec N)) γ) ?_ ?_
    · intro P γ hγ
      obtain ⟨ε, -, hL⟩ := A1.psi_lead k P.2.1
      have h := hL.comp_eq_zero hγ
      rw [P.2.2.1] at h
      exact h
    · intro γ
      show LinearIndependent k (fun Q : {P : A1.Idx n isVec B (N + 1) ν // A1.rho n N (isVec N) (A1.DD P.1 N) = γ} =>
        weightedHomogeneousComponent (A1.wt n N (isVec N)) γ (psiPath k isVec Q.1.1 (N + 1) (canIdx ν)))
      by_cases hne : Nonempty {P : A1.Idx n isVec B (N + 1) ν // A1.rho n N (isVec N) (A1.DD P.1 N) = γ}
      swap
      · haveI := not_nonempty_iff.mp hne
        exact linearIndependent_empty_type
      obtain ⟨Q0⟩ := hne
      have hend : ∀ Q : {P : A1.Idx n isVec B (N + 1) ν // A1.rho n N (isVec N) (A1.DD P.1 N) = γ},
          Q.1.1 N = Q0.1.1 N := fun Q =>
        A1.end_determined Q.1.2.1 Q0.1.2.1 (Q.1.2.2.1.trans Q0.1.2.2.1.symm) (isVec N) (Q.2.trans Q0.2.symm)
      have hDD : ∀ Q : {P : A1.Idx n isVec B (N + 1) ν // A1.rho n N (isVec N) (A1.DD P.1 N) = γ},
          A1.DD Q.1.1 N = A1.DD Q0.1.1 N := by
        intro Q
        unfold Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1.DD
        rw [hend Q, Q.1.2.2.1, Q0.1.2.2.1]
      choose u hu using fun Q : {P : A1.Idx n isVec B (N + 1) ν // A1.rho n N (isVec N) (A1.DD P.1 N) = γ} =>
        A1.psi_lead_unit k Q.1.2.1
      have hfam : (fun Q : {P : A1.Idx n isVec B (N + 1) ν // A1.rho n N (isVec N) (A1.DD P.1 N) = γ} =>
          weightedHomogeneousComponent (A1.wt n N (isVec N)) γ (psiPath k isVec Q.1.1 (N + 1) (canIdx ν))) =
          fun Q => u Q • (psiPath k isVec Q.1.1 N (canIdx (Q0.1.1 N)) * monomial (A1.DD Q0.1.1 N) (1 : k)) := by
        funext Q
        have h := hu Q
        rw [Q.2, Q.1.2.2.1, hend Q, hDD Q] at h
        exact h
      let tr : {P : A1.Idx n isVec B (N + 1) ν // A1.rho n N (isVec N) (A1.DD P.1 N) = γ} →
          A1.Idx n isVec B N (Q0.1.1 N) := fun Q =>
        ⟨fun i => if i ≤ N then Q.1.1 i else 0,
          A1.isPath_congr (fun i hi => by simp [hi]) (A1.isPath_trunc Q.1.2.1),
          show (if N ≤ N then Q.1.1 N else 0) = Q0.1.1 N by rw [if_pos le_rfl]; exact hend Q,
          fun i hi => show (if i ≤ N then Q.1.1 i else 0) = 0 from if_neg (by omega)⟩
      have htr : Function.Injective tr := by
        intro Q Q' h
        have h' : ∀ i, i ≤ N → Q.1.1 i = Q'.1.1 i := by
          intro i hi
          have h2 : (if i ≤ N then Q.1.1 i else 0) = (if i ≤ N then Q'.1.1 i else 0) :=
            congrFun (congrArg Subtype.val h) i
          rwa [if_pos hi, if_pos hi] at h2
        apply Subtype.ext
        apply Subtype.ext
        funext i
        rcases lt_trichotomy i (N + 1) with hi | hi | hi
        · exact h' i (by omega)
        · subst hi
          rw [Q.1.2.2.1, Q'.1.2.2.1]
        · rw [Q.1.2.2.2 i hi, Q'.1.2.2.2 i hi]
      have hbase0 : LinearIndependent k
          (fun Q : {P : A1.Idx n isVec B (N + 1) ν // A1.rho n N (isVec N) (A1.DD P.1 N) = γ} =>
            psiPath k isVec Q.1.1 N (canIdx (Q0.1.1 N))) := by
        have h1 := (ih (Q0.1.1 N)).comp tr htr
        have e : (fun Q : {P : A1.Idx n isVec B (N + 1) ν // A1.rho n N (isVec N) (A1.DD P.1 N) = γ} =>
            psiPath k isVec Q.1.1 N (canIdx (Q0.1.1 N))) =
            (fun P : A1.Idx n isVec B N (Q0.1.1 N) => psiPath k isVec P.1 N (canIdx (Q0.1.1 N))) ∘ tr := by
          funext Q
          show psiPath k isVec Q.1.1 N (canIdx (Q0.1.1 N)) = psiPath k isVec (tr Q).1 N (canIdx (Q0.1.1 N))
          exact A1.psiPath_congr k isVec
            (fun i hi => by show Q.1.1 i = if i ≤ N then Q.1.1 i else 0; rw [if_pos hi]) _
        rw [e]
        exact h1
      have hM : (monomial (A1.DD Q0.1.1 N) (1 : k) : MvPolynomial (ℕ × Fin n) k) ≠ 0 := by
        rw [Ne, MvPolynomial.monomial_eq_zero]
        exact one_ne_zero
      have hbase1 := hbase0.map' (LinearMap.mulRight k (monomial (A1.DD Q0.1.1 N) (1 : k) : MvPolynomial (ℕ × Fin n) k))
        (LinearMap.ker_eq_bot.mpr (by
          intro a b hab
          simp only [LinearMap.mulRight_apply] at hab
          exact mul_right_cancel₀ hM hab))
      have e2 : (⇑(LinearMap.mulRight k (monomial (A1.DD Q0.1.1 N) (1 : k) : MvPolynomial (ℕ × Fin n) k)) ∘
          fun Q : {P : A1.Idx n isVec B (N + 1) ν // A1.rho n N (isVec N) (A1.DD P.1 N) = γ} =>
            psiPath k isVec Q.1.1 N (canIdx (Q0.1.1 N))) =
          fun Q => psiPath k isVec Q.1.1 N (canIdx (Q0.1.1 N)) * monomial (A1.DD Q0.1.1 N) (1 : k) := by
        funext Q
        simp only [Function.comp_apply, LinearMap.mulRight_apply]
      rw [e2] at hbase1
      rw [hfam]
      exact hbase1.units_smul u
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
