-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.schur_two_factor_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:35:57.083522+00:00
-- url     : https://prove2.me/submissions/cba3b588-bb24-4d2b-b271-3abdcca11bf0

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RowNormSquareBounds
import Theorems.Thm_Formalism_FourierDecayAlt_P_SchurNormSquareBounds_norm_sq_sum_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_SchurNormSquareBounds_row_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset SchurNormSquareBounds
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.F7.SchurTwo := by
  classical
  intro H _ _ G _ La ι PP _ T τ V P φ a b ε hinj hco hφ hS hab hV
  refine (norm_sq_sum_le T V).trans (add_le_add le_rfl ?_)

  have step1 : ∑ t ∈ T, ∑ t' ∈ T.erase t, ‖inner ℂ (V t) (V t')‖ ≤
      ∑ t ∈ T, ∑ t' ∈ T.erase t, ∑ p, φ p (τ t - τ t') * ((a p t + b p t') / 2) := by
    refine sum_le_sum fun t ht => sum_le_sum fun t' ht' => ?_
    obtain ⟨hne, ht'T⟩ := mem_erase.1 ht'
    refine (hV t ht t' ht'T (Ne.symm hne)).trans ?_
    refine single_le_sum (f := fun p => φ p (τ t - τ t') * ((a p t + b p t') / 2))
      (fun p _ => ?_) (mem_univ (P t t'))
    have h1 := hφ p _ (hco t ht t' ht'T)
    have h2 := (hab p t ht).1
    have h3 := (hab p t' ht'T).2
    positivity
  refine step1.trans ?_
  have step2 : ∑ t ∈ T, ∑ t' ∈ T.erase t, ∑ p, φ p (τ t - τ t') * ((a p t + b p t') / 2) =
      ∑ p, ((∑ t ∈ T, a p t / 2 * ∑ t' ∈ T.erase t, φ p (τ t - τ t')) +
        ∑ t' ∈ T, b p t' / 2 * ∑ t ∈ T.erase t', φ p (τ t - τ t')) := by
    have e1 : ∀ p, ∑ t' ∈ T, b p t' / 2 * ∑ t ∈ T.erase t', φ p (τ t - τ t') =
        ∑ t ∈ T, ∑ t' ∈ T.erase t, b p t' / 2 * φ p (τ t - τ t') := by
      intro p
      simp only [mul_sum]
      refine sum_comm' ?_
      intro x y
      simp only [mem_erase]
      constructor
      · rintro ⟨hx, hne, hy⟩; exact ⟨⟨hne.symm, hx⟩, hy⟩
      · rintro ⟨⟨hne, hx⟩, hy⟩; exact ⟨hx, hne.symm, hy⟩
    simp only [e1]
    simp only [mul_sum, ← sum_add_distrib]
    rw [sum_comm]
    refine sum_congr rfl fun t _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun t' _ => sum_congr rfl fun p _ => ?_
    ring
  rw [step2, mul_sum]
  refine sum_le_sum fun p _ => ?_
  have hA : ∑ t ∈ T, a p t / 2 * ∑ t' ∈ T.erase t, φ p (τ t - τ t') ≤ ∑ t ∈ T, a p t / 2 * ε :=
    sum_le_sum fun t ht => mul_le_mul_of_nonneg_left
      (row_le La T τ (φ p) ε hinj hco (hS p) t ht).1 (by have := (hab p t ht).1; positivity)
  have hB : ∑ t' ∈ T, b p t' / 2 * ∑ t ∈ T.erase t', φ p (τ t - τ t') ≤ ∑ t ∈ T, b p t / 2 * ε :=
    sum_le_sum fun t ht => mul_le_mul_of_nonneg_left
      (row_le La T τ (φ p) ε hinj hco (hS p) t ht).2 (by have := (hab p t ht).2; positivity)
  refine (add_le_add hA hB).trans (le_of_eq ?_)
  rw [← sum_add_distrib, mul_sum]
  exact sum_congr rfl fun t _ => by ring
end Formalism.FourierDecayAlt.P
