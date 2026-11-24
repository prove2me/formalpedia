-- Prove2me | solution 1 for Formalism.CohomologicalDescent.weightExchangeBound_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:32:56.763982+00:00
-- url     : https://prove2.me/submissions/7a83446c-f823-4cad-bf50-f218cbe35629

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_Statement
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WeightExchangeBoundHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent
open Classical
namespace Formalism.CohomologicalDescent
theorem _root_.solution : WEArith := by
  intro k j t q l h κ mw mwp U U' kc kp _ _ hU0 hU'h hsum htop hkc hkp
  have hlkp : (l : ℤ) * kp ≤ (l : ℤ) * ((mwp : ℤ) * ((t : ℤ) + 2 * κ)) :=
    mul_le_mul_of_nonneg_left ((le_abs_self kp).trans hkp) (by positivity)
  have hkc' : -kc ≤ (mw : ℤ) * ((t : ℤ) + 2 * κ) := (neg_le_abs kc).trans hkc
  have hq : ∑ a ∈ Finset.univ.filter
      (fun a : Fin (k + j + t + q) => k + j ≤ (a : ℕ) ∧ (a : ℕ) < k + j + q), (h : ℤ) ≤
      (q : ℤ) * h := by
    rw [Finset.sum_const, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have hc : (Finset.univ.filter
        (fun a : Fin (k + j + t + q) => k + j ≤ (a : ℕ) ∧ (a : ℕ) < k + j + q)).card ≤ q := by
      refine le_trans (Finset.card_le_card_of_injOn (fun a => (a : ℕ) - (k + j)) ?_ ?_)
        (Finset.card_range q).le
      · intro a ha
        simp at ha ⊢
        omega
      · intro a ha a' ha' hab
        simp at ha ha'
        have hab' : (a : ℕ) - (k + j) = (a' : ℕ) - (k + j) := hab
        exact Fin.ext (by omega)
    exact_mod_cast hc
  rw [Finset.sum_filter] at hq
  have hpt : ∀ a ∈ (Finset.univ : Finset (Fin (k + j + t + q))),
      (if (a : ℕ) < k + j then U a - U' a else 0) +
        (if k + j ≤ (a : ℕ) ∧ (a : ℕ) < k + j + t then U a else 0) ≤
      (if k + j ≤ (a : ℕ) ∧ (a : ℕ) < k + j + q then (h : ℤ) else 0) +
        (if k + j + q ≤ (a : ℕ) then U' a else 0) + (U a - U' a) := by
    intro a _
    have h1 := hU0 a
    have h2 := hU'h a
    split_ifs <;> omega
  have hsumle := Finset.sum_le_sum hpt
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hsumle
  simp only [Finset.sum_filter] at htop ⊢
  nlinarith
end Formalism.CohomologicalDescent
