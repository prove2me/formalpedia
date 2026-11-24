-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.initMinor_support
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:16:00.158962+00:00
-- url     : https://prove2.me/submissions/768cdcb4-c3c1-4bdf-a830-2aa4dc2f2934

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetdomLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_initMinor_term_support

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {R : Type*} [CommRing R] {r n s : ℕ} (I : Fin s → Fin r) (hs : s ≤ n)
    (m : Fin r × Fin n →₀ ℕ) (hm : m ∈ (initMinor R I hs).support) :
    (∀ k, rowPart k m ≤ min k s) ∧ rowTot m = s := by
  classical
  by_cases hI : Function.Injective I
  · unfold initMinor at hm
    rw [Matrix.det_apply] at hm
    have h1 := support_sum hm
    rw [Finset.mem_biUnion] at h1
    obtain ⟨σ, -, hσ⟩ := h1
    rw [Units.smul_def] at hσ
    have hσ' := support_smul hσ
    simp only [Matrix.of_apply] at hσ'
    obtain ⟨hp, ht⟩ := initMinor_term_support I hs σ m hσ'
    refine ⟨fun k => ?_, ht⟩
    rw [hp k]
    refine le_min ?_ ?_
    · calc #{p : Fin s | (I p).val < k} ≤ #{a : Fin r | a.val < k} := by
            apply Finset.card_le_card_of_injOn I
            · intro p hp'
              simp only [Finset.coe_filter, Finset.mem_univ, true_and] at hp' ⊢
              exact hp'
            · intro p _ q _ h; exact hI h
        _ = min r k := Fin.card_filter_val_lt
        _ ≤ k := min_le_right _ _
    · calc #{p : Fin s | (I p).val < k} ≤ #(Finset.univ : Finset (Fin s)) := Finset.card_filter_le _ _
        _ = s := by simp
  · exfalso
    simp only [Function.Injective, not_forall] at hI
    obtain ⟨p, q, hpq, hne⟩ := hI
    have h0 : initMinor R I hs = 0 := by
      unfold initMinor
      apply Matrix.det_zero_of_row_eq hne
      funext j
      simp [hpq]
    rw [h0, support_zero] at hm
    exact Finset.notMem_empty _ hm
end Formalism.GradedWeylDivisibility
