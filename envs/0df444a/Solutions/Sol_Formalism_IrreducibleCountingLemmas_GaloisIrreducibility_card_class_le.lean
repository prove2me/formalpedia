-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.card_class_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:06:10.872565+00:00
-- url     : https://prove2.me/submissions/35ea7128-1f88-4197-9698-1aaa16a28d41

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRBBCard
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRBBDivides
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRExcludedCount
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_zero
import Theorems.Thm_P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_zero
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_zero
attribute [local simp] P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8



set_option autoImplicit false
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution (S : Finset ℕ) (Y : ℝ) (M r : ℕ) (hM : 0 < M) (hY : 0 ≤ Y)
    (hS : ∀ g ∈ S, Y ≤ (g : ℝ) ∧ (g : ℝ) ≤ 2 * Y ∧ g % M = r) :
    (S.card : ℝ) ≤ Y / M + 1 := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp only [Finset.card_empty, Nat.cast_zero]; positivity
  set g0 := S.min' hne with hg0def
  have hg0 : g0 ∈ S := S.min'_mem hne
  have hdvd : ∀ a ∈ S, g0 ≤ a ∧ M ∣ a - g0 := by
    intro a ha
    have ha0 : g0 ≤ a := S.min'_le a ha
    refine ⟨ha0, (Nat.modEq_iff_dvd' ha0).mp ?_⟩
    unfold Nat.ModEq
    rw [(hS g0 hg0).2.2, (hS a ha).2.2]
  have hinj : Set.InjOn (fun g => (g - g0) / M) (S : Set ℕ) := by
    intro a ha b hb hab
    obtain ⟨ha0, s, hs⟩ := hdvd a ha
    obtain ⟨hb0, t, ht⟩ := hdvd b hb
    simp only at hab
    rw [hs, ht, Nat.mul_div_cancel_left _ hM, Nat.mul_div_cancel_left _ hM] at hab
    subst hab
    omega
  have himg : S.image (fun g => (g - g0) / M) ⊆ Finset.range (⌊Y / M⌋₊ + 1) := by
    intro k hk
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hk
    rw [Finset.mem_range, Nat.lt_succ_iff]
    apply Nat.le_floor
    have ha0 : g0 ≤ a := (hdvd a ha).1
    have h1 : (((a - g0) / M : ℕ) : ℝ) ≤ ((a - g0 : ℕ) : ℝ) / M := Nat.cast_div_le
    have h2 : ((a - g0 : ℕ) : ℝ) = (a : ℝ) - g0 := Nat.cast_sub ha0
    have h3 : (a : ℝ) - g0 ≤ Y := by linarith [(hS a ha).2.1, (hS g0 hg0).1]
    have hM' : (0 : ℝ) < M := by exact_mod_cast hM
    calc (((a - g0) / M : ℕ) : ℝ) ≤ ((a - g0 : ℕ) : ℝ) / M := h1
      _ ≤ Y / M := by rw [h2]; exact div_le_div_of_nonneg_right h3 hM'.le
  have hc : S.card ≤ ⌊Y / M⌋₊ + 1 := by
    rw [← Finset.card_image_of_injOn hinj]
    simpa using Finset.card_le_card himg
  have hfl : ((⌊Y / M⌋₊ : ℕ) : ℝ) ≤ Y / M := Nat.floor_le (by positivity)
  calc (S.card : ℝ) ≤ ((⌊Y / M⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast hc
    _ ≤ Y / M + 1 := by push_cast; linarith
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
