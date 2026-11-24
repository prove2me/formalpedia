-- Prove2me | solution 1 for FairSelling.EqualProceedsBagFilling.bagFilling_induction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:39:45.841956+00:00
-- url     : https://prove2.me/submissions/48906250-35dc-411f-b950-9d6b1627253a

import Mathlib
import Definitions.Def_RequestProject_EqualProceeds
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_EqualProceedsBagFilling
import Theorems.Thm_FairSelling_EqualProceedsBagFilling_priceSum_nonneg
import Theorems.Thm_FairSelling_EqualProceedsBagFilling_round_exists

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.EqualProceedsBagFilling
variable {G : Type*} {n : ℕ}
variable {vi p : G → ℝ} {tk : ℝ}
variable [DecidableEq G] (v : Fin n → G → ℝ) (p : G → ℝ) (t : Fin n → ℝ)
namespace FairSelling.EqualProceedsBagFilling
theorem _root_.solution
    (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g) (ht : ∀ i, 0 ≤ t i) (hn : 0 < n) :
    ∀ (T : Finset (Fin n)) (R : Finset G) (s : ℝ), 0 ≤ s →
      (∀ k ∈ T, (T.card : ℝ) * t k ≤ effSum (v k) p (t k) R + n * s) →
      ∃ (C : Fin n → Finset G) (D : Finset G),
        (∀ k, C k ⊆ R) ∧ D ⊆ R ∧
        (∀ j k, j ≠ k → Disjoint (C j) (C k)) ∧ (∀ k, Disjoint (C k) D) ∧
        ∀ k ∈ T, t k / n ≤ (∑ g ∈ C k, v k g) + s + priceSum p D / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  intro T
  induction T using Finset.strongInduction with
  | _ T ih =>
    intro R s hs hinv
    rcases Finset.eq_empty_or_nonempty T with rfl | hT
    · exact ⟨fun _ => ∅, ∅, by simp, by simp, by simp, by simp, by simp⟩
    · have hcard1 : (1 : ℝ) ≤ (T.card : ℝ) := by
        exact_mod_cast Finset.card_pos.mpr hT
      have hinv' : ∀ k ∈ T, t k ≤ effSum (v k) p (t k) R + (n : ℝ) * s := by
        intro k hk
        have h := hinv k hk
        nlinarith [ht k]
      obtain ⟨i, hiT, C0, D0, hC0R, hD0R, hdisj0, hisat, hloss⟩ :=
        round_exists v p t hv hp ht hn R s hs T hT hinv'
      have hsubR : C0 ∪ D0 ⊆ R := Finset.union_subset hC0R hD0R
      have hdisjR : Disjoint (R \ (C0 ∪ D0)) (C0 ∪ D0) := Finset.sdiff_disjoint
      have hpD0 : 0 ≤ priceSum p D0 := priceSum_nonneg hp _
      have hs' : (0 : ℝ) ≤ s + priceSum p D0 / n := by positivity
      have hinv2 : ∀ k ∈ T.erase i,
          (((T.erase i).card : ℝ)) * t k
            ≤ effSum (v k) p (t k) (R \ (C0 ∪ D0)) + (n : ℝ) * (s + priceSum p D0 / n) := by
        intro k hk
        have hkT : k ∈ T := Finset.mem_of_mem_erase hk
        have hki : k ≠ i := Finset.ne_of_mem_erase hk
        have hsplit : effSum (v k) p (t k) (R \ (C0 ∪ D0))
            = effSum (v k) p (t k) R - effSum (v k) p (t k) (C0 ∪ D0) := by
          unfold effSum
          exact Finset.sum_sdiff_eq_sub hsubR
        have hcard : ((T.erase i).card : ℝ) = (T.card : ℝ) - 1 := by
          rw [Finset.card_erase_of_mem hiT]
          have : 1 ≤ T.card := Finset.card_pos.mpr hT
          push_cast [Nat.cast_sub this]
          ring
        have hmoney : (n : ℝ) * (s + priceSum p D0 / n)
            = (n : ℝ) * s + priceSum p D0 := by
          field_simp
        have hl := hloss k hkT hki
        have h := hinv k hkT
        rw [hsplit, hcard, hmoney]
        nlinarith
      obtain ⟨C1, D1, hC1R, hD1R, hC1disj, hC1D1, hsat1⟩ :=
        ih (T.erase i) (Finset.erase_ssubset hiT) (R \ (C0 ∪ D0)) (s + priceSum p D0 / n) hs'
          hinv2
      have hR'sub : R \ (C0 ∪ D0) ⊆ R := Finset.sdiff_subset
      have hC1disjC0 : ∀ k, Disjoint (C1 k) C0 := fun k =>
        (hdisjR.mono (hC1R k) Finset.subset_union_left)
      have hC1disjD0 : ∀ k, Disjoint (C1 k) D0 := fun k =>
        (hdisjR.mono (hC1R k) Finset.subset_union_right)
      have hD1disjC0 : Disjoint D1 C0 := hdisjR.mono hD1R Finset.subset_union_left
      have hD1disjD0 : Disjoint D1 D0 := hdisjR.mono hD1R Finset.subset_union_right
      have hpD : priceSum p (D0 ∪ D1) = priceSum p D0 + priceSum p D1 := by
        unfold priceSum
        exact Finset.sum_union hD1disjD0.symm
      have hpD1 : 0 ≤ priceSum p D1 := priceSum_nonneg hp _
      refine ⟨Function.update C1 i C0, D0 ∪ D1, ?_, ?_, ?_, ?_, ?_⟩
      · intro k
        by_cases hk : k = i
        · subst hk
          simp only [Function.update_self]
          exact hC0R
        · simp only [Function.update_of_ne hk]
          exact (hC1R k).trans hR'sub
      · exact Finset.union_subset hD0R (hD1R.trans hR'sub)
      · intro j k hjk
        by_cases hj : j = i
        · subst hj
          have hk : k ≠ j := fun h => hjk h.symm
          simp only [Function.update_of_ne hk, Function.update_self]
          exact (hC1disjC0 k).symm
        · by_cases hk : k = i
          · subst hk
            simp only [Function.update_of_ne hj, Function.update_self]
            exact hC1disjC0 j
          · simp only [Function.update_of_ne hj, Function.update_of_ne hk]
            exact hC1disj j k hjk
      · intro k
        by_cases hk : k = i
        · subst hk
          simp only [Function.update_self]
          exact Finset.disjoint_union_right.mpr ⟨hdisj0, hD1disjC0.symm⟩
        · simp only [Function.update_of_ne hk]
          exact Finset.disjoint_union_right.mpr ⟨hC1disjD0 k, hC1D1 k⟩
      · intro k hk
        by_cases hki : k = i
        · subst hki
          simp only [Function.update_self, hpD]
          have : priceSum p D1 / n ≥ 0 := by positivity
          rw [add_div]
          linarith
        · have hke : k ∈ T.erase i := Finset.mem_erase.mpr ⟨hki, hk⟩
          have := hsat1 k hke
          simp only [Function.update_of_ne hki, hpD]
          rw [add_div]
          linarith
end FairSelling.EqualProceedsBagFilling
