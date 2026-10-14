-- Prove2me | solution 1 for ChoiceRM.MNL.proposition_6
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T02:10:26.871122+00:00
-- url     : https://prove2.me/submissions/290c4ee7-be1e-4a11-8604-ea61cea9ea91

import Theorems.Thm_ChoiceRM_MNL_mnl_purchaseProb_mono
import Theorems.Thm_ChoiceRM_MNL_exists_kstar_theta
import Theorems.Thm_ChoiceRM_MNL_mix_ge_below_kstar
import Theorems.Thm_ChoiceRM_MNL_mix_partial_sums_above_kstar
import Theorems.Thm_ChoiceRM_MNL_theorem_2_sufficiency


import Definitions.Def_ChoiceRM_MNL_Models

open ChoiceRM.MNL RevenueManagement
open scoped BigOperators

private lemma weight_nonneg {n : ℕ} (w : Fin n → ℝ) (hw : ∀ j, 0 < w j)
    (S : Finset (Fin n)) : 0 ≤ ∑ i ∈ S, w i :=
  Finset.sum_nonneg fun i _ => (hw i).le

private lemma probability_sum {n : ℕ} (w : Fin n → ℝ) (S : Finset (Fin n)) :
    purchaseProb (mnl w) S = (∑ i ∈ S, w i) / ((∑ i ∈ S, w i) + 1) := by
  simp only [purchaseProb, mnl]
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun i hi => if_pos hi

private lemma probability_total {n : ℕ} (w : Fin n → ℝ) (S : Finset (Fin n)) :
    ∑ j, mnl w S j = (∑ i ∈ S, w i) / ((∑ i ∈ S, w i) + 1) := by
  simp only [mnl]
  simp [← Finset.sum_div]

private lemma complete_mem {n k : ℕ} {j : Fin n} : j ∈ complete n k ↔ j.val < k := by
  simp [complete]

private lemma complete_zero (n : ℕ) : complete n 0 = ∅ := by
  simp [complete]

private lemma complete_all (n : ℕ) : complete n n = Finset.univ := by
  ext j
  simp [complete, j.isLt]

private lemma complete_subset {n a b : ℕ} (hab : a ≤ b) : complete n a ⊆ complete n b := by
  intro j hj
  exact complete_mem.mpr (lt_of_lt_of_le (complete_mem.mp hj) hab)

private lemma ratio_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    a / (a + 1) ≤ b / (b + 1) := by
  apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
  nlinarith

private lemma ratio_strict {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    a / (a + 1) < b / (b + 1) := by
  apply (div_lt_div_iff₀ (by linarith) (by linarith)).mpr
  nlinarith

private lemma reciprocal_mixture (y₁ y₂ y₃ θ : ℝ)
    (h0 : 0 ≤ y₁) (h12 : y₁ ≤ y₂) (h23 : y₂ ≤ y₃)
    (h : θ * (y₁ / (y₁ + 1)) + (1 - θ) * (y₃ / (y₃ + 1)) = y₂ / (y₂ + 1)) :
    θ * (1 / (y₁ + 1)) + (1 - θ) * (1 / (y₃ + 1)) = 1 / (y₂ + 1) := by
  have hid (y : ℝ) (hy : 0 ≤ y) : 1 / (y + 1) = 1 - y / (y + 1) := by
    field_simp
    <;> linarith
  rw [hid y₁ h0, hid y₂ (by linarith), hid y₃ (by linarith)]
  nlinarith [h]

private lemma twoPoint_sum {n : ℕ} (k : ℕ) (hk : k < n) (θ : ℝ)
    (f : Fin (n + 1) → ℝ) :
    ∑ l, twoPoint k θ l * f l =
      θ * f ⟨k, by omega⟩ + (1 - θ) * f ⟨k + 1, by omega⟩ := by
  classical
  let k0 : Fin (n + 1) := ⟨k, by omega⟩
  let k1 : Fin (n + 1) := ⟨k + 1, by omega⟩
  have hne : k0 ≠ k1 := by intro h; have := congrArg Fin.val h; dsimp [k0, k1] at this; omega
  have he (l : Fin (n + 1)) : twoPoint k θ l * f l =
      (if l = k0 then θ * f k0 else 0) +
      (if l = k1 then (1 - θ) * f k1 else 0) := by
    by_cases h0 : l = k0
    · subst l
      simp [twoPoint, k0, hne]
    · by_cases h1 : l = k1
      · subst l
        simp [twoPoint, k1, h0, show k + 1 ≠ k by omega]
      · have hv0 : l.val ≠ k := fun h => h0 (Fin.ext h)
        have hv1 : l.val ≠ k + 1 := fun h => h1 (Fin.ext h)
        simp [twoPoint, hv0, hv1, h0, h1]
  simp_rw [he, Finset.sum_add_distrib]
  simp [k0, k1]

private lemma mix_twoPoint {n : ℕ} (P : Finset (Fin n) → Fin n → ℝ)
    (k : ℕ) (hk : k < n) (θ : ℝ) (j : Fin n) :
    mixProb P (twoPoint k θ) j =
      θ * P (complete n k) j + (1 - θ) * P (complete n (k + 1)) j := by
  exact twoPoint_sum k hk θ (fun l => P (complete n l.val) j)

private lemma probability_nonneg {n : ℕ} (w : Fin n → ℝ) (hw : ∀ j, 0 < w j)
    (S : Finset (Fin n)) (j : Fin n) : 0 ≤ mnl w S j := by
  unfold mnl
  split_ifs
  · exact div_nonneg (hw j).le (by linarith [weight_nonneg w hw S])
  · rfl

private lemma probability_partial_total {n : ℕ} (w : Fin n → ℝ)
    (A B : Finset (Fin n)) (hAB : A ⊆ B) :
    ∑ j ∈ B, mnl w A j = (∑ i ∈ A, w i) / ((∑ i ∈ A, w i) + 1) := by
  rw [← probability_sum]
  unfold purchaseProb
  symm
  apply Finset.sum_subset hAB
  intro j hj hjA
  simp [mnl, hjA]





/-- Proposition 6, p. 23, in the form its proof establishes (pp. 24–25): the MNL choice model (14)
with positive weights has the nesting-by-fare-order property of Definition 4. -/
theorem solution {n : ℕ} (w : Fin n → ℝ) (hw : ∀ j, 0 < w j) :
    HasFareOrderNesting (mnl w) := by
  classical
  have hchoice : IsChoiceModel (mnl w) := by
    refine ⟨probability_nonneg w hw, ?_⟩
    intro S
    change purchaseProb (mnl w) S ≤ 1
    rw [probability_sum]
    exact (div_le_one (by linarith [weight_nonneg w hw S])).mpr (by linarith)
  have hsupp : SupportedOn (mnl w) := by
    intro S j hj
    simp [mnl, hj]
  apply ChoiceRM.MNL.theorem_2_sufficiency (mnl w) hchoice hsupp
    (mnl_purchaseProb_mono w hw)
  intro T hT
  obtain ⟨k, hk, hlo, hhi, hj, θ, hθ0, hθ1, h15⟩ := exists_kstar_theta w hw T hT
  have habove := mix_partial_sums_above_kstar w hw T k hk hlo hhi θ hθ0 hθ1 h15
  refine ⟨twoPoint k θ, ?_, ?_, ?_, ?_⟩
  · intro l
    unfold twoPoint
    split_ifs <;> linarith
  · have hs := twoPoint_sum k hk θ (fun _ : Fin (n + 1) => (1 : ℝ))
    simpa using hs
  · intro i hi
    by_cases hik : i ≤ k
    · apply Finset.sum_le_sum
      intro j hji
      have hjk : j.val < k := lt_of_lt_of_le (complete_mem.mp hji) hik
      have hb := mix_ge_below_kstar w hw T k hk hlo hhi θ hθ0 hθ1 h15 j hjk
      exact hb.2.trans_eq hb.1.symm
    · have ha := habove.1 i (by omega) hi.le
      exact ha.2.trans_eq ha.1.symm
  · have ha := habove.1 n hk le_rfl
    simpa [complete_all] using ha.1.trans habove.2.symm


