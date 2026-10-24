-- Prove2me | solution 1 for FirstPriceLearning.Adversarial.lemma_16
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T05:54:07.865345+00:00
-- url     : https://prove2.me/submissions/b0024ff0-031b-4e07-b938-184114fb2e8e

import Mathlib
import Definitions.Def_FirstPriceLearning_Adversarial_Model
import Definitions.Def_FirstPriceLearning_Adversarial_MLISUCB

open MeasureTheory

namespace FPA2L16

/-- If every `t ∈ S` has `f t ≥ N0 + #{s ∈ S : s < t}` with `N0 ≥ 1`, then
`∑_{t ∈ S} 1 / f t ≤ ∑_{a < |S|} 1 / (a + 1)`. -/
theorem sum_inv_le_harmonic (S : Finset ℕ) (N0 : ℕ) (hN0 : 1 ≤ N0) (f : ℕ → ℝ)
    (hf : ∀ t ∈ S, ((N0 : ℝ) + ((S.filter (fun s => s < t)).card : ℝ)) ≤ f t) :
    ∑ t ∈ S, 1 / f t ≤ ∑ a ∈ Finset.range S.card, 1 / ((a : ℝ) + 1) := by
  induction S using Finset.induction_on_max generalizing f with
  | empty => simp
  | insert a s ha ih =>
    have hnot : a ∉ s := fun h => lt_irrefl a (ha a h)
    rw [Finset.sum_insert hnot, Finset.card_insert_of_notMem hnot, Finset.sum_range_succ]
    have h1 : ∑ t ∈ s, 1 / f t ≤ ∑ a ∈ Finset.range s.card, 1 / ((a : ℝ) + 1) := by
      apply ih f
      intro t ht
      have := hf t (Finset.mem_insert_of_mem ht)
      have heq : (insert a s).filter (fun s => s < t) = s.filter (fun s => s < t) := by
        rw [Finset.filter_insert]
        have : ¬ a < t := not_lt.mpr (le_of_lt (ha t ht))
        simp [this]
      rw [heq] at this
      exact this
    have h2 : 1 / f a ≤ 1 / ((s.card : ℝ) + 1) := by
      have := hf a (Finset.mem_insert_self a s)
      have heq : (insert a s).filter (fun s => s < a) = s := by
        rw [Finset.filter_insert]
        simp only [lt_irrefl, if_false]
        exact Finset.filter_true_of_mem (fun x hx => ha x hx)
      rw [heq] at this
      have hN : (1 : ℝ) ≤ N0 := by exact_mod_cast hN0
      apply one_div_le_one_div_of_le
      · positivity
      · linarith
    linarith

theorem harmonic_sum_le (k T : ℕ) (hk : k ≤ T) :
    ∑ a ∈ Finset.range k, 1 / ((a : ℝ) + 1) ≤ 1 + Real.log T := by
  have h1 : ∑ a ∈ Finset.range k, 1 / ((a : ℝ) + 1) ≤ ∑ a ∈ Finset.range T, 1 / ((a : ℝ) + 1) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.range_subset_range.mpr hk
    · intro i _ _; positivity
  have h2 : ∑ a ∈ Finset.range T, 1 / ((a : ℝ) + 1) = (harmonic T : ℝ) := by
    rw [harmonic]; push_cast
    apply Finset.sum_congr rfl; intro i _; rw [one_div]
  have h3 := harmonic_le_one_add_log T
  linarith

end FPA2L16

open FPA2L16 in
theorem solution (T K T₀ : ℕ) (Φ : Finset ℕ) (hΦ : Φ ⊆ Finset.Icc 1 T) (idx : ℕ → ℕ)
    (hidx : ∀ t ∈ Φ, idx t < K)
    (hinit : FirstPriceLearning.Adversarial.numGrid T ≤
      (Φ.filter (fun r => r ≤ T₀ ∧ idx r = 0)).card)
    (w : ℕ → ℝ) (hw : ∀ j < K, 0 ≤ w j) (s : ℝ) (hs : ∑ j ∈ Finset.range K, w j = s) :
    (∑ t ∈ Φ.filter (fun t => T₀ < t), ∑ j ∈ Finset.Ico (idx t) K,
        w j / (FirstPriceLearning.Adversarial.obsCount K Φ idx j t : ℝ) ≤ s * (1 + Real.log T)) ∧
    (∑ t ∈ Φ.filter (fun t => T₀ < t),
        1 / (FirstPriceLearning.Adversarial.obsCount K Φ idx (idx t) t : ℝ)
        ≤ (K : ℝ) * (1 + Real.log T)) := by
  classical
  -- general statement for an arbitrary nonnegative weight vector
  have main : ∀ (w : ℕ → ℝ), (∀ j < K, 0 ≤ w j) →
      ∑ t ∈ Φ.filter (fun t => T₀ < t), ∑ j ∈ Finset.Ico (idx t) K,
        w j / (FirstPriceLearning.Adversarial.obsCount K Φ idx j t : ℝ)
        ≤ (∑ j ∈ Finset.range K, w j) * (1 + Real.log T) := by
    intro w hw
    rcases Nat.eq_zero_or_pos T with hT | hT
    · subst hT
      have : Φ = ∅ := by
        apply Finset.subset_empty.mp
        intro x hx; have := hΦ hx; simp at this
      subst this; simp
      exact Finset.sum_nonneg (fun j hj => hw j (Finset.mem_range.mp hj))
    have hK : 0 < K := by
      rcases Nat.eq_zero_or_pos K with h | h
      · -- then Φ is empty
        subst h
        have hΦe : Φ = ∅ := by
          apply Finset.eq_empty_of_forall_notMem
          intro x hx; have := hidx x hx; omega
        subst hΦe
        exfalso
        simp at hinit
        have : 1 ≤ FirstPriceLearning.Adversarial.numGrid T := by
          unfold FirstPriceLearning.Adversarial.numGrid
          apply Nat.one_le_iff_ne_zero.mpr
          intro h0
          rw [Nat.ceil_eq_zero] at h0
          have : 0 < Real.sqrt T := Real.sqrt_pos.mpr (by exact_mod_cast hT)
          linarith
        omega
      · exact h
    have hgrid : ∀ a j : ℕ, FirstPriceLearning.Adversarial.grid K a ≤
        FirstPriceLearning.Adversarial.grid K j ↔ a ≤ j := by
      intro a j
      unfold FirstPriceLearning.Adversarial.grid
      rw [div_le_div_iff_of_pos_right (by exact_mod_cast hK)]
      exact Nat.cast_le
    have hN0 : 1 ≤ FirstPriceLearning.Adversarial.numGrid T := by
      unfold FirstPriceLearning.Adversarial.numGrid
      apply Nat.one_le_iff_ne_zero.mpr
      intro h0
      rw [Nat.ceil_eq_zero] at h0
      have : 0 < Real.sqrt T := Real.sqrt_pos.mpr (by exact_mod_cast hT)
      linarith
    set F := Φ.filter (fun t => T₀ < t) with hF
    -- swap the sums
    have hswap : ∑ t ∈ F, ∑ j ∈ Finset.Ico (idx t) K,
        w j / (FirstPriceLearning.Adversarial.obsCount K Φ idx j t : ℝ)
        = ∑ j ∈ Finset.range K, ∑ t ∈ F.filter (fun t => idx t ≤ j),
          w j / (FirstPriceLearning.Adversarial.obsCount K Φ idx j t : ℝ) := by
      apply Finset.sum_comm'
      intro t j
      simp only [Finset.mem_Ico, Finset.mem_range, Finset.mem_filter, hF]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
      · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩; exact ⟨⟨h1, h2⟩, h3, h4⟩
    rw [hswap, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j hj
    rw [Finset.mem_range] at hj
    set S := F.filter (fun t => idx t ≤ j) with hS
    have hbound : ∀ t ∈ S, ((FirstPriceLearning.Adversarial.numGrid T : ℝ) +
        ((S.filter (fun s => s < t)).card : ℝ)) ≤
        (FirstPriceLearning.Adversarial.obsCount K Φ idx j t : ℝ) := by
      intro t ht
      have htS := ht
      simp only [hS, hF, Finset.mem_filter] at ht
      obtain ⟨⟨htΦ, htT⟩, htj⟩ := ht
      have hdisj : Disjoint (Φ.filter (fun r => r ≤ T₀ ∧ idx r = 0)) (S.filter (fun s => s < t)) := by
        rw [Finset.disjoint_left]
        intro x hx hx'
        simp only [hS, hF, Finset.mem_filter] at hx hx'
        omega
      have hsub : (Φ.filter (fun r => r ≤ T₀ ∧ idx r = 0)) ∪ (S.filter (fun s => s < t)) ⊆
          Φ.filter (fun s => s < t ∧ FirstPriceLearning.Adversarial.grid K (idx s) ≤
            FirstPriceLearning.Adversarial.grid K j) := by
        intro x hx
        rw [Finset.mem_union] at hx
        simp only [Finset.mem_filter, hgrid]
        rcases hx with hx | hx
        · simp only [Finset.mem_filter] at hx
          refine ⟨hx.1, by omega, by omega⟩
        · simp only [hS, hF, Finset.mem_filter] at hx
          refine ⟨hx.1.1.1, hx.2, hx.1.2⟩
      have hc := Finset.card_le_card hsub
      rw [Finset.card_union_of_disjoint hdisj] at hc
      unfold FirstPriceLearning.Adversarial.obsCount
      have : ((FirstPriceLearning.Adversarial.numGrid T : ℕ) + (S.filter (fun s => s < t)).card : ℕ)
          ≤ (Φ.filter (fun s => s < t ∧ FirstPriceLearning.Adversarial.grid K (idx s) ≤
            FirstPriceLearning.Adversarial.grid K j)).card := by omega
      exact_mod_cast this
    have hsum := sum_inv_le_harmonic S (FirstPriceLearning.Adversarial.numGrid T) hN0
      (fun t => (FirstPriceLearning.Adversarial.obsCount K Φ idx j t : ℝ)) hbound
    have hcard : S.card ≤ T := by
      have : S ⊆ Finset.Icc 1 T := fun x hx => hΦ (by
        simp only [hS, hF, Finset.mem_filter] at hx; exact hx.1.1)
      have := Finset.card_le_card this
      simpa using this
    have hh := harmonic_sum_le S.card T hcard
    have hwj := hw j hj
    calc ∑ t ∈ S, w j / (FirstPriceLearning.Adversarial.obsCount K Φ idx j t : ℝ)
        = w j * ∑ t ∈ S, 1 / (FirstPriceLearning.Adversarial.obsCount K Φ idx j t : ℝ) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro t _; ring
      _ ≤ w j * (1 + Real.log T) := by
          apply mul_le_mul_of_nonneg_left _ hwj
          exact le_trans hsum hh
  refine ⟨?_, ?_⟩
  · rw [← hs]; exact main w hw
  · have h1 := main (fun _ => 1) (fun _ _ => zero_le_one)
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at h1
    refine le_trans ?_ h1
    apply Finset.sum_le_sum
    intro t ht
    simp only [Finset.mem_filter] at ht
    have hlt := hidx t ht.1
    exact Finset.single_le_sum (f := fun x =>
        1 / (FirstPriceLearning.Adversarial.obsCount K Φ idx x t : ℝ))
      (fun i _ => by positivity) (by rw [Finset.mem_Ico]; exact ⟨le_refl _, hlt⟩)
