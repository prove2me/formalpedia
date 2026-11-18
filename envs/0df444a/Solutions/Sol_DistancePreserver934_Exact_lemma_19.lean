-- Prove2me | solution 1 for DistancePreserver934.Exact.lemma_19
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T23:54:42.550244+00:00
-- url     : https://prove2.me/submissions/6cd50aee-fa6a-4350-af1c-63f4c28361ac

import Mathlib

set_option autoImplicit false
open Classical
open scoped BigOperators

theorem solution {ι α : Type*} [Fintype ι] [DecidableEq α] (A : ι → Finset α) (γ : ℝ)
    (hM : 1 ≤ Fintype.card ι) (hΔ : 0 < ∑ i, (A i).card)
    (hμ : ∀ q : α, ((Finset.univ.filter (fun i => q ∈ A i)).card : ℝ) ≤ γ) :
    ∃ J : Finset ι,
      ((∑ i, (A i).card : ℕ) : ℝ) / (2 * γ) ≤ ((J.biUnion A).card : ℝ) ∧
      (J.card : ℝ) ≤ 2 * (Fintype.card ι : ℝ) / ((∑ i, (A i).card : ℕ) : ℝ) *
        ((J.biUnion A).card : ℝ) := by
  classical
  let D : ℝ := ∑ i, ((A i).card : ℝ)
  let M : ℝ := Fintype.card ι
  have hD : 0 < D := by dsimp [D]; exact_mod_cast hΔ
  have hM' : 0 < M := by dsimp [M]; exact_mod_cast hM
  let t := D / (2 * M)
  have ht : 0 < t := div_pos hD (by positivity)
  let f : Finset ι → ℝ := fun J => ((J.biUnion A).card : ℝ) - t * J.card
  obtain ⟨J, _, hJ⟩ := Finset.exists_max_image (Finset.univ : Finset (Finset ι)) f (by simp)
  have hscore : 0 ≤ f J := by simpa [f] using hJ ∅ (Finset.mem_univ _)
  let Q := J.biUnion A
  have hres (i : ι) : ((A i \ Q).card : ℝ) ≤ t := by
    by_cases hi : i ∈ J
    · have hs : A i ⊆ Q := Finset.subset_biUnion_of_mem A hi
      simp [Finset.sdiff_eq_empty_iff_subset.mpr hs, ht.le]
    · have hm := hJ (insert i J) (Finset.mem_univ _)
      have hc := Finset.card_sdiff_add_card (A i) Q
      have hc' : ((A i \ Q).card : ℝ) + Q.card = ((A i ∪ Q).card : ℝ) := by exact_mod_cast hc
      simp only [f, Finset.biUnion_insert, Finset.card_insert_of_notMem hi, Nat.cast_add,
        Nat.cast_one] at hm
      change ((A i ∪ Q).card : ℝ) - t * ((J.card : ℝ) + 1) ≤ (Q.card : ℝ) - t * J.card at hm
      linarith
  have hresSum : ∑ i, ((A i \ Q).card : ℝ) ≤ D / 2 := by
    calc
      _ ≤ ∑ _i : ι, t := Finset.sum_le_sum (fun i _ => hres i)
      _ = D / 2 := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        change M * (D / (2 * M)) = D / 2
        field_simp
  have hsplit : (∑ i, ((A i \ Q).card : ℝ)) + (∑ i, ((A i ∩ Q).card : ℝ)) = D := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact_mod_cast Finset.card_sdiff_add_card_inter (A i) Q
  have hcount : (∑ i, ((A i ∩ Q).card : ℝ)) =
      ∑ q ∈ Q, ((Finset.univ.filter (fun i => q ∈ A i)).card : ℝ) := by
    simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one,
      Finset.sum_filter]
    rw [Finset.sum_comm]
    simp [Finset.inter_comm]
  have hcovered : D / 2 ≤ γ * (Q.card : ℝ) := by
    have hb : (∑ i, ((A i ∩ Q).card : ℝ)) ≤ γ * (Q.card : ℝ) := by
      rw [hcount, mul_comm γ]
      simpa using Finset.sum_le_sum (fun q (_ : q ∈ Q) => hμ q)
    linarith
  have hγ : 0 < γ := by
    by_contra! hn
    have : γ * (Q.card : ℝ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hn (Nat.cast_nonneg _)
    linarith
  refine ⟨J, ?_, ?_⟩
  · change ((∑ i, (A i).card : ℕ) : ℝ) / (2 * γ) ≤ (Q.card : ℝ)
    rw [div_le_iff₀ (by positivity)]
    have hcast : ((∑ i, (A i).card : ℕ) : ℝ) = D := by simp [D]
    rw [hcast]
    nlinarith
  · have hcast : ((∑ i, (A i).card : ℕ) : ℝ) = D := by simp [D]
    rw [hcast]
    change (J.card : ℝ) ≤ 2 * M / D * Q.card
    apply (mul_le_mul_iff_left₀ hD).mp
    have hs : t * (J.card : ℝ) ≤ (Q.card : ℝ) := by change 0 ≤ (Q.card : ℝ) - t * J.card at hscore; linarith
    have hs' := (div_le_iff₀ (by positivity : 0 < 2 * M)).mp (show D * J.card / (2 * M) ≤ (Q.card : ℝ) by simpa [t, div_mul_eq_mul_div] using hs)
    calc
      (J.card : ℝ) * D ≤ 2 * M * Q.card := by nlinarith
      _ = (2 * M / D * Q.card) * D := by field_simp
