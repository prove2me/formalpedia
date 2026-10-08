-- Prove2me | solution 1 for Disjunctive.MonoidalStrengthening.gmi_strictly_dominating_cuts_v2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T07:24:41.785823+00:00
-- url     : https://prove2.me/submissions/c25efe57-21c0-4c77-9f02-07de36145b80

import Mathlib
import Definitions.Def_Disjunctive_MonoidalStrengthening_Basic

set_option autoImplicit false

namespace P94b68679

open Disjunctive.MonoidalStrengthening

theorem key {n : ℕ} (f : ℝ) (hf0 : 0 < f) (hf1 : f < 1) (a c x t : Fin n → ℝ) (y : ℝ)
    (hy : y = 0 ∨ y = 1) (hrow : f - ∑ j, a j * x j = y)
    (hint : ∀ j, ∃ z : ℤ, t j = z) (ht0 : ∀ j, 0 ≤ t j)
    (h2 : ∀ j, (t j - a j * x j) / (1 - f) ≤ c j * x j)
    (h1 : ∀ j, t j = 0 → (a j * x j - t j) / f ≤ c j * x j) :
    1 ≤ ∑ j, c j * x j := by
  choose z hz using hint
  have hT : ∑ j, t j = ((∑ j, z j : ℤ) : ℝ) := by push_cast; simp [hz]
  have hTnn : 0 ≤ ∑ j, t j := Finset.sum_nonneg (fun j _ => ht0 j)
  have hZnn : 0 ≤ ∑ j, z j := by
    have : (0:ℝ) ≤ ((∑ j, z j : ℤ) : ℝ) := hT ▸ hTnn
    exact_mod_cast this
  have hf1' : 0 < 1 - f := by linarith
  have hy0 : 0 ≤ y := by rcases hy with h | h <;> simp [h]
  by_cases hcase : 1 ≤ y + ∑ j, t j
  · have hsum : ∑ j, (t j - a j * x j) / (1 - f) ≤ ∑ j, c j * x j :=
      Finset.sum_le_sum (fun j _ => h2 j)
    rw [← Finset.sum_div, Finset.sum_sub_distrib] at hsum
    have : 1 ≤ (∑ j, t j - ∑ j, a j * x j) / (1 - f) := by
      rw [le_div_iff₀ hf1']; linarith
    linarith
  · have hZ : ∑ j, z j = 0 := by
      by_contra hne
      have h1' : 1 ≤ ∑ j, z j := by omega
      have : (1:ℝ) ≤ ∑ j, t j := by rw [hT]; exact_mod_cast h1'
      exact hcase (by linarith)
    have hT0 : ∑ j, t j = 0 := by rw [hT, hZ]; simp
    have hall : ∀ j, t j = 0 := fun j =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => ht0 j)).1 hT0 j (Finset.mem_univ j)
    have hyz : y = 0 := by
      rcases hy with h | h
      · exact h
      · exfalso; apply hcase; rw [h]; linarith
    have hsum : ∑ j, (a j * x j - t j) / f ≤ ∑ j, c j * x j :=
      Finset.sum_le_sum (fun j _ => h1 j (hall j))
    rw [← Finset.sum_div, Finset.sum_sub_distrib, hT0] at hsum
    have : 1 ≤ (∑ j, a j * x j - 0) / f := by
      rw [le_div_iff₀ hf0]; linarith
    linarith

theorem plus_j {n : ℕ} (a0 : ℝ) (a : Fin n → ℝ) (J1 : Finset (Fin n)) (ha0 : 0 < a0)
    (ha0' : a0 < 1) (x : Fin n → ℝ) (hx : 0 ≤ x) (hx_int : ∀ j ∈ J1, ∃ k : ℤ, x j = (k : ℝ))
    (j : Fin n) :
    ∃ t : ℝ, (∃ z : ℤ, t = z) ∧ 0 ≤ t ∧
      (t - a j * x j) / (1 - a0) ≤ AlphaPlus a0 a J1 j * x j ∧
      (t = 0 → (a j * x j - t) / a0 ≤ AlphaPlus a0 a J1 j * x j) := by
  have hxj : 0 ≤ x j := hx j
  have h1f : 0 < 1 - a0 := by linarith
  unfold AlphaPlus
  split_ifs with hA hB
  · obtain ⟨k, hk⟩ := hx_int j hA.1
    refine ⟨x j, ⟨k, hk⟩, hxj, le_of_eq (by ring), ?_⟩
    intro h0; rw [h0]; simp
  · obtain ⟨k, hk⟩ := hx_int j hB.1
    have hceil : (-1 : ℤ) < ⌈a j⌉ := Int.lt_ceil.2 (by push_cast; linarith)
    have hcnn : (0:ℝ) ≤ (⌈a j⌉ : ℝ) := by exact_mod_cast (by omega : (0:ℤ) ≤ ⌈a j⌉)
    have hle_c : a j ≤ (⌈a j⌉ : ℝ) := Int.le_ceil _
    have hfl_le : (⌊a j⌋ : ℝ) ≤ a j := Int.floor_le _
    have hB0 : 0 ≤ (-(a j) + (⌈a j⌉ : ℝ)) / (1 - a0) := div_nonneg (by linarith) h1f.le
    have hA0 : 0 ≤ (a j - (⌊a j⌋ : ℝ)) / a0 := div_nonneg (by linarith) ha0.le
    by_cases hBA : (-(a j) + (⌈a j⌉ : ℝ)) / (1 - a0) ≤ (a j - (⌊a j⌋ : ℝ)) / a0
    · rw [min_eq_right hBA]
      refine ⟨(⌈a j⌉ : ℝ) * x j, ⟨⌈a j⌉ * k, by rw [hk]; push_cast; ring⟩,
        mul_nonneg hcnn hxj, le_of_eq (by ring), ?_⟩
      intro _
      rw [div_le_iff₀ ha0]
      have : 0 ≤ (-(a j) + (⌈a j⌉ : ℝ)) / (1 - a0) * x j * a0 :=
        mul_nonneg (mul_nonneg hB0 hxj) ha0.le
      nlinarith
    · rw [not_le] at hBA
      rw [min_eq_left hBA.le]
      have hfloor : (-1 : ℤ) ≤ ⌊a j⌋ := Int.le_floor.2 (by push_cast; linarith)
      have hfnn : (0 : ℤ) ≤ ⌊a j⌋ := by
        by_contra hneg
        have hfl : ⌊a j⌋ = -1 := by omega
        have hlt0 : a j < 0 := by
          have := Int.lt_floor_add_one (a j)
          rw [hfl] at this; push_cast at this; linarith
        have hcl : ⌈a j⌉ = 0 := by
          have : ⌈a j⌉ ≤ 0 := Int.ceil_le.2 (by push_cast; linarith)
          omega
        rw [hfl, hcl] at hBA
        push_cast at hBA
        rw [div_lt_div_iff₀ ha0 h1f] at hBA
        nlinarith
      have hfnn' : (0:ℝ) ≤ (⌊a j⌋ : ℝ) := by exact_mod_cast hfnn
      refine ⟨(⌊a j⌋ : ℝ) * x j, ⟨⌊a j⌋ * k, by rw [hk]; push_cast; ring⟩,
        mul_nonneg hfnn' hxj, ?_, fun _ => le_of_eq (by ring)⟩
      rw [div_le_iff₀ h1f]
      have : 0 ≤ (a j - (⌊a j⌋ : ℝ)) / a0 * x j * (1 - a0) :=
        mul_nonneg (mul_nonneg hA0 hxj) h1f.le
      nlinarith
  · refine ⟨0, ⟨0, by simp⟩, le_refl _, ?_, ?_⟩
    · have := mul_le_mul_of_nonneg_right (le_max_right (a j / a0) (-(a j) / (1 - a0))) hxj
      calc (0 - a j * x j) / (1 - a0) = -(a j) / (1 - a0) * x j := by ring
        _ ≤ _ := this
    · intro _
      have := mul_le_mul_of_nonneg_right (le_max_left (a j / a0) (-(a j) / (1 - a0))) hxj
      calc (a j * x j - 0) / a0 = a j / a0 * x j := by ring
        _ ≤ _ := this

theorem minus_j {n : ℕ} (a0 : ℝ) (a : Fin n → ℝ) (J1 : Finset (Fin n)) (ha0 : 0 < a0)
    (ha0' : a0 < 1) (x : Fin n → ℝ) (hx : 0 ≤ x) (hx_int : ∀ j ∈ J1, ∃ k : ℤ, x j = (k : ℝ))
    (j : Fin n) :
    ∃ t : ℝ, (∃ z : ℤ, t = z) ∧ t ≤ 0 ∧
      (a j * x j - t) / a0 ≤ AlphaMinus a0 a J1 j * x j ∧
      (t = 0 → (t - a j * x j) / (1 - a0) ≤ AlphaMinus a0 a J1 j * x j) := by
  have hxj : 0 ≤ x j := hx j
  have h1f : 0 < 1 - a0 := by linarith
  unfold AlphaMinus
  split_ifs with hA hB
  · obtain ⟨k, hk⟩ := hx_int j hA.1
    refine ⟨-x j, ⟨-k, by rw [hk]; push_cast; ring⟩, by linarith, le_of_eq (by ring), ?_⟩
    intro h0
    have : x j = 0 := by linarith
    rw [h0, this]; simp
  · obtain ⟨k, hk⟩ := hx_int j hB.1
    have hle_c : a j ≤ (⌈a j⌉ : ℝ) := Int.le_ceil _
    have hfl_le : (⌊a j⌋ : ℝ) ≤ a j := Int.floor_le _
    have hB0 : 0 ≤ (-(a j) + (⌈a j⌉ : ℝ)) / (1 - a0) := div_nonneg (by linarith) h1f.le
    have hA0 : 0 ≤ (a j - (⌊a j⌋ : ℝ)) / a0 := div_nonneg (by linarith) ha0.le
    by_cases hAB : (a j - (⌊a j⌋ : ℝ)) / a0 ≤ (-(a j) + (⌈a j⌉ : ℝ)) / (1 - a0)
    · rw [min_eq_left hAB]
      have hfl : ⌊a j⌋ < 1 := Int.floor_lt.2 (by push_cast; linarith)
      have hfnp : (⌊a j⌋ : ℝ) ≤ 0 := by exact_mod_cast (by omega : ⌊a j⌋ ≤ 0)
      refine ⟨(⌊a j⌋ : ℝ) * x j, ⟨⌊a j⌋ * k, by rw [hk]; push_cast; ring⟩,
        mul_nonpos_of_nonpos_of_nonneg hfnp hxj, le_of_eq (by ring), ?_⟩
      intro _
      rw [div_le_iff₀ h1f]
      have : 0 ≤ (a j - (⌊a j⌋ : ℝ)) / a0 * x j * (1 - a0) :=
        mul_nonneg (mul_nonneg hA0 hxj) h1f.le
      nlinarith
    · rw [not_le] at hAB
      rw [min_eq_right hAB.le]
      have hcle1 : ⌈a j⌉ ≤ 1 := Int.ceil_le.2 (by push_cast; linarith)
      have hcnp : ⌈a j⌉ ≤ 0 := by
        by_contra hpos
        have hcl : ⌈a j⌉ = 1 := by omega
        have hpos' : 0 < a j := by
          by_contra hle
          rw [not_lt] at hle
          have : ⌈a j⌉ ≤ 0 := Int.ceil_le.2 (by push_cast; linarith)
          omega
        have hfl : ⌊a j⌋ = 0 := by
          rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
        rw [hfl, hcl] at hAB
        push_cast at hAB
        rw [div_lt_div_iff₀ h1f ha0] at hAB
        nlinarith
      have hcnp' : (⌈a j⌉ : ℝ) ≤ 0 := by exact_mod_cast hcnp
      refine ⟨(⌈a j⌉ : ℝ) * x j, ⟨⌈a j⌉ * k, by rw [hk]; push_cast; ring⟩,
        mul_nonpos_of_nonpos_of_nonneg hcnp' hxj, ?_, fun _ => le_of_eq (by ring)⟩
      rw [div_le_iff₀ ha0]
      have : 0 ≤ (-(a j) + (⌈a j⌉ : ℝ)) / (1 - a0) * x j * a0 :=
        mul_nonneg (mul_nonneg hB0 hxj) ha0.le
      nlinarith
  · refine ⟨0, ⟨0, by simp⟩, le_refl _, ?_, ?_⟩
    · have := mul_le_mul_of_nonneg_right (le_max_left (a j / a0) (-(a j) / (1 - a0))) hxj
      calc (a j * x j - 0) / a0 = a j / a0 * x j := by ring
        _ ≤ _ := this
    · intro _
      have := mul_le_mul_of_nonneg_right (le_max_right (a j / a0) (-(a j) / (1 - a0))) hxj
      calc (0 - a j * x j) / (1 - a0) = -(a j) / (1 - a0) * x j := by ring
        _ ≤ _ := this

end P94b68679

open Disjunctive.MonoidalStrengthening in
theorem solution {n : ℕ} (a0 : ℝ) (a : Fin n → ℝ) (J1 : Finset (Fin n))
    (ha0 : 0 < a0) (ha0' : a0 < 1)
    (x : Fin n → ℝ) (hx_nonneg : 0 ≤ x) (hx_int : ∀ j ∈ J1, ∃ k : ℤ, x j = (k : ℝ))
    (hy : a0 - ∑ j, a j * x j = 0 ∨ a0 - ∑ j, a j * x j = 1) :
    1 ≤ ∑ j, AlphaPlus a0 a J1 j * x j ∧ 1 ≤ ∑ j, AlphaMinus a0 a J1 j * x j := by
  constructor
  · choose t ht using fun j => P94b68679.plus_j a0 a J1 ha0 ha0' x hx_nonneg hx_int j
    exact P94b68679.key a0 ha0 ha0' a (fun j => AlphaPlus a0 a J1 j) x t _ hy rfl
      (fun j => (ht j).1) (fun j => (ht j).2.1) (fun j => (ht j).2.2.1) (fun j => (ht j).2.2.2)
  · choose t ht using fun j => P94b68679.minus_j a0 a J1 ha0 ha0' x hx_nonneg hx_int j
    have hy' : 1 - (a0 - ∑ j, a j * x j) = 0 ∨ 1 - (a0 - ∑ j, a j * x j) = 1 := by
      rcases hy with h | h
      · right; rw [h]; norm_num
      · left; rw [h]; norm_num
    refine P94b68679.key (1 - a0) (by linarith) (by linarith) (fun j => -a j)
      (fun j => AlphaMinus a0 a J1 j) x (fun j => -t j) _ hy' ?_ ?_ ?_ ?_ ?_
    · simp only [neg_mul, Finset.sum_neg_distrib]; ring
    · intro j
      obtain ⟨z, hz⟩ := (ht j).1
      exact ⟨-z, by rw [hz]; push_cast; ring⟩
    · intro j; have := (ht j).2.1; linarith
    · intro j
      have h := (ht j).2.2.1
      have e : (-t j - -a j * x j) / (1 - (1 - a0)) = (a j * x j - t j) / a0 := by ring
      rw [e]; exact h
    · intro j h0
      have h0' : t j = 0 := by linarith
      have h := (ht j).2.2.2 h0'
      have e : (-a j * x j - -t j) / (1 - a0) = (t j - a j * x j) / (1 - a0) := by ring
      rw [e]; exact h
