-- Prove2me | solution 2 for BlockCycleRotation.seg_add_two_le
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-05T12:28:41.743358+00:00
-- url     : https://prove2.me/submissions/4c9ad8ee-3083-42cc-8e2e-2794a9fedaaf

import Definitions.Def_BlockCycleRotation_Buffer
import Mathlib

open BlockCycleRotation
open Finset Filter Topology Real MeasureTheory BoxIntegral
open scoped ENNReal

private theorem Inn_nonneg (x : ℝ) : 0 ≤ Inn x := by
  unfold Inn
  split_ifs
  · exact le_refl 0
  · have h1 : (0 : ℝ) ≤ Int.fract (1 / x) := Int.fract_nonneg _
    positivity

private theorem Inn_lt_half (x : ℝ) : Inn x < 1 / 2 := by
  unfold Inn
  split_ifs
  · norm_num
  · have h1 : (0 : ℝ) ≤ Int.fract (1 / x) := Int.fract_nonneg _
    have h2 : Int.fract (1 / x) < 1 := Int.fract_lt_one _
    rw [div_lt_div_iff₀ (by linarith) (by norm_num)]
    linarith

private theorem Outt_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Outt x := by
  unfold Outt
  split_ifs
  · exact le_refl 0
  · have h1 : (0 : ℝ) ≤ Int.fract (1 / x) := Int.fract_nonneg _
    positivity

private theorem iterate_Inn_mem {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (i : ℕ) :
    0 ≤ Inn^[i] x ∧ Inn^[i] x ≤ 1 / 2 := by
  cases i with
  | zero => exact ⟨hx0, hx⟩
  | succ j =>
    rw [Function.iterate_succ_apply']
    exact ⟨Inn_nonneg _, le_of_lt (Inn_lt_half _)⟩

private theorem prod_Outt_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (i : ℕ) :
    0 ≤ ∏ m ∈ Finset.range i, Outt (Inn^[m] x) :=
  Finset.prod_nonneg fun m _ => Outt_nonneg (iterate_Inn_mem hx0 hx m).1

private theorem seg_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (i : ℕ) : 0 ≤ seg x i := by
  unfold seg
  exact mul_nonneg (prod_Outt_nonneg hx0 hx i) (iterate_Inn_mem hx0 hx i).1

private theorem Outt_mul_Inn (y : ℝ) : Outt y * Inn y = y * Int.fract (1 / y) := by
  unfold Outt Inn
  split_ifs with h
  · rw [h]; simp
  · have hg : (0 : ℝ) ≤ Int.fract (1 / y) := Int.fract_nonneg _
    have hden : (1 : ℝ) + Int.fract (1 / y) ≠ 0 := by positivity
    field_simp

private theorem seg_succ' (x : ℝ) (i : ℕ) :
    seg x (i + 1) = seg x i * Int.fract (1 / Inn^[i] x) := by
  unfold seg
  rw [Finset.prod_range_succ, Function.iterate_succ_apply']
  have h := Outt_mul_Inn (Inn^[i] x)
  calc (∏ m ∈ Finset.range i, Outt (Inn^[m] x)) * Outt (Inn^[i] x) * Inn (Inn^[i] x)
      = (∏ m ∈ Finset.range i, Outt (Inn^[m] x)) * (Outt (Inn^[i] x) * Inn (Inn^[i] x)) := by
        ring
    _ = (∏ m ∈ Finset.range i, Outt (Inn^[m] x)) * (Inn^[i] x * Int.fract (1 / Inn^[i] x)) := by
        rw [h]
    _ = (∏ m ∈ Finset.range i, Outt (Inn^[m] x)) * Inn^[i] x * Int.fract (1 / Inn^[i] x) := by
        ring

private theorem fract_inv_Inn (y : ℝ) :
    Int.fract (1 / Inn y) = Int.fract (1 / Int.fract (1 / y)) := by
  unfold Inn
  split_ifs with h
  · rw [h]; simp
  · rcases eq_or_lt_of_le (Int.fract_nonneg (1 / y)) with hg | hg
    · rw [← hg]; simp
    · have hden : (0 : ℝ) < 1 + Int.fract (1 / y) := by linarith
      have hrw : 1 / (Int.fract (1 / y) / (1 + Int.fract (1 / y)))
          = 1 / Int.fract (1 / y) + 1 := by field_simp
      rw [hrw, Int.fract_add_one]

private theorem fract_mul_le_half {g : ℝ} (hg0 : 0 ≤ g) (hg1 : g < 1) :
    g * Int.fract (1 / g) ≤ 1 / 2 := by
  rcases eq_or_lt_of_le hg0 with h | hg
  · rw [← h]; simp
  · have hm : (1 : ℝ) < 1 / g := by rw [lt_div_iff₀ hg]; linarith
    have hm1 : (1 : ℝ) ≤ ((⌊1 / g⌋ : ℤ) : ℝ) := by
      have : (1 : ℤ) ≤ ⌊1 / g⌋ := Int.le_floor.2 (by exact_mod_cast le_of_lt hm)
      exact_mod_cast this
    have hlt : 1 / g < ((⌊1 / g⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
    have hub : 1 < (((⌊1 / g⌋ : ℤ) : ℝ) + 1) * g := (div_lt_iff₀ hg).1 hlt
    rw [Int.fract]
    have heq : g * (1 / g - ((⌊1 / g⌋ : ℤ) : ℝ)) = 1 - g * ((⌊1 / g⌋ : ℤ) : ℝ) := by
      field_simp
    rw [heq]
    nlinarith [hub, hm1, hg,
      mul_lt_mul_of_pos_left hub (show (0 : ℝ) < ((⌊1 / g⌋ : ℤ) : ℝ) by linarith)]

theorem solution {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (i : ℕ) :
    seg x (i + 2) ≤ 1 / 2 * seg x i := by
  have h1 : seg x (i + 1) = seg x i * Int.fract (1 / Inn^[i] x) := seg_succ' x i
  have h2 : seg x (i + 2) = seg x (i + 1) * Int.fract (1 / Inn^[i + 1] x) := seg_succ' x (i + 1)
  have h3 : Inn^[i + 1] x = Inn (Inn^[i] x) := Function.iterate_succ_apply' Inn i x
  have hg0 : (0 : ℝ) ≤ Int.fract (1 / Inn^[i] x) := Int.fract_nonneg _
  have hg1 : Int.fract (1 / Inn^[i] x) < 1 := Int.fract_lt_one _
  have hhalf := fract_mul_le_half hg0 hg1
  have hsi := seg_nonneg hx0 hx i
  rw [h2, h1, h3, fract_inv_Inn]
  nlinarith
