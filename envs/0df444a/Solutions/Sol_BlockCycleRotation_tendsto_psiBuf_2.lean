-- Prove2me | solution 2 for BlockCycleRotation.tendsto_psiBuf
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-05T12:45:21.607189+00:00
-- url     : https://prove2.me/submissions/769ecf8d-ac64-4458-bd09-c363ea91cf8f

import Definitions.Def_BlockCycleRotation_Buffer
import Definitions.Def_BlockCycleRotation_Theorem10
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

private theorem Outt_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) : Outt x ≤ 2 / 3 := by
  unfold Outt
  split_ifs with h
  · norm_num
  · have hx0' : 0 < x := lt_of_le_of_ne hx0 (Ne.symm h)
    have h2 : (2 : ℝ) ≤ 1 / x := by
      rw [le_div_iff₀ hx0']
      linarith
    have hm2 : (2 : ℝ) ≤ ((⌊1 / x⌋ : ℤ) : ℝ) := by
      have : (2 : ℤ) ≤ ⌊1 / x⌋ := Int.le_floor.2 (by exact_mod_cast h2)
      exact_mod_cast this
    have hfl' : 1 / x < ((⌊1 / x⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
    have hub : 1 < (((⌊1 / x⌋ : ℤ) : ℝ) + 1) * x := (div_lt_iff₀ hx0').1 hfl'
    have heq : x * (1 + Int.fract (1 / x)) = 1 - (((⌊1 / x⌋ : ℤ) : ℝ) - 1) * x := by
      rw [Int.fract]
      field_simp
      ring
    rw [heq]
    nlinarith [hub, hm2, hx0']

private theorem iterate_Inn_mem {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (i : ℕ) :
    0 ≤ Inn^[i] x ∧ Inn^[i] x ≤ 1 / 2 := by
  cases i with
  | zero => exact ⟨hx0, hx⟩
  | succ j =>
    rw [Function.iterate_succ_apply']
    exact ⟨Inn_nonneg _, le_of_lt (Inn_lt_half _)⟩

private theorem prod_Outt_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (i : ℕ) :
    (0 ≤ ∏ m ∈ Finset.range i, Outt (Inn^[m] x))
      ∧ (∏ m ∈ Finset.range i, Outt (Inn^[m] x)) ≤ (2 / 3) ^ i := by
  constructor
  · refine Finset.prod_nonneg fun m _ => Outt_nonneg (iterate_Inn_mem hx0 hx m).1
  · calc (∏ m ∈ Finset.range i, Outt (Inn^[m] x))
        ≤ ∏ _m ∈ Finset.range i, (2 / 3 : ℝ) := by
          refine Finset.prod_le_prod (fun m _ => Outt_nonneg (iterate_Inn_mem hx0 hx m).1)
            (fun m _ => Outt_le (iterate_Inn_mem hx0 hx m).1 (iterate_Inn_mem hx0 hx m).2)
      _ = (2 / 3 : ℝ) ^ i := by rw [Finset.prod_const, Finset.card_range]

private theorem psiTerm_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (i : ℕ) : 0 ≤ psiTerm x i := by
  unfold psiTerm
  have h1 := (prod_Outt_le hx0 hx i).1
  have h2 := (iterate_Inn_mem hx0 hx i).1
  positivity

private theorem psiTerm_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (i : ℕ) :
    psiTerm x i ≤ (2 / 3 : ℝ) ^ i := by
  unfold psiTerm
  obtain ⟨hp0, hp⟩ := prod_Outt_le hx0 hx i
  obtain ⟨hi0, hi⟩ := iterate_Inn_mem hx0 hx i
  have hpow : (0 : ℝ) ≤ (2 / 3 : ℝ) ^ i := by positivity
  nlinarith

private theorem psi_summable {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) : Summable (psiTerm x) := by
  refine Summable.of_nonneg_of_le (psiTerm_nonneg hx0 hx) (psiTerm_le hx0 hx) ?_
  exact summable_geometric_of_lt_one (by norm_num) (by norm_num)

private theorem psiTerm_eq_two_mul_seg (x : ℝ) (i : ℕ) : psiTerm x i = 2 * seg x i := by
  unfold psiTerm seg
  ring

private theorem seg_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (i : ℕ) : 0 ≤ seg x i := by
  unfold seg
  exact mul_nonneg (prod_Outt_le hx0 hx i).1 (iterate_Inn_mem hx0 hx i).1

private theorem seg_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (i : ℕ) :
    seg x i ≤ (2 / 3 : ℝ) ^ i * (1 / 2) := by
  unfold seg
  obtain ⟨hp0, hp⟩ := prod_Outt_le hx0 hx i
  obtain ⟨hi0, hi⟩ := iterate_Inn_mem hx0 hx i
  have hpow : (0 : ℝ) ≤ (2 / 3 : ℝ) ^ i := by positivity
  nlinarith

private theorem exists_seg_le {β x : ℝ} (hβ : 0 < β) (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    ∃ i, seg x i ≤ β := by
  obtain ⟨i, hi⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 2 * β by linarith)
    (show (2 / 3 : ℝ) < 1 by norm_num)
  exact ⟨i, le_of_lt (lt_of_le_of_lt (seg_le hx0 hx i) (by linarith))⟩

private theorem seg_bufDepth_le {β x : ℝ} (h : ∃ i, seg x i ≤ β) : seg x (bufDepth β x) ≤ β :=
  Nat.sInf_mem h

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

private theorem seg_add_two_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (i : ℕ) :
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

private theorem seg_succ_le_self {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (i : ℕ) :
    seg x (i + 1) ≤ seg x i := by
  rw [seg_succ' x i]
  have hg0 : (0 : ℝ) ≤ Int.fract (1 / Inn^[i] x) := Int.fract_nonneg _
  have hg1 : Int.fract (1 / Inn^[i] x) < 1 := Int.fract_lt_one _
  nlinarith [seg_nonneg hx0 hx i]

private theorem seg_summable {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) : Summable (seg x) := by
  have h := (psi_summable hx0 hx).div_const 2
  refine h.congr fun i => ?_
  rw [psiTerm_eq_two_mul_seg]
  ring

private theorem tsum_seg_tail_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (T : ℕ) :
    ∑' j, seg x (T + j) ≤ 2 * (seg x T + seg x (T + 1)) := by
  have hs : Summable (fun j => seg x (T + j)) := by
    have := (seg_summable hx0 hx).comp_injective (add_right_injective T)
    exact this
  have hs2 : Summable (fun j => seg x (T + (j + 2))) := by
    have := (summable_nat_add_iff 2).2 hs
    exact this
  have hsplit := hs.sum_add_tsum_nat_add 2
  have hbound : ∑' j, seg x (T + (j + 2)) ≤ ∑' j, seg x (T + j) / 2 := by
    refine hs2.tsum_le_tsum (fun j => ?_) (hs.div_const 2)
    have := seg_add_two_le hx0 hx (T + j)
    have heq : T + (j + 2) = T + j + 2 := by omega
    rw [heq]
    linarith
  rw [tsum_div_const] at hbound
  have hfin : ∑ j ∈ Finset.range 2, seg x (T + j) = seg x T + seg x (T + 1) := by
    rw [Finset.sum_range_succ, Finset.sum_range_one, Nat.add_zero]
  rw [hfin] at hsplit
  linarith

private theorem psi_sub_psiBuf_le_linear {β x : ℝ} (hβ : 0 < β) (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    psi x - psiBuf β x ≤ 8 * β := by
  have hex : ∃ i, seg x i ≤ β := exists_seg_le hβ hx0 hx
  set T := bufDepth β x with hT
  have hsT : seg x T ≤ β := seg_bufDepth_le hex
  have hsT1 : seg x (T + 1) ≤ β := le_trans (seg_succ_le_self hx0 hx T) hsT
  have htail := tsum_seg_tail_le hx0 hx T
  have hs : Summable (seg x) := seg_summable hx0 hx
  have hsplit := hs.sum_add_tsum_nat_add T
  have hpsi : psi x = 2 * ∑' i, seg x i := by
    rw [psi, ← tsum_mul_left]
    exact tsum_congr fun i => psiTerm_eq_two_mul_seg x i
  have hnn := seg_nonneg hx0 hx T
  have hcomm : ∑' i : ℕ, seg x (i + T) = ∑' j : ℕ, seg x (T + j) :=
    tsum_congr fun i => by rw [Nat.add_comm]
  rw [hcomm] at hsplit
  rw [hpsi, psiBuf]
  linarith

private theorem psiPartial_eq_two_mul (x : ℝ) (N : ℕ) :
    psiPartial N x = 2 * ∑ i ∈ Finset.range N, seg x i := by
  rw [psiPartial, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => psiTerm_eq_two_mul_seg x i

private theorem psiPartial_le_psi {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (N : ℕ) :
    psiPartial N x ≤ psi x :=
  (psi_summable hx0 hx).sum_le_tsum (Finset.range N) (fun i _ => psiTerm_nonneg hx0 hx i)

private theorem psiBuf_le_psi {β x : ℝ} (_hβ : 0 < β) (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    psiBuf β x ≤ psi x := by
  have hstep : psiBuf β x ≤ psiPartial (bufDepth β x + 1) x := by
    rw [psiBuf, psiPartial_eq_two_mul, Finset.sum_range_succ]
    have := seg_nonneg hx0 hx (bufDepth β x)
    linarith
  exact le_trans hstep (psiPartial_le_psi hx0 hx _)

theorem solution {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    Filter.Tendsto (fun β => psiBuf β x) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (psi x)) := by
  have hlow : Filter.Tendsto (fun β : ℝ => psi x - 8 * β) (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 (psi x)) := by
    have h : Filter.Tendsto (fun β : ℝ => psi x - 8 * β) (𝓝 0) (𝓝 (psi x - 8 * 0)) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.mul Filter.tendsto_id)
    rw [mul_zero, sub_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with β hβ
    linarith [psi_sub_psiBuf_le_linear hβ hx0 hx]
  · filter_upwards [self_mem_nhdsWithin] with β hβ
    exact psiBuf_le_psi hβ hx0 hx
