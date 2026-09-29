-- Prove2me | solution 1 for BlockCycleRotation.psi_sub_psiBuf_le_linear
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T12:10:30.471135+00:00
-- url     : https://prove2.me/submissions/246123dd-cb01-471b-8ed6-c286cfe83b1a

import Definitions.Def_BlockCycleRotation_Algorithm
import Definitions.Def_BlockCycleRotation_Buffer
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Definitions.Def_BlockCycleRotation_Theorem10
import Theorems.Thm_BlockCycleRotation_Outt_le
import Theorems.Thm_BlockCycleRotation_seg_succ_prime
import Theorems.Thm_BlockCycleRotation_seg_add_two_le
import Mathlib

open Finset Filter Topology Real MeasureTheory BoxIntegral
open scoped ENNReal

namespace BlockCycleRotation

@[simp]
theorem remSum_zero (n : ℕ) : remSum n 0 = 0 := by
  rw [remSum]; simp

@[simp]
theorem norm_e (θ : ℝ) : ‖e θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

@[simp]
theorem norm_e_pow (θ : ℝ) (n : ℕ) : ‖e θ ^ n‖ = 1 := by
  rw [norm_pow, norm_e, one_pow]

@[simp]
theorem cost_zero (n : ℕ) : cost n 0 = 0 := by
  rw [cost]; simp

@[simp]
theorem finalSeg_zero (n : ℕ) : finalSeg n 0 = n := by
  rw [finalSeg]; simp

@[simp]
theorem e_zero : e 0 = 1 := by simp [e]

@[simp] theorem K_nil : K [] = 1 := rfl

@[simp] theorem K_singleton (c : ℕ) : K [c] = c := rfl

@[simp] theorem cf_zero (a : ℕ) : cf a 0 = [] := by rw [cf]; simp

theorem Inn_nonneg (x : ℝ) : 0 ≤ Inn x := by
  unfold Inn
  split_ifs
  · exact le_refl 0
  · have h1 : (0 : ℝ) ≤ Int.fract (1 / x) := Int.fract_nonneg _
    positivity

/-- **`In` maps into `[0,1/2)`.**  Since `{1/x} < 1`, `{1/x}/(1+{1/x}) < 1/2`. -/
theorem Inn_lt_half (x : ℝ) : Inn x < 1 / 2 := by
  unfold Inn
  split_ifs
  · norm_num
  · have h1 : (0 : ℝ) ≤ Int.fract (1 / x) := Int.fract_nonneg _
    have h2 : Int.fract (1 / x) < 1 := Int.fract_lt_one _
    rw [div_lt_div_iff₀ (by linarith) (by norm_num)]
    linarith

theorem Outt_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Outt x := by
  unfold Outt
  split_ifs
  · exact le_refl 0
  · have h1 : (0 : ℝ) ≤ Int.fract (1 / x) := Int.fract_nonneg _
    positivity

theorem iterate_Inn_mem {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (i : ℕ) :
    0 ≤ Inn^[i] x ∧ Inn^[i] x ≤ 1 / 2 := by
  cases i with
  | zero => exact ⟨hx0, hx⟩
  | succ j =>
    rw [Function.iterate_succ_apply']
    exact ⟨Inn_nonneg _, le_of_lt (Inn_lt_half _)⟩

theorem prod_Outt_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (i : ℕ) :
    (0 ≤ ∏ m ∈ Finset.range i, Outt (Inn^[m] x))
      ∧ (∏ m ∈ Finset.range i, Outt (Inn^[m] x)) ≤ (2 / 3) ^ i := by
  constructor
  · refine Finset.prod_nonneg fun m _ => Outt_nonneg (iterate_Inn_mem hx0 hx m).1
  · calc (∏ m ∈ Finset.range i, Outt (Inn^[m] x))
        ≤ ∏ _m ∈ Finset.range i, (2 / 3 : ℝ) := by
          refine Finset.prod_le_prod (fun m _ => Outt_nonneg (iterate_Inn_mem hx0 hx m).1)
            (fun m _ => Outt_le (iterate_Inn_mem hx0 hx m).1 (iterate_Inn_mem hx0 hx m).2)
      _ = (2 / 3 : ℝ) ^ i := by rw [Finset.prod_const, Finset.card_range]

theorem psiTerm_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (i : ℕ) : 0 ≤ psiTerm x i := by
  unfold psiTerm
  have h1 := (prod_Outt_le hx0 hx i).1
  have h2 := (iterate_Inn_mem hx0 hx i).1
  positivity

theorem psiTerm_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (i : ℕ) :
    psiTerm x i ≤ (2 / 3 : ℝ) ^ i := by
  unfold psiTerm
  obtain ⟨hp0, hp⟩ := prod_Outt_le hx0 hx i
  obtain ⟨hi0, hi⟩ := iterate_Inn_mem hx0 hx i
  have hpow : (0 : ℝ) ≤ (2 / 3 : ℝ) ^ i := by positivity
  nlinarith

theorem psi_summable {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) : Summable (psiTerm x) := by
  refine Summable.of_nonneg_of_le (psiTerm_nonneg hx0 hx) (psiTerm_le hx0 hx) ?_
  exact summable_geometric_of_lt_one (by norm_num) (by norm_num)

theorem psiTerm_eq_two_mul_seg (x : ℝ) (i : ℕ) : psiTerm x i = 2 * seg x i := by
  unfold psiTerm seg
  ring

theorem seg_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (i : ℕ) : 0 ≤ seg x i := by
  unfold seg
  exact mul_nonneg (prod_Outt_le hx0 hx i).1 (iterate_Inn_mem hx0 hx i).1

theorem seg_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (i : ℕ) :
    seg x i ≤ (2 / 3 : ℝ) ^ i * (1 / 2) := by
  unfold seg
  obtain ⟨hp0, hp⟩ := prod_Outt_le hx0 hx i
  obtain ⟨hi0, hi⟩ := iterate_Inn_mem hx0 hx i
  have hpow : (0 : ℝ) ≤ (2 / 3 : ℝ) ^ i := by positivity
  nlinarith

theorem exists_seg_le {β x : ℝ} (hβ : 0 < β) (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    ∃ i, seg x i ≤ β := by
  obtain ⟨i, hi⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 2 * β by linarith)
    (show (2 / 3 : ℝ) < 1 by norm_num)
  exact ⟨i, le_of_lt (lt_of_le_of_lt (seg_le hx0 hx i) (by linarith))⟩

theorem seg_bufDepth_le {β x : ℝ} (h : ∃ i, seg x i ≤ β) : seg x (bufDepth β x) ≤ β :=
  Nat.sInf_mem h

/-- The one-step ratio is at most `1`, so segments are non-increasing. -/
theorem seg_succ_le_self {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (i : ℕ) :
    seg x (i + 1) ≤ seg x i := by
  rw [seg_succ_prime x i]
  have hg0 : (0 : ℝ) ≤ Int.fract (1 / Inn^[i] x) := Int.fract_nonneg _
  have hg1 : Int.fract (1 / Inn^[i] x) < 1 := Int.fract_lt_one _
  nlinarith [seg_nonneg hx0 hx i]

theorem seg_summable {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) : Summable (seg x) := by
  have h := (psi_summable hx0 hx).div_const 2
  refine h.congr fun i => ?_
  rw [psiTerm_eq_two_mul_seg]
  ring

theorem tsum_seg_tail_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (T : ℕ) :
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

@[simp]
theorem costB_zero (n b : ℕ) : costB n 0 b = 0 := by rw [costB]; simp

end BlockCycleRotation

open BlockCycleRotation in
/-- **`ψ - ψ_β ≤ 8β`.** -/
theorem solution {β x : ℝ} (hβ : 0 < β) (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    psi x - psiBuf β x ≤ 8 * β:= by
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
