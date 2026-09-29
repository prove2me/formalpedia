-- Prove2me | solution 1 for BlockCycleRotation.psiBuf_rec
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T12:06:10.443026+00:00
-- url     : https://prove2.me/submissions/ede80c16-a8ce-452a-9a85-8f1a7add013c

import Definitions.Def_BlockCycleRotation_Algorithm
import Definitions.Def_BlockCycleRotation_Buffer
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Definitions.Def_BlockCycleRotation_Theorem10
import Theorems.Thm_BlockCycleRotation_Outt_le
import Theorems.Thm_BlockCycleRotation_seg_succ
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

theorem seg_zero (x : ℝ) : seg x 0 = x := by
  unfold seg
  simp

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

theorem lt_seg_of_lt_bufDepth {β x : ℝ} {i : ℕ} (hi : i < bufDepth β x) : β < seg x i := by
  by_contra hc
  push_neg at hc
  exact absurd hi (not_lt.2 (Nat.sInf_le hc))

theorem Outt_pos {x : ℝ} (hx : 0 < x) : 0 < Outt x := by
  unfold Outt
  rw [if_neg (ne_of_gt hx)]
  have : (0 : ℝ) ≤ Int.fract (1 / x) := Int.fract_nonneg _
  positivity

@[simp]
theorem costB_zero (n b : ℕ) : costB n 0 b = 0 := by rw [costB]; simp

end BlockCycleRotation

open BlockCycleRotation in
/-- **The recursion, eq. (def-mu-nu).**  Off the terminating branch the buffer
is unchanged in absolute size, hence of relative size `β/Out(x)` in the
subproblem. -/
theorem solution {β x : ℝ} (hβ : 0 < β) (hx : β < x) (hx2 : x ≤ 1 / 2) :
    psiBuf β x = 2 * x + Outt x * psiBuf (β / Outt x) (Inn x):= by
  have hx0 : 0 < x := lt_trans hβ hx
  have hOut : 0 < Outt x := Outt_pos hx0
  have hβ' : 0 < β / Outt x := by positivity
  have hIn0 : 0 ≤ Inn x := Inn_nonneg x
  have hIn : Inn x ≤ 1 / 2 := le_of_lt (Inn_lt_half x)
  have hex : ∃ i, seg (Inn x) i ≤ β / Outt x := exists_seg_le hβ' hIn0 hIn
  set T' := bufDepth (β / Outt x) (Inn x) with hT'
  -- the depth increases by one
  have hmem : seg x (T' + 1) ≤ β := by
    rw [seg_succ]
    have h := seg_bufDepth_le hex
    rw [← hT'] at h
    calc Outt x * seg (Inn x) T' ≤ Outt x * (β / Outt x) :=
          mul_le_mul_of_nonneg_left h (le_of_lt hOut)
      _ = β := by field_simp
  have hall : ∀ i, i < T' + 1 → β < seg x i := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · rw [seg_zero]; exact hx
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hipos.ne'
      have hj : j < T' := by omega
      have hgt : β / Outt x < seg (Inn x) j := lt_seg_of_lt_bufDepth (by rw [← hT']; exact hj)
      rw [seg_succ]
      calc β = Outt x * (β / Outt x) := by field_simp
        _ < Outt x * seg (Inn x) j := by
            exact mul_lt_mul_of_pos_left hgt hOut
  have hdepth : bufDepth β x = T' + 1 := by
    refine le_antisymm (Nat.sInf_le hmem) ?_
    by_contra hlt
    push_neg at hlt
    have h2 : seg x (bufDepth β x) ≤ β := seg_bufDepth_le ⟨T' + 1, hmem⟩
    exact absurd h2 (not_le.2 (hall _ hlt))
  rw [psiBuf, hdepth, psiBuf, ← hT', Finset.sum_range_succ', seg_zero,
    Finset.sum_congr rfl (fun i (_ : i ∈ Finset.range T') => seg_succ x i), ← Finset.mul_sum,
    seg_succ]
  ring
