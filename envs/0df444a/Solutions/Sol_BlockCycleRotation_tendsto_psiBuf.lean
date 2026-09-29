-- Prove2me | solution 1 for BlockCycleRotation.tendsto_psiBuf
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T12:10:47.34832+00:00
-- url     : https://prove2.me/submissions/a7b1c55d-f3b0-42a4-bd73-6abd49d51886

import Definitions.Def_BlockCycleRotation_Algorithm
import Definitions.Def_BlockCycleRotation_Buffer
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Definitions.Def_BlockCycleRotation_Theorem10
import Theorems.Thm_BlockCycleRotation_Outt_le
import Theorems.Thm_BlockCycleRotation_psi_sub_psiBuf_le_linear
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

theorem psiPartial_eq_two_mul (x : ℝ) (N : ℕ) :
    psiPartial N x = 2 * ∑ i ∈ Finset.range N, seg x i := by
  rw [psiPartial, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => psiTerm_eq_two_mul_seg x i

theorem psiPartial_le_psi {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (N : ℕ) :
    psiPartial N x ≤ psi x :=
  (psi_summable hx0 hx).sum_le_tsum (Finset.range N) (fun i _ => psiTerm_nonneg hx0 hx i)

/-- **The buffer never hurts.**  `ψ_β ≤ ψ`. -/
theorem psiBuf_le_psi {β x : ℝ} (hβ : 0 < β) (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    psiBuf β x ≤ psi x := by
  have hstep : psiBuf β x ≤ psiPartial (bufDepth β x + 1) x := by
    rw [psiBuf, psiPartial_eq_two_mul, Finset.sum_range_succ]
    have := seg_nonneg hx0 hx (bufDepth β x)
    linarith
  exact le_trans hstep (psiPartial_le_psi hx0 hx _)

@[simp]
theorem costB_zero (n b : ℕ) : costB n 0 b = 0 := by rw [costB]; simp

end BlockCycleRotation

open BlockCycleRotation in
/-- **`ψ_β → ψ` as `β → 0⁺`.** -/
theorem solution {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    Filter.Tendsto (fun β => psiBuf β x) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (psi x)):= by
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
