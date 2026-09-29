-- Prove2me | solution 1 for BlockCycleRotation.muCost_le_three_mul
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T12:12:51.227489+00:00
-- url     : https://prove2.me/submissions/7e8dc69e-c891-4bb5-91e6-99dacb81d00e

import Definitions.Def_BlockCycleRotation_Algorithm
import Definitions.Def_BlockCycleRotation_Buffer
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Definitions.Def_BlockCycleRotation_Theorem10
import Theorems.Thm_BlockCycleRotation_Outt_le
import Theorems.Thm_BlockCycleRotation_psiPartial_le_two
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

/-- **`ψ ≤ 2`**, the paper's `μ(N,ℓ) ≤ 3N` in relative form. -/
theorem psi_le_two {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) : psi x ≤ 2 := by
  refine Real.tsum_le_of_sum_le (psiTerm_nonneg hx0 hx) fun s => ?_
  obtain ⟨N, hN⟩ : ∃ N, s ⊆ Finset.range N :=
    ⟨s.sup id + 1, fun i hi => Finset.mem_range.2 (by
      have := Finset.le_sup (f := id) hi
      simp only [id] at this
      omega)⟩
  calc ∑ i ∈ s, psiTerm x i ≤ ∑ i ∈ Finset.range N, psiTerm x i :=
        Finset.sum_le_sum_of_subset_of_nonneg hN (fun i _ _ => psiTerm_nonneg hx0 hx i)
    _ ≤ 2 := psiPartial_le_two N hx0 hx

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
/-- **The Observation `μ(N,ℓ,β) ≤ 3N`.** -/
theorem solution {N l b : ℝ} (hN : 0 < N) (hb : 0 < b) (hl0 : 0 ≤ l)
    (hl : 2 * l ≤ N) : muCost N l b ≤ 3 * N:= by
  have hx0 : 0 ≤ l / N := by positivity
  have hx : l / N ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hN (by norm_num)]
    linarith
  have hbN : 0 < b / N := by positivity
  have h1 : psiBuf (b / N) (l / N) ≤ psi (l / N) := psiBuf_le_psi hbN hx0 hx
  have h2 : psi (l / N) ≤ 2 := psi_le_two hx0 hx
  unfold muCost
  nlinarith
