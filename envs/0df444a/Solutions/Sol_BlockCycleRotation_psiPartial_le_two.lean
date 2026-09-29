-- Prove2me | solution 1 for BlockCycleRotation.psiPartial_le_two
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T12:01:19.931076+00:00
-- url     : https://prove2.me/submissions/9dc5cce2-885f-4302-9fb0-a4f4b73e8370

import Definitions.Def_BlockCycleRotation_Algorithm
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Definitions.Def_BlockCycleRotation_Theorem10
import Theorems.Thm_BlockCycleRotation_add_Outt_le_one
import Mathlib

open Finset Real Filter Topology MeasureTheory BoxIntegral
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

theorem psiTerm_succ (x : ℝ) (i : ℕ) : psiTerm x (i + 1) = Outt x * psiTerm (Inn x) i := by
  unfold psiTerm
  rw [Finset.prod_range_succ']
  have hit : ∀ m : ℕ, Inn^[m] (Inn x) = Inn^[m + 1] x := by
    intro m
    rw [← Function.iterate_succ_apply]
  have hprod : ∏ m ∈ Finset.range i, Outt (Inn^[m] (Inn x))
      = ∏ m ∈ Finset.range i, Outt (Inn^[m + 1] x) :=
    Finset.prod_congr rfl fun m _ => by rw [hit]
  rw [hprod, hit i, Function.iterate_zero_apply]
  ring

end BlockCycleRotation

open BlockCycleRotation in
/-- **`ψ_N ≤ 2` for every partial sum**, by induction along the recursion. -/
theorem solution : ∀ (N : ℕ) {x : ℝ}, 0 ≤ x → x ≤ 1 / 2 → psiPartial N x ≤ 2:= by
  intro N
  induction N with
  | zero =>
    intro x _ _
    simp [psiPartial]
  | succ M ih =>
    intro x hx0 hx
    have hIn0 : 0 ≤ Inn x := Inn_nonneg x
    have hIn : Inn x ≤ 1 / 2 := le_of_lt (Inn_lt_half x)
    have hrec : psiPartial (M + 1) x = 2 * x + Outt x * psiPartial M (Inn x) := by
      rw [psiPartial, psiPartial, Finset.sum_range_succ']
      have h0 : psiTerm x 0 = 2 * x := by
        unfold psiTerm
        simp
      rw [h0, Finset.sum_congr rfl (fun i (_ : i ∈ Finset.range M) => psiTerm_succ x i),
        ← Finset.mul_sum]
      ring
    have hIH := ih hIn0 hIn
    have hOut : 0 ≤ Outt x := Outt_nonneg hx0
    have hkey := add_Outt_le_one hx0 hx
    rw [hrec]
    nlinarith
