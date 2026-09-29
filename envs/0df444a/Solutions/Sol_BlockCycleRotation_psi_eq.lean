-- Prove2me | solution 1 for BlockCycleRotation.psi_eq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:57:54.894064+00:00
-- url     : https://prove2.me/submissions/a8fd5f08-fc8e-4ada-bbef-982adb573670

import Definitions.Def_BlockCycleRotation_Algorithm
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Definitions.Def_BlockCycleRotation_Theorem10
import Theorems.Thm_BlockCycleRotation_Outt_le
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

end BlockCycleRotation

open BlockCycleRotation in
/-- **The functional equation.**  `ψ(x) = 2x + Out(x)·ψ(In(x))`. -/
theorem solution {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    psi x = 2 * x + Outt x * psi (Inn x):= by
  have hIn0 : 0 ≤ Inn x := Inn_nonneg x
  have hIn : Inn x ≤ 1 / 2 := le_of_lt (Inn_lt_half x)
  have hshift : ∀ i : ℕ, psiTerm x (i + 1) = Outt x * psiTerm (Inn x) i := by
    intro i
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
  have hsum1 : Summable (fun i => psiTerm x (i + 1)) :=
    (summable_nat_add_iff 1).2 (psi_summable hx0 hx)
  rw [psi, tsum_eq_zero_add' hsum1]
  have h0 : psiTerm x 0 = 2 * x := by
    unfold psiTerm
    simp
  rw [h0]
  congr 1
  rw [tsum_congr hshift, tsum_mul_left, psi]
