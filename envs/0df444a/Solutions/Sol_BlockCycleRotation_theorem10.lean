-- Prove2me | solution 1 for BlockCycleRotation.theorem10
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T12:04:03.892764+00:00
-- url     : https://prove2.me/submissions/47350304-eabd-492d-aa4c-b1a09d58f1c8

import Definitions.Def_BlockCycleRotation_Algorithm
import Definitions.Def_BlockCycleRotation_Average
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Definitions.Def_BlockCycleRotation_Theorem10
import Theorems.Thm_BlockCycleRotation_theorem10_unit
import Theorems.Thm_BlockCycleRotation_integral_fCost_split
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

theorem fBar_eq_fCost {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1) : fBar x = fCost x := by
  unfold fBar; rw [if_pos ⟨hx0, hx⟩]

theorem uIoc_subset_Icc {a b : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    ∀ x ∈ Set.uIoc a b, 0 ≤ x ∧ x ≤ 1 := by
  intro x hx
  rw [Set.uIoc, Set.mem_Ioc] at hx
  constructor
  · exact le_of_lt (lt_of_le_of_lt (le_inf ha hb) hx.1)
  · exact le_trans hx.2 (sup_le ha1 hb1)

theorem integral_fBar_eq_fCost {a b : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    ∫ x in a..b, fBar x = ∫ x in a..b, fCost x := by
  refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun x hx => ?_)
  obtain ⟨h0, h1⟩ := uIoc_subset_Icc ha ha1 hb hb1 x hx
  exact fBar_eq_fCost h0 h1

end BlockCycleRotation

open BlockCycleRotation in
/-- **Theorem 10.**  `avgCost n / n → 2∫₀^{1/2} f`. -/
theorem solution :
    Tendsto (fun n : ℕ => avgCost n / (n : ℝ)) atTop
      (𝓝 (2 * ∫ x in (0 : ℝ)..(1 / 2), fCost x)):= by
  have h := theorem10_unit
  rw [integral_fBar_eq_fCost (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    integral_fCost_split] at h
  exact h
