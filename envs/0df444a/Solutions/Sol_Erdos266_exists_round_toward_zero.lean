-- Prove2me | solution 1 for Erdos266.exists_round_toward_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:40:50.395967+00:00
-- url     : https://prove2.me/submissions/43f254f3-a2f7-464d-83d1-893fd32fe90f

module
public import Definitions.Def_Erdos266_SlopeLemma
public import Definitions.Def_Erdos266_LatticeLemma

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Matrix
namespace Erdos266
theorem _root_.solution (u : ℝ) {c : ℝ} (hc : 0 < c) :
    ∃ z : ℤ, |c * z - u| ≤ c ∧ c * |(z : ℝ)| ≤ |u| := by
  rcases le_or_gt 0 u with hu | hu
  · refine ⟨⌊u / c⌋, ?_, ?_⟩
    · have h1 : (⌊u / c⌋ : ℝ) ≤ u / c := Int.floor_le _
      have h2 : u / c < ⌊u / c⌋ + 1 := Int.lt_floor_add_one _
      have h1' : c * (⌊u / c⌋ : ℝ) ≤ u := by
        have := mul_le_mul_of_nonneg_left h1 hc.le
        rwa [mul_div_cancel₀ u hc.ne'] at this
      have h2' : u < c * (⌊u / c⌋ : ℝ) + c := by
        have := mul_lt_mul_of_pos_left h2 hc
        rw [mul_add, mul_one, mul_div_cancel₀ u hc.ne'] at this
        linarith
      rw [abs_le]
      constructor <;> linarith
    · have h0 : (0 : ℤ) ≤ ⌊u / c⌋ := Int.floor_nonneg.mpr (div_nonneg hu hc.le)
      have h1 : (⌊u / c⌋ : ℝ) ≤ u / c := Int.floor_le _
      have h1' : c * (⌊u / c⌋ : ℝ) ≤ u := by
        have := mul_le_mul_of_nonneg_left h1 hc.le
        rwa [mul_div_cancel₀ u hc.ne'] at this
      rw [abs_of_nonneg (show (0:ℝ) ≤ (⌊u / c⌋ : ℝ) by exact_mod_cast h0),
        abs_of_nonneg hu]
      exact h1'
  · refine ⟨⌈u / c⌉, ?_, ?_⟩
    · have h1 : (u / c : ℝ) ≤ ⌈u / c⌉ := Int.le_ceil _
      have h2 : (⌈u / c⌉ : ℝ) < u / c + 1 := Int.ceil_lt_add_one _
      have h1' : u ≤ c * (⌈u / c⌉ : ℝ) := by
        have := mul_le_mul_of_nonneg_left h1 hc.le
        rwa [mul_div_cancel₀ u hc.ne'] at this
      have h2' : c * (⌈u / c⌉ : ℝ) < u + c := by
        have := mul_lt_mul_of_pos_left h2 hc
        rw [mul_add, mul_one, mul_div_cancel₀ u hc.ne'] at this
        linarith
      rw [abs_le]
      constructor <;> linarith
    · have h0 : ⌈u / c⌉ ≤ 0 :=
        Int.ceil_nonpos.mpr (div_nonpos_of_nonpos_of_nonneg hu.le hc.le)
      have h1 : (u / c : ℝ) ≤ ⌈u / c⌉ := Int.le_ceil _
      have h1' : u ≤ c * (⌈u / c⌉ : ℝ) := by
        have := mul_le_mul_of_nonneg_left h1 hc.le
        rwa [mul_div_cancel₀ u hc.ne'] at this
      rw [abs_of_nonpos (show (⌈u / c⌉ : ℝ) ≤ 0 by exact_mod_cast h0),
        abs_of_neg hu]
      linarith [mul_le_mul_of_nonneg_left
        (show -(⌈u/c⌉ : ℝ) ≤ -(⌈u/c⌉ : ℝ) from le_rfl) hc.le]
end Erdos266
