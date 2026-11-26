-- Prove2me | solution 1 for Erdos266.blockAnchor_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:49:47.510807+00:00
-- url     : https://prove2.me/submissions/7ba0354e-4b33-4157-a0ef-c7cd7ef595af

module
public import Definitions.Def_Erdos266_LatticeLemma
public import Definitions.Def_Erdos266_Growth
public import Definitions.Def_Erdos266_Algorithm
public import Theorems.Thm_Erdos266_dOf_le
public import Theorems.Thm_Erdos266_sample_ge
public import Theorems.Thm_Erdos266_f_le


set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset
namespace Erdos266
theorem _root_.solution {i l : ℕ} (h2i : (2 * i : ℝ) ≤ (bigN l : ℝ)) (hi : 1 ≤ i)
    (hN2 : (2 : ℝ) ≤ (bigN l : ℝ)) :
    blockAnchor i l ≤ (l : ℝ) * (2 / (bigN l : ℝ)) := by
  have hNpos : (0:ℝ) < (bigN l : ℝ) := by linarith
  have hterm : ∀ j ∈ range (dOf l), f i (((j + 1) * bigN l : ℕ) : ℝ) ≤ 2 / (bigN l : ℝ) := by
    intro j _
    have h1 : (2 * i : ℝ) ≤ (((j + 1) * bigN l : ℕ) : ℝ) := le_trans h2i sample_ge
    have h0 : (0:ℝ) < (((j + 1) * bigN l : ℕ) : ℝ) := lt_of_lt_of_le hNpos sample_ge
    have h2 := f_le h1 h0
    have h3 : (2 / (((j + 1) * bigN l : ℕ) : ℝ)) ^ i ≤ (2 / (bigN l : ℝ)) ^ i := by
      apply pow_le_pow_left₀ (by positivity)
      apply div_le_div_of_nonneg_left (by norm_num) hNpos sample_ge
    have h4 : (2 / (bigN l : ℝ)) ^ i ≤ (2 / (bigN l : ℝ)) ^ 1 := by
      apply pow_le_pow_of_le_one (by positivity) ?_ hi
      rw [div_le_one hNpos]
      exact hN2
    rw [pow_one] at h4
    exact h2.trans (h3.trans h4)
  calc blockAnchor i l ≤ ∑ _j ∈ range (dOf l), (2 / (bigN l : ℝ)) := sum_le_sum hterm
  _ = (dOf l : ℝ) * (2 / (bigN l : ℝ)) := by
      rw [sum_const, card_range, nsmul_eq_mul]
  _ ≤ (l : ℝ) * (2 / (bigN l : ℝ)) := by
      have h5 : (dOf l : ℝ) ≤ (l : ℝ) := by exact_mod_cast dOf_le l
      exact mul_le_mul_of_nonneg_right h5 (by positivity)
end Erdos266
