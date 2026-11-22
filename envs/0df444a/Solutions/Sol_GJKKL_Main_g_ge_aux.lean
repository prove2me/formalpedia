-- Prove2me | solution 1 for GJKKL.Main.g_ge_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:19:49.858484+00:00
-- url     : https://prove2.me/submissions/1cf278ba-da73-4374-9c43-2827d71aca95

module
public import Definitions.Def_GJKKL_Trajectory_Tracking
public import Definitions.Def_GJKKL_Trajectory_Functions
public import Definitions.Def_GJKKL_Greedy_VertexCount
public import Definitions.Def_GJKKL_Main_Parameters
public import Theorems.Thm_GJKKL_Dv_nil
public import Theorems.Thm_GJKKL_History_aliveBefore_cons
public import Theorems.Thm_GJKKL_History_aliveBefore_nil
public import Theorems.Thm_GJKKL_History_expect_zero
public import Theorems.Thm_GJKKL_History_weight_cons
public import Theorems.Thm_GJKKL_History_weight_nil
public import Theorems.Thm_GJKKL_Trajectory_le_pow_sub_pow
public import Theorems.Thm_GJKKL_Trajectory_pow_sub_pow_le
public import Theorems.Thm_GJKKL_isGreedySeq_cons
public import Theorems.Thm_GJKKL_isGreedySeq_nil
attribute [local simp] GJKKL.Dv_nil
attribute [local simp] GJKKL.History.aliveBefore_cons
attribute [local simp] GJKKL.History.aliveBefore_nil
attribute [local simp] GJKKL.History.expect_zero
attribute [local simp] GJKKL.History.weight_cons
attribute [local simp] GJKKL.History.weight_nil
attribute [local simp] GJKKL.isGreedySeq_cons
attribute [local simp] GJKKL.isGreedySeq_nil



set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Main
open Finset Real Pseudorandom GJKKL.Trajectory
variable {a μ x y : ℝ}
namespace GJKKL.Main
theorem _root_.solution {x y a d : ℝ} (j : ℕ) (hy : 0 ≤ y) (hxy : y ≤ x) (hx : 0 < x) (ha : 0 < a)
    (hd : 0 ≤ d) (hxy' : x - y = 1 / a) :
    ((j : ℝ) + 1) * (d * x ^ (j + 1)) / (a * x) -
        ((j : ℝ) + 1) * j * (d * x ^ (j + 1)) / (a * x) ^ 2 ≤
      d * x ^ (j + 1) - d * y ^ (j + 1) := by
  have hx0 : x ≠ 0 := hx.ne'
  have ha0 : a ≠ 0 := ha.ne'
  have hlow := le_pow_sub_pow hy hxy j
  rw [hxy'] at hlow
  rcases j with _ | i
  · -- `j = 0`
    simp only [Nat.cast_zero, zero_add, pow_one, mul_zero, zero_mul, zero_div, sub_zero, one_mul]
    rw [mul_div_mul_right _ _ hx0]
    have : d * x - d * y = d * (1 / a) := by rw [← hxy']; ring
    rw [this, mul_one_div]
  · -- `j = i + 1`
    have hyi : x ^ (i + 1) - ((i : ℝ) + 1) * x ^ i * (1 / a) ≤ y ^ (i + 1) := by
      have := pow_sub_pow_le hy hxy i
      rw [hxy'] at this
      linarith
    have e : (((i + 1 : ℕ) : ℝ) + 1) * (d * x ^ (i + 1 + 1)) / (a * x) -
        (((i + 1 : ℕ) : ℝ) + 1) * ((i + 1 : ℕ) : ℝ) * (d * x ^ (i + 1 + 1)) / (a * x) ^ 2 =
        (((i : ℝ) + 2) * d * (1 / a)) * (x ^ (i + 1) - ((i : ℝ) + 1) * x ^ i * (1 / a)) := by
      push_cast
      first | (field_simp; ring) | field_simp
    have hc : 0 ≤ ((i : ℝ) + 2) * d * (1 / a) := by positivity
    have h1 := mul_le_mul_of_nonneg_left hyi hc
    have h2 : ((i : ℝ) + 2) * d * (1 / a) * y ^ (i + 1) ≤
        d * x ^ (i + 1 + 1) - d * y ^ (i + 1 + 1) := by
      have := mul_le_mul_of_nonneg_left hlow hd
      push_cast at this
      linarith
    linarith [e, h1, h2]
end GJKKL.Main
