-- Prove2me | solution 1 for FirstPassageLinearTransport.sharp_entropy_tail_exact_rate_Icc_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:00:21.656693+00:00
-- url     : https://prove2.me/submissions/d463d752-910e-478e-8168-8fe0acfab9dc

import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Order.Interval.Finset.SuccPred
import Definitions.Def_FirstPassageLinearTransport_TerminalTail
import Definitions.Def_FirstPassageLinearTransport_MovingSharpTail
import Theorems.Thm_FirstPassageLinearTransport_offset_exp_Icc_le
import Theorems.Thm_FirstPassageLinearTransport_rank_over_sqrt_shift_le

set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped BigOperators Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {b₀ b : ℝ} (hb₀ : 0 < b₀) (hb₀b : b₀ ≤ b)
    {L U : ℕ} (hL : 2 ≤ L) (hLU : L ≤ U) :
    ∑ q ∈ Finset.Icc L U,
        ((q + 1 : ℕ) : ℝ) / Real.sqrt ((q - 1 : ℕ) : ℝ) *
          Real.exp (-(b * ((q - 1 : ℕ) : ℝ))) ≤
      3 * Real.sqrt L * Real.exp (-(b * ((L - 1 : ℕ) : ℝ))) *
        weightedTailConstant b₀ (b₀ / 2) := by
  have hterm : ∀ q ∈ Finset.Icc L U,
      ((q + 1 : ℕ) : ℝ) / Real.sqrt ((q - 1 : ℕ) : ℝ) *
          Real.exp (-(b * ((q - 1 : ℕ) : ℝ))) ≤
        (3 * Real.sqrt L * Real.exp (-(b * ((L - 1 : ℕ) : ℝ)))) *
          (((q - L + 1 : ℕ) : ℝ) *
            Real.exp (-(b * ((q - L : ℕ) : ℝ)))) := by
    intro q hq
    have hLq : L ≤ q := (Finset.mem_Icc.mp hq).1
    have hq1 : 1 ≤ q := le_trans (by norm_num) (hL.trans hLq)
    have hL1 : 1 ≤ L := le_trans (by norm_num) hL
    have hexpSplit :
        Real.exp (-(b * ((q - 1 : ℕ) : ℝ))) =
          Real.exp (-(b * ((L - 1 : ℕ) : ℝ))) *
            Real.exp (-(b * ((q - L : ℕ) : ℝ))) := by
      rw [Nat.cast_sub hq1, Nat.cast_sub hL1]
      have hcastSub : ((q - L : ℕ) : ℝ) = (q : ℝ) - (L : ℝ) := by
        rw [Nat.cast_sub hLq]
      rw [hcastSub, ← Real.exp_add]
      congr 1
      ring
    rw [hexpSplit]
    have hrank := rank_over_sqrt_shift_le hL hLq
    calc
      ((q + 1 : ℕ) : ℝ) / Real.sqrt ((q - 1 : ℕ) : ℝ) *
          (Real.exp (-(b * ((L - 1 : ℕ) : ℝ))) *
            Real.exp (-(b * ((q - L : ℕ) : ℝ)))) ≤
        (3 * Real.sqrt L * ((q - L + 1 : ℕ) : ℝ)) *
          (Real.exp (-(b * ((L - 1 : ℕ) : ℝ))) *
            Real.exp (-(b * ((q - L : ℕ) : ℝ)))) := by
          gcongr
      _ = (3 * Real.sqrt L *
            Real.exp (-(b * ((L - 1 : ℕ) : ℝ)))) *
          (((q - L + 1 : ℕ) : ℝ) *
            Real.exp (-(b * ((q - L : ℕ) : ℝ)))) := by ring
  have hcoef0 : 0 ≤
      3 * Real.sqrt L * Real.exp (-(b * ((L - 1 : ℕ) : ℝ))) := by
    positivity
  calc
    ∑ q ∈ Finset.Icc L U,
        ((q + 1 : ℕ) : ℝ) / Real.sqrt ((q - 1 : ℕ) : ℝ) *
          Real.exp (-(b * ((q - 1 : ℕ) : ℝ))) ≤
      ∑ q ∈ Finset.Icc L U,
        (3 * Real.sqrt L * Real.exp (-(b * ((L - 1 : ℕ) : ℝ)))) *
          (((q - L + 1 : ℕ) : ℝ) *
            Real.exp (-(b * ((q - L : ℕ) : ℝ)))) :=
        Finset.sum_le_sum hterm
    _ = (3 * Real.sqrt L *
          Real.exp (-(b * ((L - 1 : ℕ) : ℝ)))) *
        ∑ q ∈ Finset.Icc L U,
          (((q - L + 1 : ℕ) : ℝ) *
            Real.exp (-(b * ((q - L : ℕ) : ℝ)))) := by
      rw [Finset.mul_sum]
    _ ≤ (3 * Real.sqrt L *
          Real.exp (-(b * ((L - 1 : ℕ) : ℝ)))) *
        weightedTailConstant b₀ (b₀ / 2) := by
      exact mul_le_mul_of_nonneg_left
        (offset_exp_Icc_le hb₀ hb₀b hLU) hcoef0
end FirstPassageLinearTransport
