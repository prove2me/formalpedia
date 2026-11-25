-- Prove2me | solution 1 for Erdos684.log_obstructionModulus_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:56:21.192009+00:00
-- url     : https://prove2.me/submissions/023dbdcf-ce79-4e4f-aaca-5d17a9faa002

module
public import Definitions.Def_Erdos684_Finite
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Definitions.Def_Erdos684_Lower

set_option autoImplicit false
@[expose] public section
public section
open Filter Real
open scoped Topology
open Erdos684
namespace Erdos684
theorem _root_.solution (K : ℕ) : log (obstructionModulus K : ℝ) ≤ 8 * K := by
  have hpsi := Chebyshev.psi_le_const_mul_self (x := (K : ℝ)) (Nat.cast_nonneg K)
  have htheta := Chebyshev.theta_le_log4_mul_x (x := (K : ℝ)) (Nat.cast_nonneg K)
  have hthetaeq : Chebyshev.theta (K : ℝ) = log (primorial K : ℝ) := by
    simpa using Chebyshev.theta_eq_log_primorial (K : ℝ)
  have hpsieq := Chebyshev.psi_eq_log_lcmUpto K
  have hlog4 : log (4 : ℝ) ≤ 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hlog2 ⊢
    linarith
  rw [obstructionModulus, Nat.cast_mul,
    Real.log_mul (Nat.cast_ne_zero.mpr (Nat.lcmUpto_ne_zero K))
      (Nat.cast_ne_zero.mpr (primorial_ne_zero K))]
  rw [← hthetaeq, ← hpsieq]
  nlinarith [Nat.cast_nonneg (α := ℝ) K]
end Erdos684
