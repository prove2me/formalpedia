-- Prove2me | solution 1 for BitDFT.scalar_product_width
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T17:59:46.723991+00:00
-- url     : https://prove2.me/submissions/21e76042-7080-43bf-bada-266227114dbf

import Definitions.Def_BitDFT_Numerics
import Mathlib.Tactic
open BitDFT IntMul

/-- Exact product fits the scaler's advertised magnitude width. -/
theorem solution (n q : ℕ) (z : ℤ) (hz : z.natAbs ≤ 2^q) :
    ((n : ℤ)*z).natAbs < 2^(q+lg n+1) ∧
    (0 < n → (((n : ℤ)*z < 0) ↔ z < 0)) := by
  have hn : n ≤ 2^lg n := (Nat.le_pow_clog (by decide : 1<2) n).trans
    (Nat.pow_le_pow_right (by decide : 0<2) (le_max_left _ _))
  constructor
  · rw [Int.natAbs_mul,Int.natAbs_natCast]
    have hprod : n*z.natAbs ≤ 2^(q+lg n) := by
      calc
        n*z.natAbs ≤ 2^lg n*2^q := Nat.mul_le_mul hn hz
        _ = 2^(q+lg n) := by rw [pow_add,Nat.mul_comm]
    have hp := Nat.two_pow_pos (q+lg n)
    rw [pow_succ]
    omega
  · intro hnpos
    have hnz : (0 : ℤ) < n := by exact_mod_cast hnpos
    constructor <;> intro h <;> nlinarith
