-- Prove2me | solution 1 for DerivativeChainPrivate.nested_interval_budget
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T20:13:50.272351+00:00
-- url     : https://prove2.me/submissions/86fd7a6a-dd7e-4d13-baf6-240c231e2356

import Mathlib
namespace DerivativeChainPrivate
end DerivativeChainPrivate
open DerivativeChainPrivate Filter Topology Polynomial
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false


open DerivativeChainPrivate in
theorem solution (a b A B : ℝ)
    (ha : 0 ≤ a) (haA : a ≤ A) (hb : 0 ≤ b) (hbB : b ≤ B)
    (hAB : 0 < A + B) :
    2 * (A * B - a * b) / (A + B) ≤
      2 * (Real.sqrt (A * B) - Real.sqrt (a * b)) := by
  have hA : 0 ≤ A := ha.trans haA
  have hB : 0 ≤ B := hb.trans hbB
  have hab_le : a * b ≤ A * B := mul_le_mul haA hbB hb hA
  have hsqrt_le : Real.sqrt (a * b) ≤ Real.sqrt (A * B) :=
    Real.sqrt_le_sqrt hab_le
  have hamgm : Real.sqrt (A * B) ≤ (A + B) / 2 := by
    apply (Real.sqrt_le_left (by linarith : 0 ≤ (A + B) / 2)).2
    nlinarith [sq_nonneg (A - B)]
  have hsum : Real.sqrt (A * B) + Real.sqrt (a * b) ≤ A + B := by
    linarith
  have hgap : 0 ≤ Real.sqrt (A * B) - Real.sqrt (a * b) :=
    sub_nonneg.mpr hsqrt_le
  have hmul := mul_le_mul_of_nonneg_left hsum hgap
  have hsquareAB := Real.sq_sqrt (mul_nonneg hA hB)
  have hsquareab := Real.sq_sqrt (mul_nonneg ha hb)
  apply (div_le_iff₀ hAB).2
  nlinarith [hmul]
