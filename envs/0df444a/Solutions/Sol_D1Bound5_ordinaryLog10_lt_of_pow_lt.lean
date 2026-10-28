-- Prove2me | solution 1 for D1Bound5.ordinaryLog10_lt_of_pow_lt
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:00:38.165342+00:00
-- url     : https://prove2.me/submissions/cf8ce861-9445-484b-a1e7-4be0046f0f8a

import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Definitions.Def_D1Bound5_OrdinaryLog10_Definitions
import Theorems.Thm_D1Bound5_ordinaryLog10_pow
import Theorems.Thm_D1Bound5_ordinaryLog10_strictMono
import Theorems.Thm_D1Bound5_ordinaryLog10_ten

section
namespace D1Bound5

















/-- Exact integer-power comparisons certify all decimal logarithm
parameters; no decimal approximation or external numerical oracle is used. -/
theorem _root_.solution (x : ℝ) (m n : ℕ)
    (hx : 0 < x) (hpow : x^n < (10 : ℝ)^m) :
    (n : ℝ)*ordinaryLog10 x < m := by
  have h := ordinaryLog10_strictMono (pow_pos hx n) hpow
  simpa only [ordinaryLog10_pow,ordinaryLog10_ten,mul_one] using h





end D1Bound5
end
