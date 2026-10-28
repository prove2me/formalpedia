-- Prove2me | solution 1 for D1Bound5.ordinaryLog10_unit_parameters
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:22:25.175762+00:00
-- url     : https://prove2.me/submissions/df01792b-71da-4d88-8880-38c46a4500d3

import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Definitions.Def_D1Bound5_OrdinaryLog10_Definitions
import Theorems.Thm_D1Bound5_ordinaryLog10_lt_of_pow_lt
import Theorems.Thm_D1Bound5_ordinaryLog10_mul

section
namespace D1Bound5





















theorem _root_.solution :
    ordinaryLog10 42 < (163/100 : ℝ) ∧
    -(2/5 : ℝ) < ordinaryLog10 (2/5) ∧
    ordinaryLog10 253 < (241/100 : ℝ) := by
  have h42 := ordinaryLog10_lt_of_pow_lt 42 163 100 (by norm_num) (by norm_num)
  have h52 := ordinaryLog10_lt_of_pow_lt (5/2) 2 5 (by norm_num) (by norm_num)
  have h253 := ordinaryLog10_lt_of_pow_lt 253 241 100 (by norm_num) (by norm_num)
  have hrec : ordinaryLog10 (2/5)+ordinaryLog10 (5/2) = 0 := by
    rw [← ordinaryLog10_mul (2/5) (5/2) (by norm_num) (by norm_num)]
    norm_num [ordinaryLog10]
  norm_num at h42 h52 h253
  exact ⟨by linarith only [h42],by linarith only [h52,hrec],by linarith only [h253]⟩

end D1Bound5
end
