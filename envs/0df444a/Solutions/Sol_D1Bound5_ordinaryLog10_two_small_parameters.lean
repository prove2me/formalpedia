-- Prove2me | solution 1 for D1Bound5.ordinaryLog10_two_small_parameters
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:54:05.734396+00:00
-- url     : https://prove2.me/submissions/1295b68b-96b5-414e-984c-e2e0c6021f72

import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Definitions.Def_D1Bound5_OrdinaryLog10_Definitions
import Theorems.Thm_D1Bound5_ordinaryLog10_lt_of_pow_lt
import Theorems.Thm_D1Bound5_ordinaryLog10_mul

section
namespace D1Bound5













theorem _root_.solution :
    ordinaryLog10 1134 < (31/10 : ℝ) ∧
      -(9/10 : ℝ) < ordinaryLog10 (2/15) ∧
      ordinaryLog10 2277 < (17/5 : ℝ) := by
  have hH := ordinaryLog10_lt_of_pow_lt 1134 31 10 (by norm_num) (by norm_num)
  have hR := ordinaryLog10_lt_of_pow_lt (15/2) 9 10 (by norm_num) (by norm_num)
  have hU := ordinaryLog10_lt_of_pow_lt 2277 17 5 (by norm_num) (by norm_num)
  have hinv : ordinaryLog10 (2/15)+ordinaryLog10 (15/2) = 0 := by
    rw [← ordinaryLog10_mul (2/15) (15/2) (by norm_num) (by norm_num)]
    norm_num [ordinaryLog10]
  norm_num at hH hR hU
  exact ⟨by linarith only [hH],by linarith only [hR,hinv],by linarith only [hU]⟩

end D1Bound5
end
