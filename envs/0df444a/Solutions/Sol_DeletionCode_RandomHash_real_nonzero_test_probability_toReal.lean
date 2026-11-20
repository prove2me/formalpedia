-- Prove2me | solution 1 for DeletionCode.RandomHash.real_nonzero_test_probability_toReal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:24:35.882826+00:00
-- url     : https://prove2.me/submissions/889b33a1-cf5a-4f2c-b538-eb136e4fbcac

import Definitions.Def_DeletionCode_IntegerTorusMap
import Definitions.Def_DeletionCode_TorusHaar
import Definitions.Def_DeletionCode_CircleUniform
import Definitions.Def_DeletionCode_RandomHash
import Theorems.Thm_DeletionCode_RandomHash_real_nonzero_test_probability

set_option autoImplicit true
open DeletionCode DeletionCode.RandomHash
open MeasureTheory ProbabilityTheory CircleHash IntegerTorusMap CircleUniform
open scoped BigOperators
variable {I J : Type*} [Fintype I] [Fintype J]
namespace DeletionCode.RandomHash
theorem _root_.solution (w : I → ℤ) (hw : w ≠ 0) (Q : ℕ) (hQ : 2 ≤ Q) :
    (realWeights I {weights | ‖realWeightedHash weights w‖ < 1 / (Q : ℝ)}).toReal =
      2 / (Q : ℝ) := by
  rw [real_nonzero_test_probability w hw Q hQ,
    ENNReal.toReal_ofReal (div_nonneg (by norm_num) (Nat.cast_nonneg Q))]
end DeletionCode.RandomHash
