-- Prove2me | solution 1 for DeletionCode.RandomHash.real_rules_survival_probability_toReal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:24:35.347074+00:00
-- url     : https://prove2.me/submissions/39554882-f747-4c59-a7ab-1ba6b065c29e

import Definitions.Def_DeletionCode_IntegerTorusMap
import Definitions.Def_DeletionCode_TorusHaar
import Definitions.Def_DeletionCode_CircleUniform
import Definitions.Def_DeletionCode_RandomHash
import Theorems.Thm_DeletionCode_RandomHash_real_rules_survival_probability

set_option autoImplicit true
open DeletionCode DeletionCode.RandomHash
open MeasureTheory ProbabilityTheory CircleHash IntegerTorusMap CircleUniform
open scoped BigOperators
variable {I J : Type*} [Fintype I] [Fintype J]
namespace DeletionCode.RandomHash
theorem _root_.solution (w : J → I → ℤ)
    (h : LinearIndependent ℚ (fun j i => (w j i : ℚ)))
    (K₀ : Set (I → ℤ)) (hw : ∀ j, w j ∈ K₀) (Q : ℕ) (hQ : 2 ≤ Q) :
    (realWeights I {weights | ∀ j, w j ∈ surviving (realWeightedHash weights) Q K₀}).toReal =
      (2 / (Q : ℝ)) ^ Fintype.card J := by
  rw [real_rules_survival_probability w h K₀ hw Q hQ, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (div_nonneg (by norm_num) (Nat.cast_nonneg Q))]
end DeletionCode.RandomHash
