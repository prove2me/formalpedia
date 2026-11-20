-- Prove2me | solution 1 for DeletionCode.RandomHash.real_rules_survival_probability
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:23:49.124248+00:00
-- url     : https://prove2.me/submissions/47ff004e-136a-47b2-acc8-fb3abb541843

import Definitions.Def_DeletionCode_IntegerTorusMap
import Definitions.Def_DeletionCode_TorusHaar
import Definitions.Def_DeletionCode_CircleUniform
import Definitions.Def_DeletionCode_RandomHash
import Theorems.Thm_DeletionCode_RandomHash_real_simultaneous_test_probability
import Theorems.Thm_DeletionCode_IntegerTorusMap_jointHash_apply
attribute [local simp] DeletionCode.IntegerTorusMap.jointHash_apply



set_option autoImplicit true
open DeletionCode DeletionCode.RandomHash
open MeasureTheory ProbabilityTheory CircleHash IntegerTorusMap CircleUniform
open scoped BigOperators
variable {I J : Type*} [Fintype I] [Fintype J]
namespace DeletionCode.RandomHash
theorem _root_.solution (w : J → I → ℤ)
    (h : LinearIndependent ℚ (fun j i => (w j i : ℚ)))
    (K₀ : Set (I → ℤ)) (hw : ∀ j, w j ∈ K₀) (Q : ℕ) (hQ : 2 ≤ Q) :
    realWeights I {weights | ∀ j, w j ∈ surviving (realWeightedHash weights) Q K₀} =
      ENNReal.ofReal (2 / (Q : ℝ)) ^ Fintype.card J := by
  simpa only [surviving, Set.mem_ofPred_eq, hw, true_and] using
    real_simultaneous_test_probability w h Q hQ
end DeletionCode.RandomHash
