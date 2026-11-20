-- Prove2me | solution 1 for DeletionCode.RandomHash.rules_survival_probability
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:22:49.338197+00:00
-- url     : https://prove2.me/submissions/293b885d-e5f4-403e-aa06-b7f377e69a19

import Definitions.Def_DeletionCode_IntegerTorusMap
import Definitions.Def_DeletionCode_TorusHaar
import Definitions.Def_DeletionCode_CircleUniform
import Definitions.Def_DeletionCode_RandomHash
import Theorems.Thm_DeletionCode_RandomHash_simultaneous_test_probability
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
    volume {weights : I → UnitAddCircle | ∀ j, w j ∈ surviving (weightedHash weights) Q K₀} =
      ENNReal.ofReal (2 / (Q : ℝ)) ^ Fintype.card J := by
  simpa only [surviving, Set.mem_ofPred_eq, hw, true_and] using
    simultaneous_test_probability w h Q hQ
end DeletionCode.RandomHash
