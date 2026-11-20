-- Prove2me | solution 1 for DeletionCode.RandomHash.real_simultaneous_test_probability
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:22:59.557464+00:00
-- url     : https://prove2.me/submissions/bb3763e2-aa4b-4e74-b58c-1e2ffd83324b

import Definitions.Def_DeletionCode_IntegerTorusMap
import Definitions.Def_DeletionCode_TorusHaar
import Definitions.Def_DeletionCode_CircleUniform
import Definitions.Def_DeletionCode_RandomHash
import Theorems.Thm_DeletionCode_RandomHash_real_joint_uniform
import Theorems.Thm_DeletionCode_CircleUniform_measurableSet_smallArc
import Theorems.Thm_DeletionCode_CircleUniform_volume_smallArc
import Theorems.Thm_DeletionCode_IntegerTorusMap_jointHash_apply
import Theorems.Thm_DeletionCode_TorusHaar_forall_mem_measure
attribute [local simp] DeletionCode.IntegerTorusMap.jointHash_apply



set_option autoImplicit true
open DeletionCode DeletionCode.RandomHash
open MeasureTheory ProbabilityTheory CircleHash IntegerTorusMap CircleUniform
open scoped BigOperators
variable {I J : Type*} [Fintype I] [Fintype J]
namespace DeletionCode.RandomHash
theorem _root_.solution (w : J → I → ℤ)
    (h : LinearIndependent ℚ (fun j i => (w j i : ℚ))) (Q : ℕ) (hQ : 2 ≤ Q) :
    realWeights I {weights | ∀ j, ‖realWeightedHash weights (w j)‖ < 1 / (Q : ℝ)} =
      ENNReal.ofReal (2 / (Q : ℝ)) ^ Fintype.card J := by
  classical
  calc
    _ = ∏ j : J, volume (smallArc Q) := by
      simpa only [smallArc, Set.mem_ofPred_eq] using
        TorusHaar.forall_mem_measure (real_joint_uniform w h)
          (fun _ => smallArc Q) (fun _ => measurableSet_smallArc Q)
    _ = _ := by simp only [volume_smallArc Q hQ, Finset.prod_const, Finset.card_univ]
end DeletionCode.RandomHash
