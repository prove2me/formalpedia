-- Prove2me | solution 1 for DeletionCode.RandomHash.independent_differences
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:24:06.391274+00:00
-- url     : https://prove2.me/submissions/470ef836-e945-401d-915f-fcc7071c8b4d

import Definitions.Def_DeletionCode_IntegerTorusMap
import Definitions.Def_DeletionCode_TorusHaar
import Definitions.Def_DeletionCode_CircleUniform
import Definitions.Def_DeletionCode_RandomHash
import Theorems.Thm_DeletionCode_RandomHash_real_joint_uniform
import Theorems.Thm_DeletionCode_RandomHash_real_coordinate_uniform
import Theorems.Thm_DeletionCode_RandomHash_real_independent

set_option autoImplicit true
open DeletionCode DeletionCode.RandomHash
open MeasureTheory ProbabilityTheory CircleHash IntegerTorusMap CircleUniform
open scoped BigOperators
variable {I J : Type*} [Fintype I] [Fintype J]
namespace DeletionCode.RandomHash
theorem _root_.solution (w : J → I → ℤ)
    (h : LinearIndependent ℚ (fun j i => (w j i : ℚ))) :
    iIndepFun (fun j weights => realWeightedHash weights (w j)) (realWeights I) ∧
    (∀ j, MeasurePreserving (fun weights => realWeightedHash weights (w j)) (realWeights I) volume) ∧
    MeasurePreserving (fun weights j => realWeightedHash weights (w j)) (realWeights I) volume :=
  ⟨real_independent w h, real_coordinate_uniform w h, real_joint_uniform w h⟩
end DeletionCode.RandomHash
