-- Prove2me | solution 1 for DeletionCode.RandomHash.real_independent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:23:00.992904+00:00
-- url     : https://prove2.me/submissions/196d64d7-86d9-48bf-a9af-96507f523e93

import Definitions.Def_DeletionCode_IntegerTorusMap
import Definitions.Def_DeletionCode_TorusHaar
import Definitions.Def_DeletionCode_CircleUniform
import Definitions.Def_DeletionCode_RandomHash
import Theorems.Thm_DeletionCode_RandomHash_real_joint_uniform
import Theorems.Thm_DeletionCode_TorusHaar_coordinates_independent_of_measurePreserving


set_option autoImplicit true
open DeletionCode DeletionCode.RandomHash
open MeasureTheory ProbabilityTheory CircleHash IntegerTorusMap CircleUniform
open scoped BigOperators
variable {I J : Type*} [Fintype I] [Fintype J]
namespace DeletionCode.RandomHash
theorem _root_.solution (w : J → I → ℤ)
    (h : LinearIndependent ℚ (fun j i => (w j i : ℚ))) :
    iIndepFun (fun j weights => realWeightedHash weights (w j)) (realWeights I) :=
  TorusHaar.coordinates_independent_of_measurePreserving (real_joint_uniform w h)
end DeletionCode.RandomHash
