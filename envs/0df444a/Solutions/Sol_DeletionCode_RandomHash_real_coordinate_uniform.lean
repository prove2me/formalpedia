-- Prove2me | solution 1 for DeletionCode.RandomHash.real_coordinate_uniform
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:23:00.511194+00:00
-- url     : https://prove2.me/submissions/9679f801-11aa-4708-8c05-7820938b0e3a

import Definitions.Def_DeletionCode_IntegerTorusMap
import Definitions.Def_DeletionCode_TorusHaar
import Definitions.Def_DeletionCode_CircleUniform
import Definitions.Def_DeletionCode_RandomHash
import Theorems.Thm_DeletionCode_RandomHash_real_joint_uniform
import Theorems.Thm_DeletionCode_TorusHaar_coordinate_measurePreserving_of_measurePreserving


set_option autoImplicit true
open DeletionCode DeletionCode.RandomHash
open MeasureTheory ProbabilityTheory CircleHash IntegerTorusMap CircleUniform
open scoped BigOperators
variable {I J : Type*} [Fintype I] [Fintype J]
namespace DeletionCode.RandomHash
theorem _root_.solution (w : J → I → ℤ)
    (h : LinearIndependent ℚ (fun j i => (w j i : ℚ))) (j : J) :
    MeasurePreserving (fun weights => realWeightedHash weights (w j)) (realWeights I) volume :=
  TorusHaar.coordinate_measurePreserving_of_measurePreserving (real_joint_uniform w h) j
end DeletionCode.RandomHash
