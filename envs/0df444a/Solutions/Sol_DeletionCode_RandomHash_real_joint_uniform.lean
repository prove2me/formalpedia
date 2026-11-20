-- Prove2me | solution 1 for DeletionCode.RandomHash.real_joint_uniform
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:22:08.343687+00:00
-- url     : https://prove2.me/submissions/04cb3420-42e4-4591-bdf9-ac52227e9b42

import Definitions.Def_DeletionCode_IntegerTorusMap
import Definitions.Def_DeletionCode_TorusHaar
import Definitions.Def_DeletionCode_CircleUniform
import Definitions.Def_DeletionCode_RandomHash
import Theorems.Thm_DeletionCode_RandomHash_joint_uniform
import Theorems.Thm_DeletionCode_CircleUniform_measurePreserving_toCircle


set_option autoImplicit true
open DeletionCode DeletionCode.RandomHash
open MeasureTheory ProbabilityTheory CircleHash IntegerTorusMap CircleUniform
open scoped BigOperators
variable {I J : Type*} [Fintype I] [Fintype J]
namespace DeletionCode.RandomHash
theorem _root_.solution (w : J → I → ℤ)
    (h : LinearIndependent ℚ (fun j i => (w j i : ℚ))) :
    MeasurePreserving (fun weights j => realWeightedHash weights (w j)) (realWeights I) volume :=
  (joint_uniform w h).comp (measurePreserving_toCircle I)
end DeletionCode.RandomHash
