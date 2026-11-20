-- Prove2me | solution 1 for DeletionCode.RandomHash.joint_uniform
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:21:15.414954+00:00
-- url     : https://prove2.me/submissions/d1a2a577-ee04-430f-ac60-b37183bfdb35

import Definitions.Def_DeletionCode_IntegerTorusMap
import Definitions.Def_DeletionCode_TorusHaar
import Definitions.Def_DeletionCode_CircleUniform
import Definitions.Def_DeletionCode_RandomHash
import Theorems.Thm_DeletionCode_IntegerTorusMap_continuous_jointHash
import Theorems.Thm_DeletionCode_IntegerTorusMap_jointHash_surjective
import Theorems.Thm_DeletionCode_TorusHaar_measurePreserving


set_option autoImplicit true
open DeletionCode DeletionCode.RandomHash
open MeasureTheory ProbabilityTheory CircleHash IntegerTorusMap CircleUniform
open scoped BigOperators
variable {I J : Type*} [Fintype I] [Fintype J]
namespace DeletionCode.RandomHash
theorem _root_.solution (w : J → I → ℤ)
    (h : LinearIndependent ℚ (fun j i => (w j i : ℚ))) :
    MeasurePreserving (jointHash w) volume volume :=
  TorusHaar.measurePreserving (jointHash w) (continuous_jointHash w) (jointHash_surjective w h)
end DeletionCode.RandomHash
