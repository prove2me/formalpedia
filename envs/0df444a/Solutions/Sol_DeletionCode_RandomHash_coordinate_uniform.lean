-- Prove2me | solution 1 for DeletionCode.RandomHash.coordinate_uniform
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:21:17.074532+00:00
-- url     : https://prove2.me/submissions/bc355193-9d28-4807-8b42-51195107ef4d

import Definitions.Def_DeletionCode_IntegerTorusMap
import Definitions.Def_DeletionCode_TorusHaar
import Definitions.Def_DeletionCode_CircleUniform
import Definitions.Def_DeletionCode_RandomHash
import Theorems.Thm_DeletionCode_IntegerTorusMap_continuous_jointHash
import Theorems.Thm_DeletionCode_IntegerTorusMap_jointHash_surjective
import Theorems.Thm_DeletionCode_TorusHaar_coordinate_measurePreserving


set_option autoImplicit true
open DeletionCode DeletionCode.RandomHash
open MeasureTheory ProbabilityTheory CircleHash IntegerTorusMap CircleUniform
open scoped BigOperators
variable {I J : Type*} [Fintype I] [Fintype J]
namespace DeletionCode.RandomHash
theorem _root_.solution (w : J → I → ℤ)
    (h : LinearIndependent ℚ (fun j i => (w j i : ℚ))) (j : J) :
    MeasurePreserving (fun weights => weightedHash weights (w j)) volume volume :=
  TorusHaar.coordinate_measurePreserving (jointHash w)
    (continuous_jointHash w) (jointHash_surjective w h) j
end DeletionCode.RandomHash
