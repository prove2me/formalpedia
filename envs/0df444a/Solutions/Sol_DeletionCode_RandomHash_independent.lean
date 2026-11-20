-- Prove2me | solution 1 for DeletionCode.RandomHash.independent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:21:15.855162+00:00
-- url     : https://prove2.me/submissions/3999c7cb-91c2-49cf-8b69-e4f6231ba55f

import Definitions.Def_DeletionCode_IntegerTorusMap
import Definitions.Def_DeletionCode_TorusHaar
import Definitions.Def_DeletionCode_CircleUniform
import Definitions.Def_DeletionCode_RandomHash
import Theorems.Thm_DeletionCode_IntegerTorusMap_continuous_jointHash
import Theorems.Thm_DeletionCode_IntegerTorusMap_jointHash_surjective
import Theorems.Thm_DeletionCode_TorusHaar_coordinates_independent


set_option autoImplicit true
open DeletionCode DeletionCode.RandomHash
open MeasureTheory ProbabilityTheory CircleHash IntegerTorusMap CircleUniform
open scoped BigOperators
variable {I J : Type*} [Fintype I] [Fintype J]
namespace DeletionCode.RandomHash
theorem _root_.solution (w : J → I → ℤ)
    (h : LinearIndependent ℚ (fun j i => (w j i : ℚ))) :
    iIndepFun (fun j weights => weightedHash weights (w j)) volume :=
  TorusHaar.coordinates_independent (jointHash w)
    (continuous_jointHash w) (jointHash_surjective w h)
end DeletionCode.RandomHash
