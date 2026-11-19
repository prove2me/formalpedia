-- Prove2me | solution 1 for DeletionCode.IntegerTorusMap.jointHash_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:35:43.108217+00:00
-- url     : https://prove2.me/submissions/578f4ff4-ae94-4ab2-ab0d-16d335496e1b

import Definitions.Def_DeletionCode_CircleHash
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Algebra.Group.Basic
import Definitions.Def_DeletionCode_IntegerTorusMap

set_option autoImplicit true
open DeletionCode DeletionCode.IntegerTorusMap
open scoped BigOperators Matrix
open CircleHash
variable {I J : Type*} [Fintype I]
namespace DeletionCode.IntegerTorusMap
theorem _root_.solution (w : J → I → ℤ)
    (weights : I → UnitAddCircle) (j : J) :
    jointHash w weights j = weightedHash weights (w j) := rfl
end DeletionCode.IntegerTorusMap
