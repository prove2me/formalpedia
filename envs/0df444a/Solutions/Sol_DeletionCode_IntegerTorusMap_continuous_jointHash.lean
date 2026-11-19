-- Prove2me | solution 1 for DeletionCode.IntegerTorusMap.continuous_jointHash
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:36:08.745188+00:00
-- url     : https://prove2.me/submissions/0f452b4f-e976-47de-9999-3e5199003861

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
theorem _root_.solution (w : J → I → ℤ) : Continuous (jointHash w) := by
  apply continuous_pi
  intro j
  change Continuous (fun weights : I → UnitAddCircle => ∑ i, w j i • weights i)
  exact continuous_finsetSum _ (fun i _ => (continuous_apply i).zsmul (w j i))
end DeletionCode.IntegerTorusMap
