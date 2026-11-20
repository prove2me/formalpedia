-- Prove2me | solution 1 for DeletionCode.IntegerTorusMap.jointHash_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:20:18.872034+00:00
-- url     : https://prove2.me/submissions/e7238d49-e4f9-4bf3-8d6c-f9e83e983c83

import Definitions.Def_DeletionCode_CircleHash
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Algebra.Group.Basic
import Definitions.Def_DeletionCode_IntegerTorusMap
import Theorems.Thm_DeletionCode_IntegerTorusMap_realWeightedSums_surjective
import Theorems.Thm_DeletionCode_CircleHash_realWeightedHash_apply


set_option autoImplicit true
open DeletionCode DeletionCode.IntegerTorusMap
open scoped BigOperators Matrix
open CircleHash
variable {I J : Type*} [Fintype I]
variable [Fintype J]
namespace DeletionCode.IntegerTorusMap
theorem _root_.solution (w : J → I → ℤ)
    (h : LinearIndependent ℚ (fun j => fun i => (w j i : ℚ))) :
    Function.Surjective (jointHash w) := by
  intro target
  obtain ⟨weights, hweights⟩ :=
    realWeightedSums_surjective w h (fun j => representative (target j))
  refine ⟨fun i => (weights i : UnitAddCircle), ?_⟩
  funext j
  have hj : (∑ i, weights i * (w j i : ℝ)) = representative (target j) :=
    congrFun hweights j
  change realWeightedHash weights (w j) = target j
  rw [realWeightedHash_apply, hj, coe_representative]
end DeletionCode.IntegerTorusMap
