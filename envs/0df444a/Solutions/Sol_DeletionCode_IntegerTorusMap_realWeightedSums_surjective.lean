-- Prove2me | solution 1 for DeletionCode.IntegerTorusMap.realWeightedSums_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:19:07.208894+00:00
-- url     : https://prove2.me/submissions/65856c7f-63c1-45ae-a093-0e358bd179d2

import Definitions.Def_DeletionCode_CircleHash
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Algebra.Group.Basic
import Definitions.Def_DeletionCode_IntegerTorusMap
import Theorems.Thm_DeletionCode_IntegerTorusMap_jointHash_apply
import Theorems.Thm_DeletionCode_IntegerTorusMap_real_right_inverse
attribute [local simp] DeletionCode.IntegerTorusMap.jointHash_apply

set_option autoImplicit true
open DeletionCode DeletionCode.IntegerTorusMap
open scoped BigOperators Matrix
open CircleHash
variable {I J : Type*} [Fintype I]
variable [Fintype J]
namespace DeletionCode.IntegerTorusMap
theorem _root_.solution (w : J → I → ℤ)
    (h : LinearIndependent ℚ (fun j => fun i => (w j i : ℚ))) :
    Function.Surjective (fun weights : I → ℝ =>
      fun j => ∑ i, weights i * (w j i : ℝ)) := by
  classical
  let A : Matrix J I ℚ := fun j i => (w j i : ℚ)
  have hA : LinearIndependent ℚ A.row := h
  obtain ⟨B, hB⟩ := real_right_inverse A hA
  have hsurj : Function.Surjective (A.map (Rat.castHom ℝ)).mulVec :=
    Matrix.mulVec_surjective_iff_exists_right_inverse.mpr ⟨B, hB⟩
  intro target
  obtain ⟨weights, hweights⟩ := hsurj target
  refine ⟨weights, ?_⟩
  funext j
  have hj := congrFun hweights j
  change (∑ i, ((w j i : ℚ) : ℝ) * weights i) = target j at hj
  simpa only [Rat.cast_intCast, mul_comm] using hj
end DeletionCode.IntegerTorusMap
