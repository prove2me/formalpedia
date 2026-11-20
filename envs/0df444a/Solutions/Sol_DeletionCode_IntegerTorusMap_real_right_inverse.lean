-- Prove2me | solution 1 for DeletionCode.IntegerTorusMap.real_right_inverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:47.720509+00:00
-- url     : https://prove2.me/submissions/0d4ec3cc-2133-487e-b8d6-2d5d21f7d1f9

import Definitions.Def_DeletionCode_CircleHash
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Algebra.Group.Basic
import Definitions.Def_DeletionCode_IntegerTorusMap
import Theorems.Thm_DeletionCode_IntegerTorusMap_rational_right_inverse

set_option autoImplicit true
open DeletionCode DeletionCode.IntegerTorusMap
open scoped BigOperators Matrix
open CircleHash
variable {I J : Type*} [Fintype I]
variable [Fintype J]
namespace DeletionCode.IntegerTorusMap
theorem _root_.solution [DecidableEq J] (A : Matrix J I ℚ)
    (h : LinearIndependent ℚ A.row) :
    ∃ B : Matrix I J ℝ, A.map (Rat.castHom ℝ) * B = 1 := by
  classical
  obtain ⟨B, hB⟩ := rational_right_inverse A h
  refine ⟨B.map (Rat.castHom ℝ), ?_⟩
  have hmap := congrArg (fun M : Matrix J J ℚ => M.map (Rat.castHom ℝ)) hB
  rw [Matrix.map_mul] at hmap
  have hone : (1 : Matrix J J ℚ).map (Rat.castHom ℝ) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  exact hmap.trans hone
end DeletionCode.IntegerTorusMap
