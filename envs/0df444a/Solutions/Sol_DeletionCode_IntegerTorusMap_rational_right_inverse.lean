-- Prove2me | solution 1 for DeletionCode.IntegerTorusMap.rational_right_inverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:16:33.523344+00:00
-- url     : https://prove2.me/submissions/783439b1-b6d9-4941-a057-01ad5f4daf92

import Definitions.Def_DeletionCode_CircleHash
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Algebra.Group.Basic
import Definitions.Def_DeletionCode_IntegerTorusMap
import Theorems.Thm_DeletionCode_IntegerTorusMap_jointHash_apply
attribute [local simp] DeletionCode.IntegerTorusMap.jointHash_apply

set_option autoImplicit true
open DeletionCode DeletionCode.IntegerTorusMap
open scoped BigOperators Matrix
open CircleHash
variable {I J : Type*} [Fintype I]
variable [Fintype J]
namespace DeletionCode.IntegerTorusMap
theorem _root_.solution [DecidableEq J] (A : Matrix J I ℚ)
    (h : LinearIndependent ℚ A.row) :
    ∃ B : Matrix I J ℚ, A * B = 1 := by
  classical
  have hrank : A.rank = Fintype.card J := h.rank_matrix
  have hrange : LinearMap.range A.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    change A.rank = Module.finrank ℚ (J → ℚ)
    simpa only [Module.finrank_fintype_fun_eq_card] using hrank
  have hsurj : Function.Surjective A.mulVec :=
    LinearMap.range_eq_top.mp hrange
  exact Matrix.mulVec_surjective_iff_exists_right_inverse.mp hsurj
end DeletionCode.IntegerTorusMap
