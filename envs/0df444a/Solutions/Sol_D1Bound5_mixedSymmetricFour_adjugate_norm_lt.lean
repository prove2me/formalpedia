-- Prove2me | solution 1 for D1Bound5.mixedSymmetricFour_adjugate_norm_lt
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:29:25.649219+00:00
-- url     : https://prove2.me/submissions/a9d95690-d569-4e28-8c3d-ef05c3ac1e9e

import Lean.Util.CollectAxioms
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_RootMatrixOperatorBound_Definitions
import Theorems.Thm_D1Bound5_halfOffDiagonal_adjugate_apply
import Theorems.Thm_D1Bound5_mixedFour_adjugate_norm_of_entries
import Theorems.Thm_D1Bound5_mixed_offDiagonal_first
import Theorems.Thm_D1Bound5_mixed_offDiagonal_later
import Theorems.Thm_D1Bound5_mixed_triple_first_first_later
import Theorems.Thm_D1Bound5_mixed_triple_later
import Theorems.Thm_D1Bound5_symmetricFour_adjugate_formula

section
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5

/-- An unconditional L2-adjugate bound for mixed first/later cofactor radii. -/
theorem _root_.solution (x y z u v w : ℂ)
    (hx : ‖x-(1/2 : ℂ)‖ < (1/18 : ℝ))
    (hy : ‖y-(1/2 : ℂ)‖ < (1/18 : ℝ))
    (hz : ‖z-(1/2 : ℂ)‖ < (1/18 : ℝ))
    (hu : ‖u-(1/2 : ℂ)‖ < (1/64 : ℝ))
    (hv : ‖v-(1/2 : ℂ)‖ < (1/64 : ℝ))
    (hw : ‖w-(1/2 : ℂ)‖ < (1/64 : ℝ)) :
    ‖( !![0,x,y,z; x,0,u,v; y,u,0,w; z,v,w,0] :
       Matrix (Fin 4) (Fin 4) ℂ).adjugate‖ <
      (155/96 : ℝ) * (59/96)^2 := by
  let F : Matrix (Fin 4) (Fin 4) ℂ :=
    !![0,x,y,z; x,0,u,v; y,u,0,w; z,v,w,0]
  have hAdj : F.adjugate =
    !![2*u*v*w, w^2*x-w*z*u-w*y*v, v^2*y-v*z*u-v*x*w, u^2*z-u*y*v-u*x*w;
       w^2*x-w*z*u-w*y*v, 2*y*z*w, z^2*u-z*y*v-z*x*w, y^2*v-y*x*w-y*z*u;
       v^2*y-v*z*u-v*x*w, z^2*u-z*y*v-z*x*w, 2*x*z*v, x^2*w-x*y*v-x*z*u;
       u^2*z-u*y*v-u*x*w, y^2*v-y*x*w-y*z*u, x^2*w-x*y*v-x*z*u, 2*x*y*u] := by
    exact symmetricFour_adjugate_formula x y z u v w
  have h00 := mixed_triple_later u v w hu hv hw
  have h11 := mixed_triple_first_first_later y z w hy hz hw
  have h22 := mixed_triple_first_first_later x z v hx hz hv
  have h33 := mixed_triple_first_first_later x y u hx hy hu
  have h01 := mixed_offDiagonal_first x y z u v w hx hy hz hu hv hw
  have h02 := mixed_offDiagonal_first y x z u w v hy hx hz hu hw hv
  have h03 := mixed_offDiagonal_first z x y v w u hz hx hy hv hw hu
  have h12 := mixed_offDiagonal_later x y z u v w hx hy hz hu hv hw
  have h13 := mixed_offDiagonal_later z x y v w u hz hx hy hv hw hu
  have h23 := mixed_offDiagonal_later z y x w v u hz hy hx hw hv hu
  change ‖F.adjugate‖ < _
  apply mixedFour_adjugate_norm_of_entries F
  · intro i
    fin_cases i
    · simpa [Matrix.sub_apply, hAdj, Matrix.of_apply,
             halfOffDiagonal_adjugate_apply, sub_neg_eq_add, neg_div] using h00
    · simpa [Matrix.sub_apply, hAdj, Matrix.of_apply,
             halfOffDiagonal_adjugate_apply, sub_neg_eq_add, neg_div] using h11
    · simpa [Matrix.sub_apply, hAdj, Matrix.of_apply,
             halfOffDiagonal_adjugate_apply, sub_neg_eq_add, neg_div] using h22
    · simpa [Matrix.sub_apply, hAdj, Matrix.of_apply,
             halfOffDiagonal_adjugate_apply, sub_neg_eq_add, neg_div] using h33
  · intro i j hij hz
    fin_cases i <;> fin_cases j <;> try simp at hij <;> try simp at hz
    all_goals first
      | simpa [Matrix.sub_apply, hAdj, Matrix.of_apply,
               halfOffDiagonal_adjugate_apply, sub_neg_eq_add, neg_div] using h01
      | simpa [Matrix.sub_apply, hAdj, Matrix.of_apply,
               halfOffDiagonal_adjugate_apply, sub_neg_eq_add, neg_div] using h02
      | simpa [Matrix.sub_apply, hAdj, Matrix.of_apply,
               halfOffDiagonal_adjugate_apply, sub_neg_eq_add, neg_div] using h03
  · intro i j hij hz
    fin_cases i <;> fin_cases j <;> try simp at hij <;> try simp at hz
    all_goals first
      | simpa [Matrix.sub_apply, hAdj, Matrix.of_apply,
               halfOffDiagonal_adjugate_apply, sub_neg_eq_add, neg_div] using h12
      | simpa [Matrix.sub_apply, hAdj, Matrix.of_apply,
               halfOffDiagonal_adjugate_apply, sub_neg_eq_add, neg_div] using h13
      | simpa [Matrix.sub_apply, hAdj, Matrix.of_apply,
               halfOffDiagonal_adjugate_apply, sub_neg_eq_add, neg_div] using h23



end D1Bound5
end
