-- Prove2me | solution 1 for D1Bound5.finiteQ_pair_height
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:31:56.820013+00:00
-- url     : https://prove2.me/submissions/cc73e049-111e-41fb-9c1e-4975af5cbd21

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteQMatrix_Definitions

section
namespace D1Bound5

/-- The actual two polynomial root weights have total height at most the
sum of their 36 absolute integer coefficients. -/
theorem _root_.solution
    (u v c : ℂ) (T C : ℝ) (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hu : ‖u‖ ≤ T) (hv : ‖v‖ ≤ T) (hc : ‖c‖ ≤ C) (hTC : 1 ≤ T*C) :
    ‖finiteQLeft u v c‖ + ‖finiteQRight u v c‖ ≤ 36*T^3*C := by
  have hleft : ‖finiteQLeft u v c‖ ≤ 6*T^2+12*T^3*C := by
    calc
      _ ≤ ‖u^2-5*u*v‖ + ‖(4*u^3-8*u^2*v)*c‖ := norm_add_le _ _
      _ ≤ (‖u^2‖+‖5*u*v‖) + (‖4*u^3‖+‖8*u^2*v‖)*‖c‖ := by
        rw [norm_mul]
        exact add_le_add (norm_sub_le _ _)
          (mul_le_mul_of_nonneg_right (norm_sub_le _ _) (norm_nonneg _))
      _ = (‖u‖^2+5*‖u‖*‖v‖) + (4*‖u‖^3+8*‖u‖^2*‖v‖)*‖c‖ := by
        norm_num [norm_mul, norm_pow]
      _ ≤ (T^2+5*T*T)+(4*T^3+8*T^2*T)*C := by gcongr
      _ = _ := by ring
  have hright : ‖finiteQRight u v c‖ ≤ 6*T^2+12*T^3*C := by
    calc
      _ ≤ ‖5*u*v-v^2‖ + ‖(8*u*v^2-4*v^3)*c‖ := norm_add_le _ _
      _ ≤ (‖5*u*v‖+‖v^2‖) + (‖8*u*v^2‖+‖4*v^3‖)*‖c‖ := by
        rw [norm_mul]
        exact add_le_add (norm_sub_le _ _)
          (mul_le_mul_of_nonneg_right (norm_sub_le _ _) (norm_nonneg _))
      _ = (5*‖u‖*‖v‖+‖v‖^2) + (8*‖u‖*‖v‖^2+4*‖v‖^3)*‖c‖ := by
        norm_num [norm_mul, norm_pow]
      _ ≤ (5*T*T+T^2)+(8*T*T^2+4*T^3)*C := by gcongr
      _ = _ := by ring
  have hsmall := mul_le_mul_of_nonneg_left hTC (sq_nonneg T)
  nlinarith only [hleft, hright, hsmall]



end D1Bound5
end
