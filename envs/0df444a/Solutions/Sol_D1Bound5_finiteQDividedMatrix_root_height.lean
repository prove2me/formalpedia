-- Prove2me | solution 1 for D1Bound5.finiteQDividedMatrix_root_height
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:57:47.974781+00:00
-- url     : https://prove2.me/submissions/dde175c1-5de4-4bf6-bd62-ff224b44f828

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
import Theorems.Thm_D1Bound5_finiteQ_pair_height

section
namespace D1Bound5



/-- Every one of the five actual rows satisfies the same root-column
height bound. The selected nonzero integral row can therefore be used
without imposing a separate height certificate. -/
theorem _root_.solution
    (a b s t c : ℂ) (T C : ℝ) (hT : 0 ≤ T) (hC : 0 ≤ C)
    (ha : ‖a‖ ≤ T) (hb : ‖b‖ ≤ T) (hs : ‖s‖ ≤ T) (ht : ‖t‖ ≤ T)
    (hc : ‖c‖ ≤ C) (hTC : 1 ≤ T*C) (i : Fin 5) :
    (∑ j : Fin 4, ‖finiteQDividedMatrix a b s t c i j.succ‖) ≤ 36*T^3*C := by
  have hab := finiteQ_pair_height a b c T C hT hC ha hb hc hTC
  have has := finiteQ_pair_height a s c T C hT hC ha hs hc hTC
  have hbs := finiteQ_pair_height b s c T C hT hC hb hs hc hTC
  have hat := finiteQ_pair_height a t c T C hT hC ha ht hc hTC
  have hbt := finiteQ_pair_height b t c T C hT hC hb ht hc hTC
  fin_cases i <;>
    simp_all [finiteQDividedMatrix, Fin.sum_univ_succ]

end D1Bound5
end
