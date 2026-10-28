-- Prove2me | solution 1 for D1Bound5.finiteA5_five_region_height_slack
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:27:43.757823+00:00
-- url     : https://prove2.me/submissions/a7374040-f64e-433b-a8cf-f51d60e57dbd

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic
import Mathlib.Tactic.Convert
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteA5Coefficients_Definitions
import Definitions.Def_D1Bound5_FiniteA5RatioHeight_Definitions
import Definitions.Def_D1Bound5_FiniteHomogeneousRatio_Definitions

section
noncomputable section

namespace D1Bound5









set_option maxHeartbeats 4000000 in
/-- The five displayed coefficient constants are checked directly from the
actual integer coefficient vectors at their exact rational anchor ratios. -/
theorem _root_.solution (region : Fin 5) (i : Fin 3) :
    (101/100 : ℝ)*(∑ ell : Fin 6,
      finiteA5RatioWeights (fiveRegionAnchorRatio region) i ell/(1000 : ℝ)^(5-(ell : ℕ))) <
      fiveRegionA5Height region := by
  fin_cases region <;> fin_cases i <;>
    norm_num [finiteA5RatioWeights,fiveRegionAnchorRatio,fiveRegionA5Height,finiteHomogeneousRatioWeight,
      finiteA5Coeff0, finiteA5Coeff1, finiteA5Coeff2, finiteA5Coeff3, finiteA5Coeff4, finiteA5Coeff5,Fin.sum_univ_succ,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_succ',
      Matrix.head_cons, Matrix.tail_cons]



end D1Bound5
end
