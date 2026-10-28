-- Prove2me | solution 1 for D1Bound5.finiteN2_root_coefficient_norm_le_ratio
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:40:03.825355+00:00
-- url     : https://prove2.me/submissions/342b9d5d-0623-48c2-a4cc-13b892c84acd

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteHomogeneousRatio_Definitions
import Definitions.Def_D1Bound5_FiniteHomogeneousTwo_Definitions
import Definitions.Def_D1Bound5_FiniteN2Height_Definitions
import Definitions.Def_D1Bound5_FiniteN2RatioHeight_Definitions
import Theorems.Thm_D1Bound5_finiteHomogeneousTwo_norm_le_ratio

section
noncomputable section

namespace D1Bound5











theorem _root_.solution (x y : ℂ) (r : ℝ)
    (hr : 0 ≤ r) (hxy : ‖x‖ ≤ r*‖y‖) (i : Fin 3) (ell : Fin 3) :
    ‖finiteN2RatioRootCoeff x y i 0 ell‖+‖finiteN2RatioRootCoeff x y i 1 ell‖ ≤
      finiteN2RatioWeights r i ell*‖y‖^(2+(ell : ℕ)) := by
  fin_cases ell
  · have h := add_le_add
      (finiteHomogeneousTwo_norm_le_ratio 2 (finiteN2Coeff0 i 0) x y r hr hxy)
      (finiteHomogeneousTwo_norm_le_ratio 2 (finiteN2Coeff0 i 1) x y r hr hxy)
    simpa [finiteN2RatioRootCoeff,finiteN2RatioWeights,add_mul] using h
  · have h := add_le_add
      (finiteHomogeneousTwo_norm_le_ratio 3 (finiteN2Coeff1 i 0) x y r hr hxy)
      (finiteHomogeneousTwo_norm_le_ratio 3 (finiteN2Coeff1 i 1) x y r hr hxy)
    simpa [finiteN2RatioRootCoeff,finiteN2RatioWeights,add_mul] using h
  · have h := add_le_add
      (finiteHomogeneousTwo_norm_le_ratio 4 (finiteN2Coeff2 i 0) x y r hr hxy)
      (finiteHomogeneousTwo_norm_le_ratio 4 (finiteN2Coeff2 i 1) x y r hr hxy)
    simpa [finiteN2RatioRootCoeff,finiteN2RatioWeights,add_mul] using h





end D1Bound5
end
