-- Prove2me | solution 1 for D1Bound5.finiteA4_root_coefficient_norm_le_ratio
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:39:58.262276+00:00
-- url     : https://prove2.me/submissions/2f76111e-a8d9-4885-92c7-513837902546

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
import Definitions.Def_D1Bound5_FiniteA4Coefficients_Definitions
import Definitions.Def_D1Bound5_FiniteA4RatioHeight_Definitions
import Definitions.Def_D1Bound5_FiniteHomogeneousRatio_Definitions
import Definitions.Def_D1Bound5_FiniteHomogeneousTwo_Definitions
import Theorems.Thm_D1Bound5_finiteHomogeneousTwo_norm_le_ratio

section
noncomputable section

namespace D1Bound5







theorem _root_.solution (x y : ℂ) (r : ℝ)
    (hr : 0 ≤ r) (hxy : ‖x‖ ≤ r*‖y‖) (i : Fin 3) (ell : Fin 5) :
    ‖finiteA4RootCoeff x y i 0 ell‖+‖finiteA4RootCoeff x y i 1 ell‖ ≤
      finiteA4RatioWeights r i ell*‖y‖^(5+(ell : ℕ)) := by
  fin_cases ell
  · have h := add_le_add
      (finiteHomogeneousTwo_norm_le_ratio 5 (finiteA4Coeff0 i 0) x y r hr hxy)
      (finiteHomogeneousTwo_norm_le_ratio 5 (finiteA4Coeff0 i 1) x y r hr hxy)
    simpa [finiteA4RootCoeff,finiteA4RatioWeights,add_mul] using h
  · have h := add_le_add
      (finiteHomogeneousTwo_norm_le_ratio 6 (finiteA4Coeff1 i 0) x y r hr hxy)
      (finiteHomogeneousTwo_norm_le_ratio 6 (finiteA4Coeff1 i 1) x y r hr hxy)
    simpa [finiteA4RootCoeff,finiteA4RatioWeights,add_mul] using h
  · have h := add_le_add
      (finiteHomogeneousTwo_norm_le_ratio 7 (finiteA4Coeff2 i 0) x y r hr hxy)
      (finiteHomogeneousTwo_norm_le_ratio 7 (finiteA4Coeff2 i 1) x y r hr hxy)
    simpa [finiteA4RootCoeff,finiteA4RatioWeights,add_mul] using h
  · have h := add_le_add
      (finiteHomogeneousTwo_norm_le_ratio 8 (finiteA4Coeff3 i 0) x y r hr hxy)
      (finiteHomogeneousTwo_norm_le_ratio 8 (finiteA4Coeff3 i 1) x y r hr hxy)
    simpa [finiteA4RootCoeff,finiteA4RatioWeights,add_mul] using h
  · have h := add_le_add
      (finiteHomogeneousTwo_norm_le_ratio 9 (finiteA4Coeff4 i 0) x y r hr hxy)
      (finiteHomogeneousTwo_norm_le_ratio 9 (finiteA4Coeff4 i 1) x y r hr hxy)
    simpa [finiteA4RootCoeff,finiteA4RatioWeights,add_mul] using h





end D1Bound5
end
