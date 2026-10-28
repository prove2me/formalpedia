-- Prove2me | solution 1 for D1Bound5.finiteA5RatioWeights_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:24:29.679339+00:00
-- url     : https://prove2.me/submissions/3e9761e4-f925-47d1-858f-2d87b70167c9

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
import Theorems.Thm_D1Bound5_finiteHomogeneousRatioWeight_nonneg

section
noncomputable section

namespace D1Bound5





theorem _root_.solution (r : ℝ) (hr : 0 ≤ r) (i : Fin 3) (ell : Fin 6) :
    0 ≤ finiteA5RatioWeights r i ell := by
  fin_cases ell
  · exact add_nonneg (finiteHomogeneousRatioWeight_nonneg 7 _ r hr)
      (finiteHomogeneousRatioWeight_nonneg 7 _ r hr)
  · exact add_nonneg (finiteHomogeneousRatioWeight_nonneg 8 _ r hr)
      (finiteHomogeneousRatioWeight_nonneg 8 _ r hr)
  · exact add_nonneg (finiteHomogeneousRatioWeight_nonneg 9 _ r hr)
      (finiteHomogeneousRatioWeight_nonneg 9 _ r hr)
  · exact add_nonneg (finiteHomogeneousRatioWeight_nonneg 10 _ r hr)
      (finiteHomogeneousRatioWeight_nonneg 10 _ r hr)
  · exact add_nonneg (finiteHomogeneousRatioWeight_nonneg 11 _ r hr)
      (finiteHomogeneousRatioWeight_nonneg 11 _ r hr)
  · exact add_nonneg (finiteHomogeneousRatioWeight_nonneg 12 _ r hr)
      (finiteHomogeneousRatioWeight_nonneg 12 _ r hr)







end D1Bound5
end
