-- Prove2me | solution 1 for D1Bound5.finiteN3RatioWeights_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:27:44.031578+00:00
-- url     : https://prove2.me/submissions/af91400a-453c-4187-9280-9a1935da0d7e

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
import Definitions.Def_D1Bound5_FiniteN3Height_Definitions
import Definitions.Def_D1Bound5_FiniteN3RatioHeight_Definitions
import Theorems.Thm_D1Bound5_finiteHomogeneousRatioWeight_nonneg

section
noncomputable section

namespace D1Bound5









theorem _root_.solution (r : ℝ) (hr : 0 ≤ r) (i : Fin 3) (ell : Fin 4) :
    0 ≤ finiteN3RatioWeights r i ell := by
  fin_cases ell
  · exact add_nonneg (finiteHomogeneousRatioWeight_nonneg 4 _ r hr)
      (finiteHomogeneousRatioWeight_nonneg 4 _ r hr)
  · exact add_nonneg (finiteHomogeneousRatioWeight_nonneg 5 _ r hr)
      (finiteHomogeneousRatioWeight_nonneg 5 _ r hr)
  · exact add_nonneg (finiteHomogeneousRatioWeight_nonneg 6 _ r hr)
      (finiteHomogeneousRatioWeight_nonneg 6 _ r hr)
  · exact add_nonneg (finiteHomogeneousRatioWeight_nonneg 7 _ r hr)
      (finiteHomogeneousRatioWeight_nonneg 7 _ r hr)







end D1Bound5
end
