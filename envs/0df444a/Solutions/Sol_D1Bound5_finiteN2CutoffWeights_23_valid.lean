-- Prove2me | solution 1 for D1Bound5.finiteN2CutoffWeights_23_valid
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:57:23.817989+00:00
-- url     : https://prove2.me/submissions/24c29eac-2f3c-4559-9016-e56f9947e6c1

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_001
import Definitions.Def_D1Bound5_OneSmallN2FixedArithmetic_Definitions

section
namespace D1Bound5
open QuadInt







set_option maxRecDepth 100000
set_option maxHeartbeats 0































































































theorem _root_.solution :
    FiniteN2FixedBound oneSmallCutoffRow_23 finiteN2CutoffWeights_23 := by
  decide +kernel







































































































































end D1Bound5
end
