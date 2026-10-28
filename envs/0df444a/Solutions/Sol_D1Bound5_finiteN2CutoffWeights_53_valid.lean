-- Prove2me | solution 1 for D1Bound5.finiteN2CutoffWeights_53_valid
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:15:56.752548+00:00
-- url     : https://prove2.me/submissions/a7588794-1112-407d-a3d2-a7909efe389c

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
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_002
import Definitions.Def_D1Bound5_OneSmallN2FixedArithmetic_Definitions

section
namespace D1Bound5
open QuadInt







set_option maxRecDepth 100000
set_option maxHeartbeats 0























































































































































































































theorem _root_.solution :
    FiniteN2FixedBound oneSmallCutoffRow_53 finiteN2CutoffWeights_53 := by
  decide +kernel















end D1Bound5
end
