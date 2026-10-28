-- Prove2me | solution 1 for D1Bound5.finiteA5CutoffWeights_10_valid
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:01:08.277872+00:00
-- url     : https://prove2.me/submissions/09b83b7a-2711-4acb-ace2-4e3de0252764

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_FiniteA5FixedHeight_Definitions
import Definitions.Def_D1Bound5_OneSmallA5FixedArithmetic_Definitions
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_001
import Definitions.Def_D1Bound5_OneSmallRows_Definitions

section
namespace D1Bound5
open QuadInt

/- Each exact square certificate evaluates the actual divided A5 root
coefficient in the quadratic integer ring before taking its field norm.
It then checks the printed M5 with a strict rational row-sum comparison. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0











































theorem _root_.solution :
    FiniteA5FixedBound oneSmallCutoffRow_10.triple.anchorA
      oneSmallCutoffRow_10.triple.anchorB oneSmallCutoffRow_10.M5
      finiteA5CutoffWeights_10 := by
  decide +kernel



























































































































































































end D1Bound5
end
