-- Prove2me | solution 1 for D1Bound5.unit_pair_three_cubic_gaps
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:47:23.457374+00:00
-- url     : https://prove2.me/submissions/ba563356-7e59-47c7-bd2a-d768036c5597

import Lean.Util.CollectAxioms
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

section
open scoped NumberField
open Module

namespace D1Bound5

/-- Three unit cubic gaps have the exact accumulated denominator 2^13. -/
theorem _root_.solution (S T C D : ℝ) (hS : 9 ≤ S)
    (hST : S^3/2 < T) (hTC : T^3/2 < C) (hCD : C^3/2 < D) :
    S^27/8192 < D := by
  have hS0 : 0 < S := by linarith only [hS]
  have hT0 : 0 < T := lt_trans (by positivity : 0 < S^3/2) hST
  have hC0 : 0 < C := lt_trans (by positivity : 0 < T^3/2) hTC
  have hSTcube : (S^3/2)^3 < T^3 := by gcongr
  have hSC : S^9/16 < C := by nlinarith only [hSTcube,hTC]
  have hSCcube : (S^9/16)^3 < C^3 := by gcongr
  nlinarith only [hSCcube,hCD]



end D1Bound5
end
