-- Prove2me | solution 1 for D1Bound5.frontier_three_variable_cofactor
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:29:34.43443+00:00
-- url     : https://prove2.me/submissions/83e0fbba-84a5-4690-ab24-f79d48a8d7ba

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
open Matrix

namespace D1Bound5



theorem _root_.solution (p q r : ℂ) (P Q R : ℝ)
    (hp : ‖p-(1/8 : ℂ)‖ ≤ P-1/8)
    (hq : ‖q-(1/8 : ℂ)‖ ≤ Q-1/8)
    (hr : ‖r-(1/8 : ℂ)‖ ≤ R-1/8) : ‖p-q-r‖ ≤ P+Q+R-1/4 := by
  have hid : p-q-r = (p-1/8)-(q-1/8)-(r-1/8)-(1/8 : ℂ) := by ring
  rw [hid]
  have h1 := norm_sub_le ((p-1/8)-(q-1/8)-(r-1/8)) (1/8 : ℂ)
  have h2 := norm_sub_le ((p-1/8)-(q-1/8)) (r-1/8)
  have h3 := norm_sub_le (p-(1/8 : ℂ)) (q-1/8)
  have h18 : ‖(1/8 : ℂ)‖ = (1/8 : ℝ) := by norm_num
  rw [h18] at h1
  linarith only [h1,h2,h3,hp,hq,hr]





end D1Bound5
end
