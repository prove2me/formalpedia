-- Prove2me | solution 1 for D1Bound5.frontier_three_cubic_cofactor
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:39:08.315087+00:00
-- url     : https://prove2.me/submissions/b9e4d8ac-5f1a-43ed-9550-e62908c9d5b2

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
namespace D1Bound5



/-- The three signed cubic cofactor terms cancel at the leading level.
Retaining this cancellation gives 3K-1/4 instead of the weaker 3K. -/
theorem _root_.solution (p q r : ℂ) (K : ℝ)
    (hp : ‖p-(1/8 : ℂ)‖ ≤ K-1/8)
    (hq : ‖q-(1/8 : ℂ)‖ ≤ K-1/8)
    (hr : ‖r-(1/8 : ℂ)‖ ≤ K-1/8) :
    ‖p-q-r‖ ≤ 3*K-1/4 := by
  have hid : p-q-r = (p-1/8)-(q-1/8)-(r-1/8)-(1/8 : ℂ) := by ring
  rw [hid]
  have h1 := norm_sub_le ((p-1/8)-(q-1/8)-(r-1/8)) (1/8 : ℂ)
  have h2 := norm_sub_le ((p-1/8)-(q-1/8)) (r-1/8)
  have h3 := norm_sub_le (p-(1/8 : ℂ)) (q-1/8)
  rw [show ‖(1/8 : ℂ)‖ = (1/8 : ℝ) by norm_num] at h1
  linarith only [h1, h2, h3, hp, hq, hr]



end D1Bound5
end
