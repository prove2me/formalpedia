-- Prove2me | solution 1 for D1Bound5.crossBlock_growth_of_scaled_determinant
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:33:23.567397+00:00
-- url     : https://prove2.me/submissions/4311dbf2-de44-4b3f-bddc-a9efb8ffc7cb

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

section
open scoped BigOperators NumberField
open Module

namespace D1Bound5









/-- The final real arithmetic of the cross-block argument, in a form that
does not use square roots or division by a possibly zero determinant. -/
theorem _root_.solution
    (W0 W1 W2 d : ℝ) (hW0 : 9 ≤ W0) (hW1 : 9 ≤ W1) (hW2 : 9 ≤ W2)
    (hd : 0 ≤ d) (hlower : (W0*W1*W2)^3 ≤ d^2)
    (hupper : d < (5/2 : ℝ)*W2^2*W1) :
    W0^3*W1/7 < W2 := by
  have hW1p : 0 < W1 := by linarith
  have hW2p : 0 < W2 := by linarith
  have hupperp : 0 < (5/2 : ℝ)*W2^2*W1 := by positivity
  have hsquare : d^2 < ((5/2 : ℝ)*W2^2*W1)^2 := by
    nlinarith only [mul_pos (sub_pos.mpr hupper) (add_pos_of_pos_of_nonneg hupperp hd)]
  have hmul : (W0^3*W1)*(W1^2*W2^3) <
      ((25/4 : ℝ)*W2)*(W1^2*W2^3) := by
    nlinarith only [hlower, hsquare]
  have hcancel : W0^3*W1 < (25/4 : ℝ)*W2 := by
    by_contra hbad
    have hnonneg := mul_nonneg (sub_nonneg.mpr (le_of_not_gt hbad))
      (by positivity : 0 ≤ W1^2*W2^3)
    nlinarith only [hmul, hnonneg]
  nlinarith only [hcancel, hW2p]

end D1Bound5
end
