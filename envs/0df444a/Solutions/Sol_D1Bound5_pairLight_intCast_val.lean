-- Prove2me | solution 1 for D1Bound5.pairLight_intCast_val
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:48:11.757302+00:00
-- url     : https://prove2.me/submissions/b4cff397-e475-4911-a210-d09e6ccff3d7

import Init
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

section
namespace D1Bound5











/-- This is the pinned integer-cast residue identity, including negative z
and modulus one. The modulus k+1 supplies the required nonzero instance. -/
theorem _root_.solution (k : ℕ) (z : ℤ) :
    (z : ZMod (k + 1)).val = (z % Int.ofNat (k + 1)).toNat := by
  simpa only [Int.toNat_natCast, Int.ofNat_eq_natCast] using
    congrArg Int.toNat (ZMod.val_intCast (n := k + 1) z)





























end D1Bound5
end
