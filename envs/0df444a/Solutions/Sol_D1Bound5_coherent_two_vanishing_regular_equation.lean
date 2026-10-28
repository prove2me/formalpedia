-- Prove2me | solution 1 for D1Bound5.coherent_two_vanishing_regular_equation
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:16:16.721979+00:00
-- url     : https://prove2.me/submissions/d287f0fa-42a2-4746-b0c8-b294c5fcdc88

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Int.GCD
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

section
namespace D1Bound5

/-- Vanishing of the two-anchor coherent form forces the precise
regular-quadruple equation used in the proof of the strong two-anchor
lemma.  The argument does not divide by any square root, so zero roots
are allowed. -/
theorem _root_.solution
    {F : Type*} [Field F] (a b p q Ra Rb z : F) (hab : a ≠ b)
    (hRa : Ra ^ 2 = (a * p + 1) * (a * q + 1))
    (hRb : Rb ^ 2 = (b * p + 1) * (b * q + 1))
    (hz : z ^ 2 = p * q + 1)
    (hL : Ra - Rb - (a - b) * z = 0) :
    (a + b - p - q) ^ 2 = 4 * (a * b + 1) * (p * q + 1) := by
  have hd : a - b ≠ 0 := sub_ne_zero.mpr hab
  have hlin : z * (Ra + Rb) = (a + b) * p * q + p + q := by
    apply (mul_left_cancel₀ hd)
    linear_combination -(Ra + Rb) * hL + hRa - hRb
  have htwice : 2 * z * Ra = 2 * a * p * q + p + q + a - b := by
    linear_combination hlin + z * hL + (a - b) * hz
  have hsq := congrArg (fun x : F => x ^ 2) htwice
  linear_combination -hsq + 4 * Ra ^ 2 * hz + 4 * (p * q + 1) * hRa



end D1Bound5
end
