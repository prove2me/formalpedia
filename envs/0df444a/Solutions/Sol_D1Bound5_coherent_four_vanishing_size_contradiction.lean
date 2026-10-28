-- Prove2me | solution 1 for D1Bound5.coherent_four_vanishing_size_contradiction
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:45:56.561042+00:00
-- url     : https://prove2.me/submissions/ccbca91f-bed3-49f3-9bca-a7a89a2847d6

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.VecNotation
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
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

section
open Finset

namespace D1Bound5





/-- The ordered modulus hypothesis makes the upper bound from
simultaneous vanishing incompatible with the elementary reverse
triangle inequality. -/
theorem _root_.solution
    (A B S T P Q Z : ℝ)
    (hA : 1 ≤ A) (hAB : A ≤ B) (hBS : B ≤ S) (hST : S ≤ T)
    (hTP : T ≤ P) (hPQ : P ≤ Q)
    (hsize : 32*B*S*T/A^3 ≤ P^2)
    (hupper : Z ≤ 121*B*S*T/(4*A^3)) (hlower : P*Q-1 ≤ Z) : False := by
  have hA0 : 0 < A := by linarith
  have hB0 : 0 < B := hA0.trans_le hAB
  have hS0 : 0 < S := hB0.trans_le hBS
  have hT0 : 0 < T := hS0.trans_le hST
  have hP0 : 0 < P := hT0.trans_le hTP
  have hr : 1 ≤ B*S*T/A^3 := by
    apply (le_div_iff₀ (by positivity : 0 < A^3)).2
    have h1 := mul_le_mul hAB (hAB.trans hBS) hA0.le hB0.le
    have h2 := mul_le_mul h1 (hAB.trans (hBS.trans hST)) hA0.le (by positivity : 0 ≤ B*S)
    nlinarith only [h2]
  have hp2 : P^2 ≤ P*Q := by
    have h := mul_le_mul_of_nonneg_left hPQ hP0.le
    nlinarith only [h]
  have hs : 32*(B*S*T/A^3) ≤ P^2 := by
    calc
      _ = 32*B*S*T/A^3 := by ring
      _ ≤ _ := hsize
  have hu : Z ≤ (121/4 : ℝ)*(B*S*T/A^3) := by
    calc
      Z ≤ 121*B*S*T/(4*A^3) := hupper
      _ = _ := by ring
  nlinarith only [hr, hp2, hs, hu, hlower]









end D1Bound5
end
