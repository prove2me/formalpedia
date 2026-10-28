-- Prove2me | solution 1 for D1Bound5.coherent_three_window_scalar
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:24:09.089657+00:00
-- url     : https://prove2.me/submissions/f40c2757-1895-49c2-9673-9a548d8b5b8f

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
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

section
open Finset

namespace D1Bound5





/-- Exact scalar vanishing window in terms of two proved remainder
constants.  The manuscript's rows are obtained by rational comparison. -/
theorem _root_.solution
    (V P Q d F ell u : ℝ) (hV : 0 < V) (hP : 0 < P) (hQ : 0 < Q)
    (hell : 0 < ell) (hu : 0 < u)
    (hdlo : 100/(201*P*Q) < d) (hdhi : d < 100/(199*P*Q))
    (hFlo : ell/P^3 ≤ F) (hFhi : F ≤ u/P^3) (hrel : d = F/V) :
    100*V*P^2/(201*u) < Q ∧ Q < 100*V*P^2/(199*ell) := by
  have hlo : 100/(201*P*Q) < u/(V*P^3) := by
    calc
      _ < d := hdlo
      _ = F/V := hrel
      _ ≤ (u/P^3)/V := div_le_div_of_nonneg_right hFhi hV.le
      _ = _ := by field_simp <;> ring
  have hhi : ell/(V*P^3) < 100/(199*P*Q) := by
    calc
      _ = (ell/P^3)/V := by field_simp <;> ring
      _ ≤ F/V := div_le_div_of_nonneg_right hFlo hV.le
      _ = d := hrel.symm
      _ < _ := hdhi
  constructor
  · apply (div_lt_iff₀ (by positivity : 0 < 201*u)).2
    have h := (div_lt_div_iff₀ (by positivity) (by positivity)).mp hlo
    apply (mul_lt_mul_iff_of_pos_right hP).mp
    nlinarith only [h]
  · apply (lt_div_iff₀ (by positivity : 0 < 199*ell)).2
    have h := (div_lt_div_iff₀ (by positivity) (by positivity)).mp hhi
    apply (mul_lt_mul_iff_of_pos_right hP).mp
    nlinarith only [h]





end D1Bound5
end
