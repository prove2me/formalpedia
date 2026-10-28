-- Prove2me | solution 1 for D1Bound5.coherent_anchor_power_moment_low
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:53:33.528569+00:00
-- url     : https://prove2.me/submissions/ec882686-f603-4a93-9124-235221eedc0d

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

section
open Finset Polynomial

namespace D1Bound5

/-- The low-degree moments in the coherent interpolation identity.  The
inverse-power form is the one obtained directly from a convergent Taylor
series at each anchor. -/
theorem _root_.solution
    {F ι : Type*} [Field F] [DecidableEq ι]
    (s : Finset ι) (a : ι → F) (hs : s.Nonempty)
    (ha : ∀ i ∈ s, a i ≠ 0) (hinj : Set.InjOn a s)
    (n : ℕ) (hn : n < s.card) :
    (∑ i ∈ s, ((a i) ^ (s.card - 1) /
      (∏ j ∈ s.erase i, (a i - a j))) * ((a i)⁻¹) ^ n) =
      if n = 0 then 1 else 0 := by
  have hterm (i : ι) (hi : i ∈ s) :
      (a i) ^ (s.card - 1) * ((a i)⁻¹) ^ n =
        (a i) ^ (s.card - 1 - n) := by
    rw [inv_pow, ← div_eq_mul_inv]
    apply (div_eq_iff (pow_ne_zero n (ha i hi))).2
    rw [← pow_add]
    congr 1
    omega
  have hsum :
      (∑ i ∈ s, ((a i) ^ (s.card - 1) /
        (∏ j ∈ s.erase i, (a i - a j))) * ((a i)⁻¹) ^ n) =
      ∑ i ∈ s, (a i) ^ (s.card - 1 - n) /
        (∏ j ∈ s.erase i, (a i - a j)) := by
    apply Finset.sum_congr rfl
    intro i hi
    calc
      ((a i) ^ (s.card - 1) /
          (∏ j ∈ s.erase i, (a i - a j))) * ((a i)⁻¹) ^ n =
        ((a i) ^ (s.card - 1) * ((a i)⁻¹) ^ n) /
          (∏ j ∈ s.erase i, (a i - a j)) := by ring
      _ = _ := by rw [hterm i hi]
  rw [hsum]
  have hdeg : ((X : F[X]) ^ (s.card - 1 - n)).degree <
      (s.card : WithBot ℕ) := by
    rw [Polynomial.degree_X_pow]
    exact_mod_cast (show s.card - 1 - n < s.card by omega)
  have h := Lagrange.coeff_eq_sum (s := s) (v := a)
    (P := (X : F[X]) ^ (s.card - 1 - n)) hinj hdeg
  by_cases hn0 : n = 0
  · subst n
    simpa [Polynomial.eval_pow, Polynomial.coeff_X_pow] using h.symm
  · have hne : s.card - 1 - n ≠ s.card - 1 := by omega
    simpa [Polynomial.eval_pow, Polynomial.coeff_X_pow, hne, Ne.symm hne, hn0]
      using h.symm











end D1Bound5




open Finset

namespace D1Bound5



end D1Bound5




open Finset

namespace D1Bound5





end D1Bound5




namespace D1Bound5









end D1Bound5
end
