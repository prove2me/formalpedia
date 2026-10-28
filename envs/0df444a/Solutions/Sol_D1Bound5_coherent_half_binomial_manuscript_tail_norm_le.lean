-- Prove2me | solution 1 for D1Bound5.coherent_half_binomial_manuscript_tail_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:27:44.926471+00:00
-- url     : https://prove2.me/submissions/4c41b064-c59e-4f76-baaa-805b4753947f

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
import Definitions.Def_D1Bound5_ComplexHalfBinomial_Definitions
import Definitions.Def_D1Bound5_HalfBinomialCoefficients_Definitions
import Theorems.Thm_D1Bound5_coherent_half_binomial_full_tail_norm_le

section
open Finset Polynomial

namespace D1Bound5













end D1Bound5




open Finset

namespace D1Bound5



end D1Bound5




open Finset

namespace D1Bound5

/-- The complete homogeneous remainder estimate in the manuscript's
parameters.  There are exactly `s.card` reciprocal anchors.  The estimate
applies to the genuine complex half-binomial coefficients, and the full
series defining `F_m` is proved summable. -/
theorem _root_.solution
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → ℂ) (hs : s.Nonempty)
    (x y : ℂ) (A P : ℝ)
    (hA : 0 < A) (hP : 0 < P)
    (ha : ∀ i ∈ s, A ≤ ‖a i‖)
    (hx : ‖x‖ ≤ 1 / P) (hy : ‖y‖ ≤ 1 / P)
    (hAP : 1 < A * P) :
    Summable (fun j : ℕ => halfBinomialWeightedCoeff x y (s.card + j) *
      MvPolynomial.aeval (fun i : s => (a i)⁻¹)
        (MvPolynomial.hsymm s ℂ j)) ∧
    ‖(∑' j : ℕ, halfBinomialWeightedCoeff x y (s.card + j) *
      MvPolynomial.aeval (fun i : s => (a i)⁻¹)
        (MvPolynomial.hsymm s ℂ j)) -
      halfBinomialWeightedCoeff x y s.card‖ ≤
      (4 * |halfBinomialCoeff (s.card + 1)|) / P ^ s.card *
        (1 / (1 - 1 / (A * P)) ^ s.card - 1) := by
  letI : Nonempty s := ⟨⟨hs.choose, hs.choose_spec⟩⟩
  have hrecip : ∀ i : s, ‖(a i)⁻¹‖ ≤ 1 / A := by
    intro i
    simpa only [one_div, norm_inv] using
      one_div_le_one_div_of_le hA (ha i i.2)
  have hprod : (1 / A) * (1 / P) = 1 / (A * P) := by
    simp only [one_div, mul_inv_rev]
    ring
  have hradius : (1 / A) * (1 / P) < 1 := by
    rw [hprod]
    exact (div_lt_one (mul_pos hA hP)).2 hAP
  obtain ⟨hfull, hbound⟩ := coherent_half_binomial_full_tail_norm_le
    (fun i : s => (a i)⁻¹) x y s.card (1 / A) (1 / P)
    (by have := hs.card_pos; omega) (by positivity) (by positivity)
    hrecip hx hy hradius
  refine ⟨hfull, ?_⟩
  rw [hprod, Fintype.card_coe] at hbound
  simpa only [one_div, inv_pow, div_eq_mul_inv, one_mul] using hbound



end D1Bound5




namespace D1Bound5









end D1Bound5
end
