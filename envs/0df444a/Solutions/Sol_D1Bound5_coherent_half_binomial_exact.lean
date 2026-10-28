-- Prove2me | solution 1 for D1Bound5.coherent_half_binomial_exact
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:47:21.383495+00:00
-- url     : https://prove2.me/submissions/30f97d78-26d5-4b9b-8d8c-50c7cecd790e

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
import Theorems.Thm_D1Bound5_coherent_interpolation_series_exact
import Theorems.Thm_D1Bound5_halfBinomialCoeff_weighted_hasSum

section
open Finset Polynomial

namespace D1Bound5







/-- The manuscript's exact coherent interpolation identity for the actual
principal square-root products, before multiplying by the Vandermonde and
the chosen square root of `pq`.  All analytic convergence is proved. -/
theorem _root_.solution
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → ℂ) (hs : s.Nonempty)
    (ha : ∀ i ∈ s, a i ≠ 0) (hinj : Set.InjOn a s)
    (x y : ℂ)
    (hx : ∀ i ∈ s, ‖x * (a i)⁻¹‖ < 1)
    (hy : ∀ i ∈ s, ‖y * (a i)⁻¹‖ < 1) :
    Summable (fun k : ℕ => halfBinomialWeightedCoeff x y (s.card + k) *
      MvPolynomial.aeval (fun i : s => (a i)⁻¹)
        (MvPolynomial.hsymm s ℂ k)) ∧
    (∑ i ∈ s, ((a i) ^ (s.card - 1) /
      (∏ j ∈ s.erase i, (a i - a j))) *
        (((1 + x * (a i)⁻¹) ^ (1 / 2 : ℂ)) *
          ((1 + y * (a i)⁻¹) ^ (1 / 2 : ℂ)))) =
      1 + ((-1 : ℂ) ^ (s.card - 1) * (∏ i ∈ s, a i)⁻¹) *
        ∑' k : ℕ, halfBinomialWeightedCoeff x y (s.card + k) *
          MvPolynomial.aeval (fun i : s => (a i)⁻¹)
            (MvPolynomial.hsymm s ℂ k) := by
  have h := coherent_interpolation_series_exact s a hs ha hinj
    (halfBinomialWeightedCoeff x y)
    (fun i => ((1 + x * (a i)⁻¹) ^ (1 / 2 : ℂ)) *
      ((1 + y * (a i)⁻¹) ^ (1 / 2 : ℂ)))
    (fun i hi => halfBinomialCoeff_weighted_hasSum x y (a i)⁻¹ (hx i hi) (hy i hi))
  simpa [halfBinomialWeightedCoeff, halfBinomialCoeff] using h





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
