-- Prove2me | solution 1 for D1Bound5.coherent_half_binomial_manuscript_anchor_radius
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:34:37.510834+00:00
-- url     : https://prove2.me/submissions/5a28982a-e851-4f24-a586-d9d057a427ad

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













end D1Bound5




open Finset

namespace D1Bound5



end D1Bound5




open Finset

namespace D1Bound5



/-- The manuscript's size assumptions place every anchor evaluation
strictly inside the disk of convergence of the half-binomial series. -/
theorem _root_.solution
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → ℂ) (x : ℂ) (A P : ℝ)
    (hA : 0 < A) (hP : 0 < P)
    (ha : ∀ i ∈ s, A ≤ ‖a i‖)
    (hx : ‖x‖ ≤ 1 / P) (hAP : 1 < A * P) :
    ∀ i ∈ s, ‖x * (a i)⁻¹‖ < 1 := by
  intro i hi
  have hai : ‖(a i)⁻¹‖ ≤ 1 / A := by
    simpa only [one_div, norm_inv] using
      one_div_le_one_div_of_le hA (ha i hi)
  have hprod : (1 / P) * (1 / A) = 1 / (A * P) := by
    simp only [one_div, mul_inv_rev]
  calc
    ‖x * (a i)⁻¹‖ = ‖x‖ * ‖(a i)⁻¹‖ := norm_mul _ _
    _ ≤ (1 / P) * (1 / A) :=
      mul_le_mul hx hai (norm_nonneg _) (by positivity)
    _ = 1 / (A * P) := hprod
    _ < 1 := (div_lt_one (mul_pos hA hP)).2 hAP

end D1Bound5




namespace D1Bound5









end D1Bound5
end
