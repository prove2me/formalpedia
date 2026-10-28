-- Prove2me | solution 1 for D1Bound5.coherent_analytic_terminal_root_sq
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:22:51.615825+00:00
-- url     : https://prove2.me/submissions/844a377c-9f9e-4806-bacc-8badf75bdb03

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
import Theorems.Thm_D1Bound5_coherent_cpow_half_sq

section
open Finset Polynomial

namespace D1Bound5













end D1Bound5




open Finset

namespace D1Bound5



end D1Bound5




open Finset

namespace D1Bound5





end D1Bound5




namespace D1Bound5



/-- The chosen coherent terminal root has square `pq + 1`, for either
choice of the square root `eta` of `pq`. -/
theorem _root_.solution
    (p q eta : ℂ) (hp : p ≠ 0) (hq : q ≠ 0)
    (heta : eta ^ 2 = p * q) :
    (eta * ((1 + p⁻¹ * q⁻¹) ^ (1 / 2 : ℂ))) ^ 2 = p * q + 1 := by
  rw [mul_pow, coherent_cpow_half_sq, heta]
  field_simp [hp, hq] <;> ring





end D1Bound5
end
