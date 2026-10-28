-- Prove2me | solution 1 for D1Bound5.coherent_analytic_anchor_root_sq
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:58:44.674983+00:00
-- url     : https://prove2.me/submissions/e68bcd70-019e-494c-a5a9-522708e0f78a

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





/-- The coherent analytic anchor root has precisely the product square
claimed in the manuscript.  Consequently any integral product root of
the same expression agrees with it up to sign. -/
theorem _root_.solution
    (a p q eta : ℂ) (ha : a ≠ 0) (hp : p ≠ 0) (hq : q ≠ 0)
    (heta : eta ^ 2 = p * q) :
    (a * eta * ((1 + p⁻¹ * a⁻¹) ^ (1 / 2 : ℂ)) *
      ((1 + q⁻¹ * a⁻¹) ^ (1 / 2 : ℂ))) ^ 2 =
      (a * p + 1) * (a * q + 1) := by
  simp only [mul_pow, coherent_cpow_half_sq, heta]
  field_simp [ha, hp, hq] <;> ring



end D1Bound5
end
