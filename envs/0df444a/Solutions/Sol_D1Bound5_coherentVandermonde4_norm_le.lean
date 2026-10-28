-- Prove2me | solution 1 for D1Bound5.coherentVandermonde4_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:27:41.963693+00:00
-- url     : https://prove2.me/submissions/05f46d9c-0283-41f9-845a-a5117bda9926

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Definitions.Def_D1Bound5_CoherentPolynomialWeights_Definitions

section
open Finset

namespace D1Bound5

/-- The exact 24-monomial expansion of the four-anchor Vandermonde
has the sorted modulus bound used in the direct-four estimate. -/
theorem _root_.solution
    (a : Fin 4 → ℂ)
    (h01 : ‖a 0‖ ≤ ‖a 1‖) (h12 : ‖a 1‖ ≤ ‖a 2‖)
    (h23 : ‖a 2‖ ≤ ‖a 3‖) :
    ‖coherentVandermonde4 a‖ ≤ 24 * ‖a 1‖ * ‖a 2‖^2 * ‖a 3‖^3 := by
  let v : Fin 24 → ℂ := ![(a 1 * a 2 * a 2 * a 3 * a 3 * a 3),
    -(a 1 * a 2 * a 2 * a 2 * a 3 * a 3),
    -(a 1 * a 1 * a 2 * a 3 * a 3 * a 3),
    (a 1 * a 1 * a 2 * a 2 * a 2 * a 3),
    (a 1 * a 1 * a 1 * a 2 * a 3 * a 3),
    -(a 1 * a 1 * a 1 * a 2 * a 2 * a 3),
    -(a 0 * a 2 * a 2 * a 3 * a 3 * a 3),
    (a 0 * a 2 * a 2 * a 2 * a 3 * a 3),
    (a 0 * a 1 * a 1 * a 3 * a 3 * a 3),
    -(a 0 * a 1 * a 1 * a 2 * a 2 * a 2),
    -(a 0 * a 1 * a 1 * a 1 * a 3 * a 3),
    (a 0 * a 1 * a 1 * a 1 * a 2 * a 2),
    (a 0 * a 0 * a 2 * a 3 * a 3 * a 3),
    -(a 0 * a 0 * a 2 * a 2 * a 2 * a 3),
    -(a 0 * a 0 * a 1 * a 3 * a 3 * a 3),
    (a 0 * a 0 * a 1 * a 2 * a 2 * a 2),
    (a 0 * a 0 * a 1 * a 1 * a 1 * a 3),
    -(a 0 * a 0 * a 1 * a 1 * a 1 * a 2),
    -(a 0 * a 0 * a 0 * a 2 * a 3 * a 3),
    (a 0 * a 0 * a 0 * a 2 * a 2 * a 3),
    (a 0 * a 0 * a 0 * a 1 * a 3 * a 3),
    -(a 0 * a 0 * a 0 * a 1 * a 2 * a 2),
    -(a 0 * a 0 * a 0 * a 1 * a 1 * a 3),
    (a 0 * a 0 * a 0 * a 1 * a 1 * a 2)]
  have heq : coherentVandermonde4 a = ∑ i, v i := by
    simp [coherentVandermonde4, v, Fin.sum_univ_succ]
    ring
  have hv (i : Fin 24) : ‖v i‖ ≤ ‖a 1‖ * ‖a 2‖^2 * ‖a 3‖^3 := by
    have heq : ‖a 1‖ * ‖a 2‖^2 * ‖a 3‖^3 =
        ‖a 1‖ * ‖a 2‖ * ‖a 2‖ * ‖a 3‖ * ‖a 3‖ * ‖a 3‖ := by ring
    rw [heq]
    fin_cases i <;> norm_num [v, norm_mul]
    all_goals gcongr <;> linarith
  rw [heq]
  calc
    ‖∑ i, v i‖ ≤ ∑ i, ‖v i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 24, ‖a 1‖ * ‖a 2‖^2 * ‖a 3‖^3 :=
      Finset.sum_le_sum (fun i _ => hv i)
    _ = _ := by simp; ring

end D1Bound5
end
