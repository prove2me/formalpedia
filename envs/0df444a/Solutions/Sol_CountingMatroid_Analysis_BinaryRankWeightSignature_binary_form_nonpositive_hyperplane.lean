-- Prove2me | solution 1 for CountingMatroid.Analysis.BinaryRankWeightSignature.binary_form_nonpositive_hyperplane
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T14:45:47.892503+00:00
-- url     : https://prove2.me/submissions/4a2be4e1-6e2b-40a3-a069-35bebc4e6dc0

import Definitions.Def_CountingMatroid_Analysis_QuadraticNonpositiveHyperplane
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Signature

namespace CountingMatroid.Analysis.BinaryRankWeightSignature
end CountingMatroid.Analysis.BinaryRankWeightSignature
set_option autoImplicit false

/-!
The two-element rank-weight signature calculation. Submodularity bounds the
pair coefficient by the product of the singleton coefficients. The resulting
quadratic has a nonpositive hyperplane, as seen by completing two squares.
-/

namespace CountingMatroid.Analysis.BinaryRankWeightSignature
end CountingMatroid.Analysis.BinaryRankWeightSignature
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.BinaryRankWeightSignature

open QuadraticNonpositiveHyperplane
open scoped BigOperators

/-- INTERNAL: The elementary quadratic rank-weight form has a nonpositive
hyperplane whenever its mixed coefficient lies between zero and the product
of its singleton coefficients.
TEXLINE: main.tex:334-348 -/
theorem solution {V : Type} [AddCommGroup V] [Module ℝ V]
    (z x y : V →ₗ[ℝ] ℝ) (b c d : ℝ) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 ≤ d) (hbc : d ≤ b * c) :
    HasNonpositiveHyperplane
      ((2 : ℝ) • QuadraticMap.linMulLin z z + (2 * b) • QuadraticMap.linMulLin z x +
        (2 * c) • QuadraticMap.linMulLin z y + (2 * d) • QuadraticMap.linMulLin x y) := by
  refine ⟨(2 : ℝ) • z + b • x + c • y, ?_⟩
  intro v hv
  simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at hv
  have hz : z v = -(b * x v + c * y v) / 2 := by linarith
  have hneg : 0 ≤ (b * c - d) * (b * x v + c * y v) ^ 2 +
      d * (b * x v - c * y v) ^ 2 :=
    add_nonneg (mul_nonneg (sub_nonneg.mpr hbc) (sq_nonneg _))
      (mul_nonneg hd (sq_nonneg _))
  have hidentity : 2 * b * c *
      (2 * (z v * z v) + (2 * b) * (z v * x v) +
        (2 * c) * (z v * y v) + (2 * d) * (x v * y v)) =
      -((b * c - d) * (b * x v + c * y v) ^ 2 +
        d * (b * x v - c * y v) ^ 2) := by
    rw [hz]
    ring
  have hscale : 0 < 2 * b * c := by positivity
  simp only [QuadraticMap.add_apply, QuadraticMap.smul_apply,
    QuadraticMap.linMulLin_apply, smul_eq_mul]
  apply (mul_le_mul_iff_left₀ hscale).mp
  rw [zero_mul, mul_comm, hidentity]
  exact neg_nonpos.mpr hneg
