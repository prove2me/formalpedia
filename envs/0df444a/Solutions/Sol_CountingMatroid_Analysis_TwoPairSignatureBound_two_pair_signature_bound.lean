-- Prove2me | solution 1 for CountingMatroid.Analysis.TwoPairSignatureBound.two_pair_signature_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T09:44:57.887342+00:00
-- url     : https://prove2.me/submissions/b5e2d191-30a2-4a6e-8cf3-72b0c0d3b2a6

import Definitions.Def_CountingMatroid_Analysis_TwoPairSignatureBound
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.Tactic
import Theorems.Thm_CountingMatroid_Analysis_SignatureOrthogonalNonpositive_signature_orthogonal_nonpositive

set_option autoImplicit false

/-! The elementary determinant consequence of the two-pair Hessian signature. -/

namespace CountingMatroid.Analysis.TwoPairSignatureBound
end CountingMatroid.Analysis.TwoPairSignatureBound
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.TwoPairSignatureBound

open scoped Matrix

/-- PAPER: main.tex:408-412
A positive first diagonal and at most one positive direction force the
two-pair Hessian determinant to be nonpositive. -/
theorem solution (a c z : ℚ) (ha : 0 < a)
    (hsig : sigPos (twoPairMatrix a c z).toQuadraticForm' ≤ 1) :
    4 * c * a ≤ z ^ 2 := by
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  let Q := (twoPairMatrix a c z).toQuadraticForm'
  have hcalc (u : Fin 2 → ℝ) :
      Q u = 2 * (a : ℝ) * u 0 ^ 2 +
        2 * (z : ℝ) * u 0 * u 1 + 2 * (c : ℝ) * u 1 ^ 2 := by
    dsimp [Q, twoPairMatrix, Matrix.toQuadraticForm']
    simp [Matrix.toLinearMap₂'_apply', dotProduct, Matrix.mulVec, Fin.sum_univ_succ]
    ring
  let e : Fin 2 → ℝ := ![1, 0]
  let v : Fin 2 → ℝ := ![-(z : ℝ), 2 * (a : ℝ)]
  have he : 0 < Q e := by rw [hcalc]; simp [e]; positivity
  have horth : Q.IsOrtho e v := by
    rw [QuadraticMap.isOrtho_def]
    simp only [hcalc]
    simp [e, v]
    ring
  have hv := SignatureOrthogonalNonpositive.signature_orthogonal_nonpositive
    Q hsig e v he (QuadraticMap.associated_isOrtho.mpr horth)
  rw [hcalc] at hv
  simp only [v, Matrix.cons_val_zero, Matrix.cons_val_one] at hv
  have hprod : (4 * (c : ℝ) * (a : ℝ) - (z : ℝ) ^ 2) * (2 * (a : ℝ)) ≤ 0 := by
    nlinarith [hv]
  have h : 4 * (c : ℝ) * (a : ℝ) ≤ (z : ℝ) ^ 2 :=
    sub_nonpos.mp (nonpos_of_mul_nonpos_left hprod (by positivity))
  exact_mod_cast h
