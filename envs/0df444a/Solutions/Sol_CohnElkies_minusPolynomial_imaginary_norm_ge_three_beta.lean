-- Prove2me | solution 1 for CohnElkies.minusPolynomial_imaginary_norm_ge_three_beta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:25.301796+00:00
-- url     : https://prove2.me/submissions/908b53d9-af17-4075-b43a-9f03f9e50221

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_minusPolynomial_imaginary_re_neg

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {ε u : ℝ} (hε : 0 < ε)
    (hu : 1 + ε / 4 ≤ u) :
    3 * beta ε ≤
      ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ := by
  have hb : 0 < beta ε := beta_pos hε
  have hone : 1 ≤ u := by linarith
  have hbeta : beta ε ≤ u - 1 := by
    unfold beta
    linarith
  have hsquare : (4 : ℝ) ≤ (1 + u) ^ 2 := by
    nlinarith [sq_nonneg (u - 1)]
  have hproduct :
      4 * beta ε ≤ (u - 1) * (1 + u) ^ 2 := by
    calc
      4 * beta ε = beta ε * 4 := by ring
      _ ≤ (u - 1) * (1 + u) ^ 2 :=
        mul_le_mul hbeta hsquare (by norm_num) (by linarith)
  have hnegative := minusPolynomial_imaginary_re_neg hε hu
  rw [minusPolynomial_imaginary, Complex.norm_real,
    Real.norm_eq_abs]
  have harg : beta ε + (1 - u) * (1 + u) ^ 2 < 0 := by
    rw [minusPolynomial_imaginary, Complex.ofReal_re]
      at hnegative
    exact hnegative
  rw [abs_of_neg harg]
  nlinarith
end CohnElkies
