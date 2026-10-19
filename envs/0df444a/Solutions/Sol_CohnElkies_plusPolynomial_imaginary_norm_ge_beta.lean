-- Prove2me | solution 1 for CohnElkies.plusPolynomial_imaginary_norm_ge_beta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:25.301796+00:00
-- url     : https://prove2.me/submissions/ece1a669-ba8a-416a-acc1-90f18b4d37ba

import Mathlib
import Definitions.Def_SpherePacking

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
    {ε u : ℝ} (hε : 0 < ε) (hu : -1 ≤ u) :
    beta ε ≤ ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ := by
  have hb : 0 < beta ε := beta_pos hε
  have hterm : 0 ≤ (1 - u) ^ 2 * (1 + u) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  have hvalue : 0 < beta ε + (1 - u) ^ 2 * (1 + u) :=
    add_pos_of_pos_of_nonneg hb hterm
  rw [plusPolynomial_imaginary, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hvalue]
  linarith
end CohnElkies
