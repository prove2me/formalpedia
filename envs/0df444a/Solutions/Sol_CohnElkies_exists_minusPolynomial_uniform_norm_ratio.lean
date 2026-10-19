-- Prove2me | solution 1 for CohnElkies.exists_minusPolynomial_uniform_norm_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:25.301796+00:00
-- url     : https://prove2.me/submissions/85282c9e-fe5c-4c32-80cb-4c84bb104842

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddle_one_add_abs_cube_le
import Theorems.Thm_CohnElkies_minusPolynomial_imaginary_norm_ge_three_beta
import Theorems.Thm_CohnElkies_minusPolynomial_imaginary_cubic_growth_le
import Theorems.Thm_CohnElkies_saddle_complex_frequency_norm_le

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
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ u : ℝ, 1 + ε / 4 ≤ u → ∀ T : ℝ,
        ‖minusPolynomial ε
            ((T : ℂ) + Complex.I * (u : ℂ))‖ /
          ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ ≤
            C * (1 + |T| ^ 3) := by
  have hb : 0 < beta ε := beta_pos hε
  refine ⟨4 * (1 + beta ε) * (9 / beta ε + 6),
    by positivity, ?_⟩
  intro u hu T
  let z : ℂ := (T : ℂ) + Complex.I * (u : ℂ)
  let D : ℝ := ‖minusPolynomial ε (Complex.I * (u : ℂ))‖
  have hD : 0 < D := by
    have h := minusPolynomial_imaginary_norm_ge_three_beta
      hε hu
    change 3 * beta ε ≤ D at h
    nlinarith
  have htriangle :
      1 + ‖z‖ ≤ (1 + |T|) * (1 + |u|) := by
    have hz := saddle_complex_frequency_norm_le T u
    change ‖z‖ ≤ |T| + |u| at hz
    nlinarith [mul_nonneg (abs_nonneg T) (abs_nonneg u)]
  have hpower :
      (1 + ‖z‖) ^ 3 ≤
        ((1 + |T|) * (1 + |u|)) ^ 3 :=
    pow_le_pow_left₀ (by positivity) htriangle 3
  have hbase := norm_minusPolynomial_le ε z
  rw [abs_of_pos hb] at hbase
  have hfrequency := saddle_one_add_abs_cube_le T
  have hheight := minusPolynomial_imaginary_cubic_growth_le
    hε hu
  change ‖minusPolynomial ε z‖ / D ≤
    (4 * (1 + beta ε) * (9 / beta ε + 6)) *
      (1 + |T| ^ 3)
  apply (div_le_iff₀ hD).2
  calc
    ‖minusPolynomial ε z‖ ≤
        (1 + beta ε) * (1 + ‖z‖) ^ 3 := hbase
    _ ≤ (1 + beta ε) *
        ((1 + |T|) * (1 + |u|)) ^ 3 := by
      gcongr
    _ = (1 + beta ε) * (1 + |T|) ^ 3 *
        (1 + |u|) ^ 3 := by
      ring
    _ ≤ (1 + beta ε) *
        (4 * (1 + |T| ^ 3)) *
          ((9 / beta ε + 6) * D) := by
      gcongr
    _ = ((4 * (1 + beta ε) * (9 / beta ε + 6)) *
        (1 + |T| ^ 3)) * D := by
      ring
end CohnElkies
