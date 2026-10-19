-- Prove2me | solution 1 for CohnElkies.exists_minusPolynomial_uniform_difference_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:25.301796+00:00
-- url     : https://prove2.me/submissions/5e9f454b-ca6e-4082-9c5b-d7a071022d51

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_minusPolynomial_imaginary_norm_ge_three_beta
import Theorems.Thm_CohnElkies_minusPolynomial_imaginary_cubic_growth_le
import Theorems.Thm_CohnElkies_minusPolynomial_translation_norm_le

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
              ((T : ℂ) + Complex.I * (u : ℂ)) -
            minusPolynomial ε (Complex.I * (u : ℂ))‖ /
          ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ ≤
            C * (|T| + |T| ^ 3) := by
  have hb : 0 < beta ε := beta_pos hε
  refine ⟨9 * (9 / beta ε + 6), by positivity, ?_⟩
  intro u hu T
  let D : ℝ := ‖minusPolynomial ε (Complex.I * (u : ℂ))‖
  let S : ℝ := |T| + |T| ^ 3
  have hD : 0 < D := by
    have h := minusPolynomial_imaginary_norm_ge_three_beta
      hε hu
    change 3 * beta ε ≤ D at h
    nlinarith
  have hS : 0 ≤ S := by
    try dsimp [S]
    positivity
  have hsquare : (1 + |u|) ^ 2 ≤ (1 + |u|) ^ 3 := by
    have hfactor :
        0 ≤ |u| * (1 + |u|) ^ 2 :=
      mul_nonneg (abs_nonneg u) (sq_nonneg _)
    nlinarith
  have hgrowth := minusPolynomial_imaginary_cubic_growth_le
    hε hu
  have hquadratic :
      (1 + |u|) ^ 2 ≤ (9 / beta ε + 6) * D :=
    hsquare.trans hgrowth
  change
    ‖minusPolynomial ε
          ((T : ℂ) + Complex.I * (u : ℂ)) -
        minusPolynomial ε (Complex.I * (u : ℂ))‖ / D ≤
      (9 * (9 / beta ε + 6)) * S
  apply (div_le_iff₀ hD).2
  calc
    ‖minusPolynomial ε
          ((T : ℂ) + Complex.I * (u : ℂ)) -
        minusPolynomial ε (Complex.I * (u : ℂ))‖ ≤
      9 * (1 + |u|) ^ 2 * S :=
        minusPolynomial_translation_norm_le ε u T
    _ ≤ 9 * ((9 / beta ε + 6) * D) * S := by
      gcongr
    _ = ((9 * (9 / beta ε + 6)) * S) * D := by
      ring
end CohnElkies
