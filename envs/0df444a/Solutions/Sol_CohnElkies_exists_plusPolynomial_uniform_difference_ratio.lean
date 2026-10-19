-- Prove2me | solution 1 for CohnElkies.exists_plusPolynomial_uniform_difference_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:25.301796+00:00
-- url     : https://prove2.me/submissions/d8bc7710-8e25-4b3d-b862-af561ad6e036

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_plusPolynomial_imaginary_norm_ge_beta
import Theorems.Thm_CohnElkies_plusPolynomial_imaginary_cubic_growth_le
import Theorems.Thm_CohnElkies_plusPolynomial_translation_norm_le

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
      ∀ u : ℝ, -1 ≤ u → ∀ T : ℝ,
        ‖plusPolynomial ε
              ((T : ℂ) + Complex.I * (u : ℂ)) -
            plusPolynomial ε (Complex.I * (u : ℂ))‖ /
          ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ ≤
            C * (|T| + |T| ^ 3) := by
  have hb : 0 < beta ε := beta_pos hε
  refine ⟨9 * (27 / beta ε + 9), by positivity, ?_⟩
  intro u hu T
  let D : ℝ := ‖plusPolynomial ε (Complex.I * (u : ℂ))‖
  let S : ℝ := |T| + |T| ^ 3
  have hD : 0 < D :=
    lt_of_lt_of_le hb (plusPolynomial_imaginary_norm_ge_beta hε hu)
  have hS : 0 ≤ S := by
    try dsimp [S]
    positivity
  have hsquare : (1 + |u|) ^ 2 ≤ (1 + |u|) ^ 3 := by
    have hfactor :
        0 ≤ |u| * (1 + |u|) ^ 2 :=
      mul_nonneg (abs_nonneg u) (sq_nonneg _)
    nlinarith
  have hgrowth := plusPolynomial_imaginary_cubic_growth_le
    hε hu
  have hquadratic :
      (1 + |u|) ^ 2 ≤ (27 / beta ε + 9) * D :=
    hsquare.trans hgrowth
  change
    ‖plusPolynomial ε
          ((T : ℂ) + Complex.I * (u : ℂ)) -
        plusPolynomial ε (Complex.I * (u : ℂ))‖ / D ≤
      (9 * (27 / beta ε + 9)) * S
  apply (div_le_iff₀ hD).2
  calc
    ‖plusPolynomial ε
          ((T : ℂ) + Complex.I * (u : ℂ)) -
        plusPolynomial ε (Complex.I * (u : ℂ))‖ ≤
      9 * (1 + |u|) ^ 2 * S :=
        plusPolynomial_translation_norm_le ε u T
    _ ≤ 9 * ((27 / beta ε + 9) * D) * S := by
      gcongr
    _ = ((9 * (27 / beta ε + 9)) * S) * D := by
      ring
end CohnElkies
