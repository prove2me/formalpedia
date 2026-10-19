-- Prove2me | solution 1 for CohnElkies.exists_plusPolynomial_uniform_central_window
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.968836+00:00
-- url     : https://prove2.me/submissions/12de1b3f-28c6-49a1-b6ca-05c44ec6744f

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_exists_plusPolynomial_uniform_difference_bound

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {ε κ : ℝ} (hε : 0 < ε) (hκ : 0 < κ) :
    ∃ R : ℝ, 0 < R ∧
      ∀ u : ℝ, -1 ≤ u →
        ∀ T : ℝ, |T| ≤ R →
          ‖plusPolynomial ε
              ((T : ℂ) + Complex.I * (u : ℂ)) -
            plusPolynomial ε (Complex.I * (u : ℂ))‖ ≤
            κ * ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_plusPolynomial_uniform_difference_bound hε
  let R : ℝ := min 1 (κ / (2 * C))
  have hR : 0 < R := by
    try dsimp [R]
    positivity
  refine ⟨R, hR, ?_⟩
  intro u hu T hT
  have hTunit : |T| ≤ 1 :=
    hT.trans (min_le_left _ _)
  have hcube : |T| ^ 3 ≤ |T| := by
    have hfactor :
        0 ≤ |T| * (1 - |T|) * (1 + |T|) := by
      exact mul_nonneg
        (mul_nonneg (abs_nonneg T) (sub_nonneg.mpr hTunit))
        (by positivity)
    nlinarith
  have hscale : 2 * C * R ≤ κ := by
    have hmin : R ≤ κ / (2 * C) := min_le_right _ _
    have hfactor : 0 < 2 * C := by positivity
    nlinarith [(le_div_iff₀ hfactor).mp hmin]
  calc
    ‖plusPolynomial ε
        ((T : ℂ) + Complex.I * (u : ℂ)) -
      plusPolynomial ε (Complex.I * (u : ℂ))‖ ≤
      C * (|T| + |T| ^ 3) *
        ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ :=
      hbound u hu T
    _ ≤ (2 * C * R) *
        ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      calc
        C * (|T| + |T| ^ 3) ≤ C * (2 * R) := by
          apply mul_le_mul_of_nonneg_left _ hC.le
          linarith
        _ = 2 * C * R := by ring
    _ ≤ κ * ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ := by
      exact mul_le_mul_of_nonneg_right hscale (norm_nonneg _)
end CohnElkies
