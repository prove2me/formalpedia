-- Prove2me | solution 1 for CohnElkies.upper_shortShellDensity_damping_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:26.273981+00:00
-- url     : https://prove2.me/submissions/8a5534cf-467b-48f8-a421-5a1fc035008a

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_upper_min_frequency_inverse_sq_le
import Theorems.Thm_CohnElkies_upper_shortShell_oscillation_div_sq_le

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
    {ε δ a A : ℝ}
    (hε : 0 < ε) (hδ : 0 ≤ δ)
    (ha : 0 < a) (haA : a ≤ A)
    (hmargin : 0 ≤ shortMargin ε a)
    (T : ℝ) :
    (-shortShellDensity ε a) *
        Real.cosh ((1 + δ) * a) *
          (1 - Real.cos (a * T)) ≤
      Real.exp (δ * A) * min (T ^ 2) 1 *
        (1 + (a ^ 2)⁻¹) := by
  have hmarginone : shortMargin ε a ≤ 1 := by
    unfold shortMargin at hmargin ⊢
    nlinarith [mul_nonneg hε.le (show 0 ≤ 1 + a by linarith)]
  have hnegativeexp : Real.exp (-2 * a) ≤ 1 := by
    exact Real.exp_le_one_iff.mpr (by linarith)
  have hratio :
      Real.cosh ((1 + δ) * a) / Real.cosh a ≤
        Real.exp (δ * A) := by
    exact (cosh_ratio_upper ha.le hδ).trans
      (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left haA hδ))
  have hosc := upper_shortShell_oscillation_div_sq_le ha T
  have hosc_nonneg :
      0 ≤ (1 - Real.cos (a * T)) / (2 * a ^ 2) := by
    exact div_nonneg
      (sub_nonneg.mpr (Real.cos_le_one _))
      (by positivity)
  have hratio_scaled :
      shortMargin ε a * Real.exp (-2 * a) *
          (Real.cosh ((1 + δ) * a) / Real.cosh a) ≤
        shortMargin ε a * Real.exp (-2 * a) *
          Real.exp (δ * A) :=
    mul_le_mul_of_nonneg_left hratio
      (mul_nonneg hmargin (Real.exp_pos _).le)
  have hidentity :
      (-shortShellDensity ε a) *
          Real.cosh ((1 + δ) * a) *
            (1 - Real.cos (a * T)) =
        shortMargin ε a * Real.exp (-2 * a) *
          (Real.cosh ((1 + δ) * a) / Real.cosh a) *
            ((1 - Real.cos (a * T)) / (2 * a ^ 2)) := by
    unfold shortShellDensity
    field_simp [ha.ne', (Real.cosh_pos a).ne']
  rw [hidentity]
  calc
    shortMargin ε a * Real.exp (-2 * a) *
        (Real.cosh ((1 + δ) * a) / Real.cosh a) *
          ((1 - Real.cos (a * T)) / (2 * a ^ 2)) ≤
      (shortMargin ε a * Real.exp (-2 * a) *
        Real.exp (δ * A)) *
          ((1 - Real.cos (a * T)) / (2 * a ^ 2)) :=
      mul_le_mul_of_nonneg_right hratio_scaled hosc_nonneg
    _ ≤
      (1 : ℝ) * 1 * Real.exp (δ * A) *
        min (T ^ 2) ((a ^ 2)⁻¹) := by
      gcongr
    _ = Real.exp (δ * A) *
        min (T ^ 2) ((a ^ 2)⁻¹) := by ring
    _ ≤ Real.exp (δ * A) *
        (min (T ^ 2) 1 * (1 + (a ^ 2)⁻¹)) :=
      mul_le_mul_of_nonneg_left
        (upper_min_frequency_inverse_sq_le ha T)
        (Real.exp_pos _).le
    _ = Real.exp (δ * A) * min (T ^ 2) 1 *
        (1 + (a ^ 2)⁻¹) := by ring
end CohnElkies
