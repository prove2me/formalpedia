-- Prove2me | solution 1 for CohnElkies.upperPositiveShellDamping_local_variance_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.968836+00:00
-- url     : https://prove2.me/submissions/482ac7d1-5847-43ab-9c9e-1539f8c5eb9e

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_upper_one_sub_cos_quadratic_lower

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {ε ℓ δ T : ℝ}
    (hε : 0 < ε) (hℓ : 0 ≤ ℓ)
    (hT : |T| ≤ 1 / (2 * (shellLocation ε + 1))) :
    (ℓ / 4) * upperPositiveShellVariance ε δ * T ^ 2 ≤
      positiveShellDamping ε ℓ δ T := by
  let B : ℝ := shellLocation ε
  have hB : 0 ≤ B := by
    try dsimp [B, shellLocation]
    positivity
  have hB1 : 0 < B + 1 := by linarith
  have horder : B ≤ B + 1 := by linarith
  have hwindow : (B + 1) * |T| ≤ 1 / 2 := by
    calc
      (B + 1) * |T| ≤
          (B + 1) * (1 / (2 * (B + 1))) := by
            apply mul_le_mul_of_nonneg_left _ (by linarith)
            simpa [B] using! hT
      _ = 1 / 2 := by
        field_simp [hB1.ne']
  have hdensity : Continuous (positiveShellDensity ε) :=
    positiveShellDensity_continuous ε
  have hcosh : Continuous
      (fun a : ℝ => Real.cosh ((1 + δ) * a)) := by
    fun_prop
  have hosc : Continuous
      (fun a : ℝ => 1 - Real.cos (a * T)) := by
    fun_prop
  have hleft : Continuous
      (fun a : ℝ =>
        (positiveShellDensity ε a * a ^ 2 *
          Real.cosh ((1 + δ) * a)) * (T ^ 2 / 4)) :=
    ((hdensity.mul (continuous_id.pow 2)).mul
      hcosh).mul continuous_const
  have hright : Continuous
      (fun a : ℝ =>
        positiveShellDensity ε a *
          Real.cosh ((1 + δ) * a) *
            (1 - Real.cos (a * T))) :=
    (hdensity.mul hcosh).mul hosc
  have hpoint : ∀ a ∈ Icc B (B + 1),
      (positiveShellDensity ε a * a ^ 2 *
        Real.cosh ((1 + δ) * a)) * (T ^ 2 / 4) ≤
          positiveShellDensity ε a *
            Real.cosh ((1 + δ) * a) *
              (1 - Real.cos (a * T)) := by
    intro a ha
    have ha0 : 0 ≤ a := hB.trans ha.1
    have haT : |a * T| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg ha0]
      calc
        a * |T| ≤ (B + 1) * |T| :=
          mul_le_mul_of_nonneg_right ha.2 (abs_nonneg T)
        _ ≤ 1 / 2 := hwindow
        _ ≤ 1 := by norm_num
    have hquadratic := upper_one_sub_cos_quadratic_lower haT
    have hw : 0 ≤
        positiveShellDensity ε a *
          Real.cosh ((1 + δ) * a) := by
      unfold positiveShellDensity
      positivity [shellWeight_pos ε]
    calc
      (positiveShellDensity ε a * a ^ 2 *
          Real.cosh ((1 + δ) * a)) * (T ^ 2 / 4) =
        (positiveShellDensity ε a *
          Real.cosh ((1 + δ) * a)) *
            ((a * T) ^ 2 / 4) := by ring
      _ ≤ (positiveShellDensity ε a *
          Real.cosh ((1 + δ) * a)) *
            (1 - Real.cos (a * T)) :=
        mul_le_mul_of_nonneg_left hquadratic hw
      _ = positiveShellDensity ε a *
          Real.cosh ((1 + δ) * a) *
            (1 - Real.cos (a * T)) := by ring
  have hmono := intervalIntegral.integral_mono_on
    (μ := volume) horder
    (hleft.intervalIntegrable _ _)
    (hright.intervalIntegrable _ _) hpoint
  have hleftvalue :
      (∫ a in B..B + 1,
        (positiveShellDensity ε a * a ^ 2 *
          Real.cosh ((1 + δ) * a)) * (T ^ 2 / 4)) =
        upperPositiveShellVariance ε δ * (T ^ 2 / 4) := by
    rw [intervalIntegral.integral_mul_const]
    rfl
  rw [hleftvalue] at hmono
  unfold positiveShellDamping
  change
    (ℓ / 4) * upperPositiveShellVariance ε δ * T ^ 2 ≤
      ℓ * ∫ a in B..B + 1,
        positiveShellDensity ε a *
          Real.cosh ((1 + δ) * a) *
            (1 - Real.cos (a * T))
  calc
    (ℓ / 4) * upperPositiveShellVariance ε δ * T ^ 2 =
        ℓ * (upperPositiveShellVariance ε δ * (T ^ 2 / 4)) := by
          ring
    _ ≤ ℓ * ∫ a in B..B + 1,
        positiveShellDensity ε a *
          Real.cosh ((1 + δ) * a) *
            (1 - Real.cos (a * T)) :=
      mul_le_mul_of_nonneg_left hmono hℓ
end CohnElkies
