-- Prove2me | solution 2 for CohnElkies.upperPositiveShellDamping_local_variance_lower
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:38:14.64509+00:00
-- url     : https://prove2.me/submissions/0df002f1-8dbe-42a3-989e-99af27be65bd

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology


theorem solution
    {ε ℓ δ T : ℝ}
    (hε : 0 < ε) (hℓ : 0 ≤ ℓ)
    (hT : |T| ≤ 1 / (2 * (shellLocation ε + 1))) :
    (ℓ / 4) * upperPositiveShellVariance ε δ * T ^ 2 ≤
      positiveShellDamping ε ℓ δ T := by
  unfold positiveShellDamping upperPositiveShellVariance
  have hL : 0 < shellLocation ε := by unfold shellLocation; positivity
  have hcd : Continuous (fun a : ℝ => positiveShellDensity ε a) := by
    unfold positiveShellDensity
    exact continuous_const.div Real.continuous_cosh (fun x => (Real.cosh_pos x).ne')
  have hcC : Continuous (fun a : ℝ => Real.cosh ((1 + δ) * a)) :=
    Real.continuous_cosh.comp (continuous_const.mul continuous_id)
  rw [show ℓ / 4 * (∫ a in shellLocation ε..shellLocation ε + 1,
      positiveShellDensity ε a * a ^ 2 * Real.cosh ((1 + δ) * a)) * T ^ 2 =
      ℓ * ∫ a in shellLocation ε..shellLocation ε + 1,
        positiveShellDensity ε a * a ^ 2 * Real.cosh ((1 + δ) * a) * (T ^ 2 / 4) by
    rw [intervalIntegral.integral_mul_const]; ring]
  apply mul_le_mul_of_nonneg_left _ hℓ
  apply intervalIntegral.integral_mono_on (by linarith)
  · exact (((hcd.mul (continuous_pow 2)).mul hcC).mul continuous_const).intervalIntegrable _ _
  · exact ((hcd.mul hcC).mul (continuous_const.sub (Real.continuous_cos.comp
      (continuous_id.mul continuous_const)))).intervalIntegrable _ _
  intro a ha
  have ha0 : 0 ≤ a := le_trans hL.le ha.1
  have hpos : 0 ≤ positiveShellDensity ε a * Real.cosh ((1 + δ) * a) := by
    unfold positiveShellDensity shellWeight
    have := Real.cosh_pos a
    have := Real.cosh_pos ((1 + δ) * a)
    positivity
  have hx : |a * T| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg ha0]
    have hT0 := abs_nonneg T
    have h1 : a ≤ shellLocation ε + 1 := ha.2
    have h2 : 0 < 2 * (shellLocation ε + 1) := by positivity
    have h3 : |T| * (2 * (shellLocation ε + 1)) ≤ 1 := by rwa [le_div_iff₀ h2] at hT
    nlinarith
  have hcos : (a * T) ^ 2 / 4 ≤ 1 - Real.cos (a * T) := by
    have hb := Real.cos_bound hx
    rw [abs_le] at hb
    have hx2 : (a * T) ^ 2 ≤ 1 := by
      have := sq_abs (a * T); nlinarith [abs_nonneg (a * T)]
    have hx4 : |a * T| ^ 4 = ((a * T) ^ 2) ^ 2 := by rw [← sq_abs (a * T)]; ring
    rw [hx4] at hb
    nlinarith [sq_nonneg (a * T)]
  calc positiveShellDensity ε a * a ^ 2 * Real.cosh ((1 + δ) * a) * (T ^ 2 / 4)
      = (positiveShellDensity ε a * Real.cosh ((1 + δ) * a)) * ((a * T) ^ 2 / 4) := by ring
    _ ≤ (positiveShellDensity ε a * Real.cosh ((1 + δ) * a)) * (1 - Real.cos (a * T)) :=
        mul_le_mul_of_nonneg_left hcos hpos

