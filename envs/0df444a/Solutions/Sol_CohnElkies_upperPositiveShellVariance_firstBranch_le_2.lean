-- Prove2me | solution 2 for CohnElkies.upperPositiveShellVariance_firstBranch_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:37:31.608984+00:00
-- url     : https://prove2.me/submissions/aaef3b3e-08a8-4b87-8c7e-74848dd19c41

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory
open scoped Topology


theorem solution
    {ε u : ℝ}
    (hε : 0 < ε) (hulower : -1 < u)
    (huupper : u ≤ 1 + ε / 2) :
    upperPositiveShellVariance ε (u - 1) ≤
      upperPositiveShellVariance ε (ε / 2) := by
  unfold upperPositiveShellVariance
  have hL : 0 < shellLocation ε := by unfold shellLocation; positivity
  have hc : ∀ δ : ℝ, Continuous (fun a : ℝ => positiveShellDensity ε a * a ^ 2 * Real.cosh ((1 + δ) * a)) := by
    intro δ
    unfold positiveShellDensity
    exact ((continuous_const.div Real.continuous_cosh (fun x => (Real.cosh_pos x).ne')).mul
      (continuous_pow 2)).mul (Real.continuous_cosh.comp (continuous_const.mul continuous_id))
  apply intervalIntegral.integral_mono_on (by linarith) ((hc _).intervalIntegrable _ _) ((hc _).intervalIntegrable _ _)
  intro a ha
  have ha0 : 0 ≤ a := le_trans hL.le ha.1
  have hd : 0 ≤ positiveShellDensity ε a * a ^ 2 := by
    unfold positiveShellDensity shellWeight
    have := Real.cosh_pos a
    positivity
  apply mul_le_mul_of_nonneg_left _ hd
  rw [Real.cosh_le_cosh, abs_mul, abs_mul, abs_of_nonneg ha0]
  apply mul_le_mul_of_nonneg_right _ ha0
  rw [abs_le]
  have : (0:ℝ) ≤ 1 + ε / 2 := by linarith
  rw [abs_of_nonneg this]
  constructor <;> linarith

