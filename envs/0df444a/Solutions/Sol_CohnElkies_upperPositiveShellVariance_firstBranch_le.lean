-- Prove2me | solution 1 for CohnElkies.upperPositiveShellVariance_firstBranch_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.217322+00:00
-- url     : https://prove2.me/submissions/827a10fc-e35d-4471-99dd-44f4d580c89b

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
namespace CohnElkies
theorem _root_.solution
    {ε u : ℝ}
    (hε : 0 < ε) (hulower : -1 < u)
    (huupper : u ≤ 1 + ε / 2) :
    upperPositiveShellVariance ε (u - 1) ≤
      upperPositiveShellVariance ε (ε / 2) := by
  let B : ℝ := shellLocation ε
  have hB : 0 ≤ B := by
    try dsimp [B, shellLocation]
    positivity
  have horder : B ≤ B + 1 := by linarith
  have huabs : |u| ≤ 1 + ε / 2 := by
    apply (abs_le).mpr
    constructor <;> linarith
  have hcont (v : ℝ) : Continuous
      (fun a : ℝ =>
        positiveShellDensity ε a * a ^ 2 *
          Real.cosh (v * a)) := by
    have hdensity := positiveShellDensity_continuous ε
    fun_prop
  have hpoint : ∀ a ∈ Icc B (B + 1),
      positiveShellDensity ε a * a ^ 2 *
          Real.cosh (u * a) ≤
        positiveShellDensity ε a * a ^ 2 *
          Real.cosh ((1 + ε / 2) * a) := by
    intro a ha
    have ha0 : 0 ≤ a := hB.trans ha.1
    have hdensity : 0 ≤ positiveShellDensity ε a := by
      unfold positiveShellDensity
      exact div_nonneg (shellWeight_pos ε).le
        (Real.cosh_pos a).le
    have habs : |u * a| ≤ |(1 + ε / 2) * a| := by
      rw [abs_mul, abs_mul, abs_of_nonneg ha0,
        abs_of_pos (by positivity : 0 < 1 + ε / 2)]
      exact mul_le_mul_of_nonneg_right huabs ha0
    exact mul_le_mul_of_nonneg_left
      (Real.cosh_le_cosh.mpr habs)
      (mul_nonneg hdensity (sq_nonneg a))
  have hmono := intervalIntegral.integral_mono_on
    (μ := volume) horder
    ((hcont u).intervalIntegrable _ _)
    ((hcont (1 + ε / 2)).intervalIntegrable _ _)
    hpoint
  simpa [upperPositiveShellVariance, B] using! hmono
end CohnElkies
