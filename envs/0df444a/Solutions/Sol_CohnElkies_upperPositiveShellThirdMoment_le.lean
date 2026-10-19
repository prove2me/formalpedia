-- Prove2me | solution 1 for CohnElkies.upperPositiveShellThirdMoment_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:26.273981+00:00
-- url     : https://prove2.me/submissions/286aa9fd-d822-46d0-b219-a49700c4c73c

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
    {ε δ : ℝ} (hε : 0 < ε) :
    upperPositiveShellThirdMoment ε δ ≤
      (shellLocation ε + 1) *
        upperPositiveShellVariance ε δ := by
  let B : ℝ := shellLocation ε
  have hB : 0 ≤ B := by
    try dsimp [B, shellLocation]
    positivity
  have horder : B ≤ B + 1 := by
    linarith
  have hdensity := positiveShellDensity_continuous ε
  have hbase : Continuous (fun a : ℝ =>
      positiveShellDensity ε a * a ^ 2 *
        Real.cosh ((1 + δ) * a)) := by
    fun_prop
  have hthird : Continuous (fun a : ℝ =>
      positiveShellDensity ε a * a ^ 3 *
        Real.cosh ((1 + δ) * a)) := by
    fun_prop
  have hright : Continuous (fun a : ℝ =>
      (B + 1) *
        (positiveShellDensity ε a * a ^ 2 *
          Real.cosh ((1 + δ) * a))) :=
    continuous_const.mul hbase
  have hpoint :
      ∀ a ∈ Set.Icc B (B + 1),
        positiveShellDensity ε a * a ^ 3 *
            Real.cosh ((1 + δ) * a) ≤
          (B + 1) *
            (positiveShellDensity ε a * a ^ 2 *
              Real.cosh ((1 + δ) * a)) := by
    intro a ha
    have hdensitynonneg : 0 ≤ positiveShellDensity ε a := by
      unfold positiveShellDensity
      exact div_nonneg (shellWeight_pos ε).le
        (Real.cosh_pos a).le
    have hbasenonneg :
        0 ≤ positiveShellDensity ε a * a ^ 2 *
          Real.cosh ((1 + δ) * a) :=
      mul_nonneg
        (mul_nonneg hdensitynonneg (sq_nonneg a))
        (Real.cosh_pos _).le
    calc
      positiveShellDensity ε a * a ^ 3 *
          Real.cosh ((1 + δ) * a) =
        a * (positiveShellDensity ε a * a ^ 2 *
          Real.cosh ((1 + δ) * a)) := by
            ring
      _ ≤ (B + 1) *
          (positiveShellDensity ε a * a ^ 2 *
            Real.cosh ((1 + δ) * a)) :=
        mul_le_mul_of_nonneg_right ha.2 hbasenonneg
  have hmono := intervalIntegral.integral_mono_on
    (μ := volume) horder
    (hthird.intervalIntegrable _ _)
    (hright.intervalIntegrable _ _)
    hpoint
  simpa [upperPositiveShellThirdMoment,
    upperPositiveShellVariance, B,
    intervalIntegral.integral_const_mul] using! hmono
end CohnElkies
