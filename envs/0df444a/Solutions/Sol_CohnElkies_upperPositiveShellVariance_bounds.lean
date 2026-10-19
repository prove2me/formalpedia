-- Prove2me | solution 1 for CohnElkies.upperPositiveShellVariance_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:26.273981+00:00
-- url     : https://prove2.me/submissions/1b965c91-3028-44c5-bed3-89cb61a7292d

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_cosh_ratio_lower

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
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 ≤ δ) :
    (1 / 2 : ℝ) * (shellLocation ε) ^ 2 *
        shellWeight ε *
          Real.exp (δ * shellLocation ε) ≤
      upperPositiveShellVariance ε δ ∧
    upperPositiveShellVariance ε δ ≤
      (shellLocation ε + 1) ^ 2 *
        shellWeight ε *
          Real.exp (δ * (shellLocation ε + 1)) := by
  let B : ℝ := shellLocation ε
  let lo : ℝ := (1 / 2 : ℝ) * B ^ 2 *
    shellWeight ε * Real.exp (δ * B)
  let hi : ℝ := (B + 1) ^ 2 *
    shellWeight ε * Real.exp (δ * (B + 1))
  have hB : 0 ≤ B := by
    try dsimp [B, shellLocation]
    positivity
  have hQ : 0 < shellWeight ε := shellWeight_pos ε
  have horder : B ≤ B + 1 := by linarith
  have hcont : Continuous (fun a : ℝ =>
      positiveShellDensity ε a * a ^ 2 *
        Real.cosh ((1 + δ) * a)) := by
    have hdensity := positiveShellDensity_continuous ε
    fun_prop
  have hlopoint :
      ∀ a ∈ Set.Icc B (B + 1),
        lo ≤ positiveShellDensity ε a * a ^ 2 *
          Real.cosh ((1 + δ) * a) := by
    intro a ha
    have ha0 : 0 ≤ a := hB.trans ha.1
    have hsquare : B ^ 2 ≤ a ^ 2 := by
      exact pow_le_pow_left₀ hB ha.1 2
    have hratio :
        Real.exp (δ * B) / 2 ≤
          Real.cosh ((1 + δ) * a) /
            Real.cosh a := by
      calc
        Real.exp (δ * B) / 2 ≤
          Real.exp (δ * a) / 2 := by
            apply div_le_div_of_nonneg_right
              (Real.exp_le_exp.mpr
                (mul_le_mul_of_nonneg_left ha.1 hδ))
              (by norm_num)
        _ ≤ Real.cosh ((1 + δ) * a) /
          Real.cosh a := cosh_ratio_lower ha0 hδ
    calc
      lo = shellWeight ε * B ^ 2 *
          (Real.exp (δ * B) / 2) := by
        try dsimp [lo]
        ring
      _ ≤ shellWeight ε * a ^ 2 *
          (Real.cosh ((1 + δ) * a) /
            Real.cosh a) := by
        gcongr
      _ = positiveShellDensity ε a * a ^ 2 *
          Real.cosh ((1 + δ) * a) := by
        unfold positiveShellDensity
        ring
  have hhipoint :
      ∀ a ∈ Set.Icc B (B + 1),
        positiveShellDensity ε a * a ^ 2 *
          Real.cosh ((1 + δ) * a) ≤ hi := by
    intro a ha
    have ha0 : 0 ≤ a := hB.trans ha.1
    have hsquare : a ^ 2 ≤ (B + 1) ^ 2 := by
      exact pow_le_pow_left₀ ha0 ha.2 2
    have hratio :
        Real.cosh ((1 + δ) * a) /
          Real.cosh a ≤
            Real.exp (δ * (B + 1)) :=
      (cosh_ratio_upper ha0 hδ).trans
        (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left ha.2 hδ))
    calc
      positiveShellDensity ε a * a ^ 2 *
          Real.cosh ((1 + δ) * a) =
        shellWeight ε * a ^ 2 *
          (Real.cosh ((1 + δ) * a) /
            Real.cosh a) := by
        unfold positiveShellDensity
        ring
      _ ≤ shellWeight ε * (B + 1) ^ 2 *
          Real.exp (δ * (B + 1)) := by
        gcongr
      _ = hi := by
        try dsimp [hi]
        ring
  have hlower := intervalIntegral.integral_mono_on
    (μ := volume) horder
    ((continuous_const : Continuous
      (fun _ : ℝ => lo)).intervalIntegrable _ _)
    (hcont.intervalIntegrable _ _)
    hlopoint
  have hupper := intervalIntegral.integral_mono_on
    (μ := volume) horder
    (hcont.intervalIntegrable _ _)
    ((continuous_const : Continuous
      (fun _ : ℝ => hi)).intervalIntegrable _ _)
    hhipoint
  change lo ≤ upperPositiveShellVariance ε δ ∧
    upperPositiveShellVariance ε δ ≤ hi
  constructor
  · simpa [upperPositiveShellVariance, B] using! hlower
  · simpa [upperPositiveShellVariance, B] using! hupper
end CohnElkies
