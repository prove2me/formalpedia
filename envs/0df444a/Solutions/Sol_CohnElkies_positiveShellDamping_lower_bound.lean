-- Prove2me | solution 1 for CohnElkies.positiveShellDamping_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.890976+00:00
-- url     : https://prove2.me/submissions/58c9ce65-0558-4c39-b4a1-23e6e1ac517c

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_shellOscillation_lower_bound
import Theorems.Thm_CohnElkies_cosh_ratio_lower

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped ContDiff FourierTransform Interval RealInnerProductSpace Topology
namespace CohnElkies
theorem _root_.solution {ε ℓ δ T : ℝ}
    (hε : 0 < ε) (hℓ : 0 ≤ ℓ) (hδ : 0 ≤ δ) :
    ℓ / 50 * shellWeight ε *
        Real.exp (δ * shellLocation ε) * min (T ^ 2) 1 ≤
      positiveShellDamping ε ℓ δ T := by
  let B : ℝ := shellLocation ε
  let C : ℝ := shellWeight ε * Real.exp (δ * B) / 2
  have hB : 0 ≤ B := by
    try dsimp [B, shellLocation]
    positivity
  have hQ : 0 < shellWeight ε := shellWeight_pos ε
  have hC : 0 ≤ C := by
    try dsimp [C]
    positivity
  have hden : Continuous (fun a : ℝ => positiveShellDensity ε a) := by
    unfold positiveShellDensity
    exact continuous_const.div Real.continuous_cosh
      (fun a => (Real.cosh_pos a).ne')
  have hosc : Continuous (fun a : ℝ => 1 - Real.cos (a * T)) := by
    fun_prop
  have hleft : Continuous
      (fun a : ℝ => C * (1 - Real.cos (a * T))) :=
    continuous_const.mul hosc
  have hcosh : Continuous (fun a : ℝ => Real.cosh ((1 + δ) * a)) := by
    fun_prop
  have hright : Continuous
      (fun a : ℝ => positiveShellDensity ε a *
        Real.cosh ((1 + δ) * a) * (1 - Real.cos (a * T))) :=
    (hden.mul hcosh).mul hosc
  have hpoint : ∀ a ∈ Set.Icc B (B + 1),
      C * (1 - Real.cos (a * T)) ≤
        positiveShellDensity ε a * Real.cosh ((1 + δ) * a) *
          (1 - Real.cos (a * T)) := by
    intro a ha
    have ha0 : 0 ≤ a := hB.trans ha.1
    have he := Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left ha.1 hδ)
    have hratio := cosh_ratio_lower ha0 hδ
    have hbase :
        C ≤ positiveShellDensity ε a * Real.cosh ((1 + δ) * a) := by
      try dsimp [C, positiveShellDensity]
      calc
        shellWeight ε * Real.exp (δ * B) / 2
          ≤ shellWeight ε * Real.exp (δ * a) / 2 := by gcongr
        _ ≤ shellWeight ε *
            (Real.cosh ((1 + δ) * a) / Real.cosh a) := by
          calc
            shellWeight ε * Real.exp (δ * a) / 2 =
              shellWeight ε * (Real.exp (δ * a) / 2) := by ring
            _ ≤ shellWeight ε *
              (Real.cosh ((1 + δ) * a) / Real.cosh a) := by
                exact mul_le_mul_of_nonneg_left hratio hQ.le
        _ = shellWeight ε / Real.cosh a *
              Real.cosh ((1 + δ) * a) := by ring
    exact mul_le_mul_of_nonneg_right hbase
      (sub_nonneg.mpr (Real.cos_le_one _))
  have hmono := intervalIntegral.integral_mono_on
    (μ := volume) (show B ≤ B + 1 by linarith)
    (hleft.intervalIntegrable _ _)
    (hright.intervalIntegrable _ _) hpoint
  have hleftIntegral :
      (∫ a in B..B + 1, C * (1 - Real.cos (a * T))) =
        C * shellOscillation B T := by
    rw [intervalIntegral.integral_const_mul]
    rfl
  rw [hleftIntegral] at hmono
  change ℓ / 50 * shellWeight ε * Real.exp (δ * B) *
      min (T ^ 2) 1 ≤
    ℓ * ∫ a in B..B + 1,
      positiveShellDensity ε a * Real.cosh ((1 + δ) * a) *
        (1 - Real.cos (a * T))
  calc
    ℓ / 50 * shellWeight ε * Real.exp (δ * B) * min (T ^ 2) 1 =
      ℓ * (C * ((1 / 25 : ℝ) * min (T ^ 2) 1)) := by
        try dsimp [C]
        ring
    _ ≤ ℓ * (C * shellOscillation B T) := by
      gcongr
      exact shellOscillation_lower_bound B T
    _ ≤ ℓ * ∫ a in B..B + 1,
        positiveShellDensity ε a * Real.cosh ((1 + δ) * a) *
          (1 - Real.cos (a * T)) := by
      gcongr
end CohnElkies
