-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.BoxTail.tail_kernel_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:59:32.311426+00:00
-- url     : https://prove2.me/submissions/c719e688-c484-4464-b340-844a6bff4fb6

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TailKernel
import Theorems.Thm_Formalism_HermitianLattices_Ext_BoxTail_tail_kernel_norm_lower
import Theorems.Thm_Formalism_HermitianLattices_Ext_BoxTail_tail_kernel_half

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.BoxTail
namespace Formalism.HermitianLattices.Ext.BoxTail
theorem _root_.solution (σ T : ℝ) (hσ0 : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1 - 1 / 800) (hT : 0 ≤ T) :
    ∫ u in (-T)..T, 1 / ‖(σ : ℂ) + (u : ℂ) * I - 1‖ ≤ 4 * Real.log (1 + 800 * T) := by
  have hg : Continuous (fun u : ℝ => 2 / (1 / 800 + |u|)) :=
    Continuous.div continuous_const (continuous_const.add continuous_abs) (fun x => by positivity)
  have hne : ∀ u : ℝ, ‖(σ : ℂ) + (u : ℂ) * I - 1‖ ≠ 0 := by
    intro u
    have := tail_kernel_norm_lower σ u hσ1
    have : 0 < (1 / 800 + |u|) / 2 := by positivity
    linarith
  have hf : Continuous (fun u : ℝ => 1 / ‖(σ : ℂ) + (u : ℂ) * I - 1‖) :=
    Continuous.div continuous_const
      (((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).sub
        continuous_const).norm) hne
  calc ∫ u in (-T)..T, 1 / ‖(σ : ℂ) + (u : ℂ) * I - 1‖
      ≤ ∫ u in (-T)..T, 2 / (1 / 800 + |u|) := by
        apply intervalIntegral.integral_mono_on (by linarith) (hf.intervalIntegrable _ _)
          (hg.intervalIntegrable _ _)
        intro u _
        have h3 := tail_kernel_norm_lower σ u hσ1
        have hp : 0 < (1 / 800 + |u|) / 2 := by positivity
        have := one_div_le_one_div_of_le hp h3
        rwa [one_div_div] at this
    _ = 4 * Real.log (1 + 800 * T) := by
        have hsplit := (intervalIntegral.integral_add_adjacent_intervals (a := -T) (b := 0) (c := T)
          (hg.intervalIntegrable (μ := MeasureTheory.volume) _ _)
          (hg.intervalIntegrable (μ := MeasureTheory.volume) _ _))
        have hneg := intervalIntegral.integral_comp_neg (a := 0) (b := T)
          (fun u : ℝ => 2 / (1 / 800 + |u|))
        simp only [neg_zero, abs_neg] at hneg
        have hpos : ∫ u in (0 : ℝ)..T, 2 / (1 / 800 + |u|) = ∫ u in (0 : ℝ)..T, 2 / (1 / 800 + u) := by
          apply intervalIntegral.integral_congr
          intro u hu
          rw [Set.uIcc_of_le hT] at hu
          simp only [abs_of_nonneg hu.1]
        rw [← hsplit, ← hneg, hpos, tail_kernel_half T hT]
        ring
end Formalism.HermitianLattices.Ext.BoxTail
