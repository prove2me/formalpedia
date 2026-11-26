-- Prove2me | solution 1 for Eden.log_planar_factors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:32:05.059616+00:00
-- url     : https://prove2.me/submissions/f6f1e728-cc08-42dd-a1e8-be78234a3342

import Definitions.Def_Eden_FactorBounds
import Definitions.Def_Eden_VolumeGrowth
import Theorems.Thm_Eden_radialDefect_at_one
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_continuousOn_squaredRadiusEvolution_time
import Theorems.Thm_Eden_diagonalLinear_apply
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_log_planarAmplitude_eq_integral
import Theorems.Thm_Eden_log_radialAmplitude_eq_integral
import Theorems.Thm_Eden_planarAmplitude_zero_time
import Theorems.Thm_Eden_planarX_origin
import Theorems.Thm_Eden_planarX_zero_time
import Theorems.Thm_Eden_planarY_origin
import Theorems.Thm_Eden_planarY_zero_time
import Theorems.Thm_Eden_radialAmplitude_zero_time
import Theorems.Thm_Eden_radialDiscriminant_at_two
import Theorems.Thm_Eden_radialDiscriminant_at_zero
import Theorems.Thm_Eden_radialDiscriminant_zero_time
import Theorems.Thm_Eden_rates_sum
import Theorems.Thm_Eden_squaredRadiusEvolution_at_one
import Theorems.Thm_Eden_squaredRadiusEvolution_at_two
import Theorems.Thm_Eden_squaredRadiusEvolution_at_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_zero_time
attribute [local simp] Eden.amplitudeSq_at_zero
attribute [local simp] Eden.amplitudeSq_zero_time
attribute [local simp] Eden.blockRotation_apply
attribute [local simp] Eden.diagonalLinear_apply
attribute [local simp] Eden.evolution_zero_time
attribute [local simp] Eden.planarAmplitude_zero_time
attribute [local simp] Eden.planarX_origin
attribute [local simp] Eden.planarX_zero_time
attribute [local simp] Eden.planarY_origin
attribute [local simp] Eden.planarY_zero_time
attribute [local simp] Eden.radialAmplitude_zero_time
attribute [local simp] Eden.radialDiscriminant_at_two
attribute [local simp] Eden.radialDiscriminant_at_zero
attribute [local simp] Eden.radialDiscriminant_zero_time
attribute [local simp] Eden.squaredRadiusEvolution_at_one
attribute [local simp] Eden.squaredRadiusEvolution_at_two
attribute [local simp] Eden.squaredRadiusEvolution_at_zero
attribute [local simp] Eden.squaredRadiusEvolution_zero_time


attribute [local simp] Eden.radialDefect_at_one
section
noncomputable section
open Set
namespace Eden
private theorem defect_intervalIntegrable {t : ℝ} (ht : 0 ≤ t) (s : ℝ) :
    IntervalIntegrable (fun τ => (squaredRadiusEvolution τ s - 1) ^ 2)
      MeasureTheory.volume 0 t := by
  have hc := (((continuousOn_squaredRadiusEvolution_time s).mono
    (show Icc 0 t ⊆ Ici 0 from fun _ h => h.1)).sub
      (continuousOn_const (c := (1 : ℝ)))).pow 2
  exact hc.intervalIntegrable_of_Icc ht
end Eden
end
end

set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    Real.log (radialAmplitude t s) + Real.log (planarAmplitude t s) =
      2 * t - 6 * radialDefect t s := by
  have hcont := (continuousOn_squaredRadiusEvolution_time s).mono
    (show Icc 0 t ⊆ Ici 0 from fun _ h => h.1)
  have ha : Continuous radialRate := by unfold radialRate; fun_prop
  have hb : Continuous tangentialRate := by unfold tangentialRate; fun_prop
  have hai := (ha.comp_continuousOn hcont).intervalIntegrable_of_Icc
    (μ := MeasureTheory.volume) ht
  have hbi := (hb.comp_continuousOn hcont).intervalIntegrable_of_Icc
    (μ := MeasureTheory.volume) ht
  simp only [Function.comp_def] at hai hbi
  rw [log_radialAmplitude_eq_integral ht hs, log_planarAmplitude_eq_integral ht hs,
    ← intervalIntegral.integral_add hai hbi]
  simp_rw [rates_sum]
  rw [intervalIntegral.integral_sub intervalIntegrable_const
    ((defect_intervalIntegrable ht s).const_mul 6), intervalIntegral.integral_const_mul]
  simp [radialDefect, mul_comm]
end Eden
