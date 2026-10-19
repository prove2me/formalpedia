-- Prove2me | solution 1 for Ehrhart.TorusFriedrichsMollifierEstimates.normalizedCoverComplexDriftCommutator_eq_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:19.434976+00:00
-- url     : https://prove2.me/submissions/660babbb-6e47-47ee-8c60-ed112fcbe72c

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_DolbeaultRegularity_complexRealMultiplication_apply

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusFriedrichsMollifierEstimates
open Set Function Filter MeasureTheory
open TorusCharacters DolbeaultRegularity TorusWeakDolbeaultMollification
open scoped BigOperators ENNReal Topology ContDiff Convolution
namespace Ehrhart.TorusFriedrichsMollifierEstimates
theorem _root_.solution
    {n : ℕ} {b h : LogSpace n → ℂ}
    (hh : LocallyIntegrable h (volume : Measure (LogSpace n)))
    (hb : Continuous b) (k : ℕ) (x : LogSpace n) :
    normalizedCoverComplexDriftCommutator b h k x =
      ∫ y : LogSpace n,
        (b y - b x) * h y *
          ((complexShrinkingBump (n := n) k).normed
            (volume : Measure (LogSpace n)) (x - y) : ℂ)
        ∂(volume : Measure (LogSpace n)) := by
  let κ : LogSpace n → ℝ :=
    (complexShrinkingBump (n := n) k).normed
      (volume : Measure (LogSpace n))
  have hκ : Continuous κ :=
    (complexShrinkingBump (n := n) k).continuous_normed
  have hκcompact : HasCompactSupport κ :=
    (complexShrinkingBump (n := n) k).hasCompactSupport_normed
  have hbh := locallyIntegrable_cover_complex_mul_continuous hh hb
  have hfirst : Integrable
      (fun y : LogSpace n => b y * h y * (κ (x - y) : ℂ))
      (volume : Measure (LogSpace n)) := by
    have hi := hκcompact.convolutionExists_right
      DolbeaultRegularity.complexRealMultiplication
      hbh hκ x
    simpa [complexRealMultiplication_apply,
      mul_assoc, mul_comm, mul_left_comm] using hi.integrable
  have hsecond : Integrable
      (fun y : LogSpace n => h y * (κ (x - y) : ℂ))
      (volume : Measure (LogSpace n)) := by
    have hi := hκcompact.convolutionExists_right
      DolbeaultRegularity.complexRealMultiplication
      hh hκ x
    simpa [complexRealMultiplication_apply,
      mul_assoc, mul_comm, mul_left_comm] using hi.integrable
  unfold normalizedCoverComplexDriftCommutator
  change
    (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
      (volume : Measure (LogSpace n))]
        (fun y => b y * h y)) x -
      b x *
        (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
          (volume : Measure (LogSpace n))] h) x = _
  rw [← congrFun
      (complex_convolution_flip (fun y => b y * h y) κ) x,
    ← congrFun (complex_convolution_flip h κ) x,
    MeasureTheory.convolution_def,
    MeasureTheory.convolution_def]
  simp_rw [complexRealMultiplication_apply]
  have hfirst' : Integrable
      (fun y : LogSpace n => (κ (x - y) : ℂ) * (b y * h y))
      (volume : Measure (LogSpace n)) := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using hfirst
  have hsecond' : Integrable
      (fun y : LogSpace n => (κ (x - y) : ℂ) * h y)
      (volume : Measure (LogSpace n)) := by
    simpa [mul_comm] using hsecond
  change
    (∫ y : LogSpace n, (κ (x - y) : ℂ) * (b y * h y)
      ∂(volume : Measure (LogSpace n))) -
      b x *
        (∫ y : LogSpace n, (κ (x - y) : ℂ) * h y
          ∂(volume : Measure (LogSpace n))) =
      ∫ y : LogSpace n,
        (b y - b x) * h y * (κ (x - y) : ℂ)
        ∂(volume : Measure (LogSpace n))
  rw [← MeasureTheory.integral_const_mul,
    ← MeasureTheory.integral_sub hfirst' (hsecond'.const_mul (b x))]
  apply integral_congr_ae
  filter_upwards with y
  ring
end Ehrhart.TorusFriedrichsMollifierEstimates
