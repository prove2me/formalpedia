-- Prove2me | solution 1 for Ehrhart.DolbeaultGraphDistributionBridge.complex_compact_integration_by_parts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:13.178776+00:00
-- url     : https://prove2.me/submissions/e630cc31-7d37-45c6-aab2-b1ee2c6a92aa

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.DolbeaultGraphDistributionBridge
open Set Function MeasureTheory Filter
open EqualitySaturatingKillingPaths DolbeaultRegularity
open scoped BigOperators ENNReal InnerProductSpace Topology Convolution
namespace Ehrhart.DolbeaultGraphDistributionBridge
theorem _root_.solution {n : ℕ}
    {F : TorusCharacters.LogSpace n → ℂ}
    {ψ : TorusCharacters.LogSpace n → ℝ}
    (hF : ContDiff ℝ 1 F)
    (hψ : ContDiff ℝ 1 ψ)
    (hψcompact : HasCompactSupport ψ)
    (v : TorusCharacters.LogSpace n) :
    (∫ z : TorusCharacters.LogSpace n,
      F z * ((fderiv ℝ ψ z) v : ℂ)
      ∂(volume : Measure (TorusCharacters.LogSpace n))) =
      -(∫ z : TorusCharacters.LogSpace n,
        (fderiv ℝ F z) v * (ψ z : ℂ)
        ∂(volume : Measure (TorusCharacters.LogSpace n))) := by
  let G : TorusCharacters.LogSpace n → ℂ :=
    fun z => (ψ z : ℂ)
  have hG : ContDiff ℝ 1 G :=
    Complex.ofRealCLM.contDiff.comp hψ
  have hGcompact : HasCompactSupport G :=
    compactSupport_complexOfReal hψcompact
  have hFd : Continuous
      (fun z : TorusCharacters.LogSpace n =>
        (fderiv ℝ F z) v) :=
    (hF.continuous_fderiv (by simp)).clm_apply continuous_const
  have hGd : Continuous
      (fun z : TorusCharacters.LogSpace n =>
        (fderiv ℝ G z) v) :=
    (hG.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdfG : Integrable
      (fun z : TorusCharacters.LogSpace n =>
        (fderiv ℝ F z) v * G z)
      (volume : Measure (TorusCharacters.LogSpace n)) :=
    (hFd.mul hG.continuous).integrable_of_hasCompactSupport
      hGcompact.mul_left
  have hfDG : Integrable
      (fun z : TorusCharacters.LogSpace n =>
        F z * (fderiv ℝ G z) v)
      (volume : Measure (TorusCharacters.LogSpace n)) :=
    (hF.continuous.mul hGd).integrable_of_hasCompactSupport
      (hGcompact.fderiv_apply ℝ v).mul_left
  have hFG : Integrable
      (fun z : TorusCharacters.LogSpace n => F z * G z)
      (volume : Measure (TorusCharacters.LogSpace n)) :=
    (hF.continuous.mul hG.continuous).integrable_of_hasCompactSupport
      hGcompact.mul_left
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure (TorusCharacters.LogSpace n)))
    (v := v) hdfG hfDG hFG
    (fun z _ => (hF.differentiable (by simp)).differentiableAt)
    (fun z _ => (hG.differentiable (by simp)).differentiableAt)
  simpa only [G,
    fderiv_complexOfReal (hψ.differentiable (by simp))] using h
end Ehrhart.DolbeaultGraphDistributionBridge
