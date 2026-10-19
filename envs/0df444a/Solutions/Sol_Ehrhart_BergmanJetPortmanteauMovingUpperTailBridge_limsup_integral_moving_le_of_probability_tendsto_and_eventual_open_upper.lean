-- Prove2me | solution 1 for Ehrhart.BergmanJetPortmanteauMovingUpperTailBridge.limsup_integral_moving_le_of_probability_tendsto_and_eventual_open_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:23.737149+00:00
-- url     : https://prove2.me/submissions/b5c272a2-088a-4429-8e7c-72a6220e62cc

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetPortmanteauMovingUpperTailBridge_iInter_movingUpperLevelClosedTail_subset_of_eventual_open_upper
import Theorems.Thm_Ehrhart_BergmanJetPortmanteauMovingUpperTailBridge_limsup_integral_moving_le_of_probability_tendsto

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetPortmanteauMovingUpperTailBridge
open Set Function Filter MeasureTheory
open BergmanJetPortmanteauSlopeBridge BergmanJetPortmanteauUpperTailBridge
open scoped BigOperators ENNReal NNReal Topology
namespace Ehrhart.BergmanJetPortmanteauMovingUpperTailBridge
theorem _root_.solution
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    (μ : ProbabilityMeasure X) (μk : ℕ → ProbabilityMeasure X)
    (hμ : Tendsto μk atTop (𝓝 μ))
    (f : ℕ → X → ℝ) (g : X → ℝ) (C : ℝ)
    (hfmeas : ∀ k : ℕ, Measurable (f k))
    (hg : UpperSemicontinuous g)
    (hC : 0 ≤ C)
    (hfnonneg : ∀ (k : ℕ) (x : X), 0 ≤ f k x)
    (hfbound : ∀ (k : ℕ) (x : X), f k x ≤ C)
    (hgnonneg : ∀ x : X, 0 ≤ g x)
    (hgbound : ∀ x : X, g x ≤ C)
    (hjoint : ∀ (x : X) (t : ℝ), g x < t →
      ∃ (N : ℕ) (U : Set X), IsOpen U ∧ x ∈ U ∧
        ∀ (k : ℕ), N ≤ k → ∀ y ∈ U, f k y < t) :
    Filter.limsup
        (fun k : ℕ => ∫ x, f k x ∂(μk k : Measure X)) atTop ≤
      ∫ x, g x ∂(μ : Measure X) := by
  apply limsup_integral_moving_le_of_probability_tendsto
    μ μk hμ f g C hfmeas hg hC
      hfnonneg hfbound hgnonneg hgbound
  exact iInter_movingUpperLevelClosedTail_subset_of_eventual_open_upper
    f g hjoint
end Ehrhart.BergmanJetPortmanteauMovingUpperTailBridge
