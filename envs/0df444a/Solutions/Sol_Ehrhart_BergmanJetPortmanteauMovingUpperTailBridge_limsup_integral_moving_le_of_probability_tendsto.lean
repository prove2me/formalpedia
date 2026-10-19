-- Prove2me | solution 1 for Ehrhart.BergmanJetPortmanteauMovingUpperTailBridge.limsup_integral_moving_le_of_probability_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:23.737149+00:00
-- url     : https://prove2.me/submissions/f8213fa8-cc6a-4265-bfba-12df32383cd6

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetPortmanteauUpperTailBridge_measurable_measureReal_upperLevel
import Theorems.Thm_Ehrhart_BergmanJetPortmanteauUpperTailBridge_integrable_upperSemicontinuous_of_probability_bound
import Theorems.Thm_Ehrhart_BergmanJetPortmanteauMovingUpperTailBridge_limsup_measureReal_moving_upperLevel_le_of_probability_tendsto

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
    (hjoint : ∀ t : ℝ,
      (⋂ N : ℕ, movingUpperLevelClosedTail f t N) ⊆
        {x : X | t ≤ g x}) :
    Filter.limsup
        (fun k : ℕ => ∫ x, f k x ∂(μk k : Measure X)) atTop ≤
      ∫ x, g x ∂(μ : Measure X) := by
  let ν : Measure ℝ :=
    (volume : Measure ℝ).restrict (Set.Ioc 0 C)
  let G : ℕ → ℝ → ℝ :=
    fun k t => (μk k : Measure X).real {x : X | t ≤ f k x}
  let h : ℝ → ℝ :=
    fun t => (μ : Measure X).real {x : X | t ≤ g x}
  have hGmeas (k : ℕ) : Measurable (G k) :=
    measurable_measureReal_upperLevel (μk k : Measure X) (f k)
  have hmeas : Measurable h :=
    measurable_measureReal_upperLevel (μ : Measure X) g
  have hhint : Integrable h ν := by
    refine (integrable_const (1 : ℝ)).mono'
      hmeas.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun t => by
      dsimp [h]
      rw [abs_of_nonneg measureReal_nonneg]
      exact measureReal_le_one
  have hGnonneg (k : ℕ) (t : ℝ) : 0 ≤ G k t :=
    measureReal_nonneg
  have hGbound (k : ℕ) (t : ℝ) : G k t ≤ 1 :=
    measureReal_le_one
  have hhpos : ∀ᵐ t ∂ν, 0 ≤ h t :=
    Filter.Eventually.of_forall fun _ => measureReal_nonneg
  have hlevel :
      ∀ᵐ t ∂ν,
        Filter.limsup (fun k : ℕ => G k t) atTop ≤ h t := by
    apply Filter.Eventually.of_forall
    intro t
    exact limsup_measureReal_moving_upperLevel_le_of_probability_tendsto
      μ μk hμ f g hjoint t
  have hgint := integrable_upperSemicontinuous_of_probability_bound
    μ hg hC hgnonneg hgbound
  have hfint (k : ℕ) : Integrable (f k) (μk k : Measure X) := by
    refine (integrable_const C).mono'
      (hfmeas k).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs, abs_of_nonneg (hfnonneg k x),
        abs_of_nonneg hC] using hfbound k x
  calc
    Filter.limsup
        (fun k : ℕ => ∫ x, f k x ∂(μk k : Measure X)) atTop =
      Filter.limsup (fun k : ℕ => ∫ t, G k t ∂ν) atTop := by
        congr 1
        funext k
        exact (hfint k).integral_eq_integral_Ioc_meas_le
          (Filter.Eventually.of_forall (hfnonneg k))
          (Filter.Eventually.of_forall (hfbound k))
    _ ≤ ∫ t, h t ∂ν :=
      ActualJetPlurisubharmonicClosure.limsup_integral_le_of_nonnegative_bounded
        ν G h 1 hGmeas hhint hGnonneg hGbound hhpos hlevel
    _ = ∫ x, g x ∂(μ : Measure X) :=
      (hgint.integral_eq_integral_Ioc_meas_le
        (Filter.Eventually.of_forall hgnonneg)
        (Filter.Eventually.of_forall hgbound)).symm
end Ehrhart.BergmanJetPortmanteauMovingUpperTailBridge
