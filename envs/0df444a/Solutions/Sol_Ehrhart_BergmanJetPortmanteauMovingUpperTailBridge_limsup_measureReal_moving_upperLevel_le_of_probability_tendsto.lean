-- Prove2me | solution 1 for Ehrhart.BergmanJetPortmanteauMovingUpperTailBridge.limsup_measureReal_moving_upperLevel_le_of_probability_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:23.737149+00:00
-- url     : https://prove2.me/submissions/8de58fcd-f04d-421e-ac5e-d21bf23f58b0

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetPortmanteauSlopeBridge_limsup_measureReal_closed_le_of_probability_tendsto
import Theorems.Thm_Ehrhart_BergmanJetPortmanteauMovingUpperTailBridge_isClosed_movingUpperLevelClosedTail
import Theorems.Thm_Ehrhart_BergmanJetPortmanteauMovingUpperTailBridge_antitone_movingUpperLevelClosedTail
import Theorems.Thm_Ehrhart_BergmanJetPortmanteauMovingUpperTailBridge_moving_upperLevel_subset_closedTail

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
    (f : ℕ → X → ℝ) (g : X → ℝ)
    (hjoint : ∀ t : ℝ,
      (⋂ N : ℕ, movingUpperLevelClosedTail f t N) ⊆
        {x : X | t ≤ g x})
    (t : ℝ) :
    Filter.limsup
        (fun k : ℕ =>
          (μk k : Measure X).real {x : X | t ≤ f k x}) atTop ≤
      (μ : Measure X).real {x : X | t ≤ g x} := by
  let S : ℕ → Set X := movingUpperLevelClosedTail f t
  have hclosed (N : ℕ) : IsClosed (S N) :=
    isClosed_movingUpperLevelClosedTail f t N
  have hanti : Antitone S :=
    antitone_movingUpperLevelClosedTail f t
  have hcob :
      Filter.IsCoboundedUnder (· ≤ ·) atTop
        (fun k : ℕ =>
          (μk k : Measure X).real {x : X | t ≤ f k x}) :=
    Filter.isCoboundedUnder_le_of_le atTop fun _ =>
      measureReal_nonneg
  have htail (N : ℕ) :
      Filter.limsup
          (fun k : ℕ =>
            (μk k : Measure X).real {x : X | t ≤ f k x}) atTop ≤
        (μ : Measure X).real (S N) := by
    have hcompare : ∀ᶠ k : ℕ in atTop,
        (μk k : Measure X).real {x : X | t ≤ f k x} ≤
          (μk k : Measure X).real (S N) := by
      filter_upwards [eventually_ge_atTop N] with k hk
      exact measureReal_mono
        (moving_upperLevel_subset_closedTail f t hk)
    have hbounded :
        Filter.IsBoundedUnder (· ≤ ·) atTop
          (fun k : ℕ => (μk k : Measure X).real (S N)) :=
      Filter.isBoundedUnder_of_eventually_le
        (Filter.Eventually.of_forall fun _ => measureReal_le_one)
    exact (Filter.limsup_le_limsup hcompare hcob hbounded).trans
      (limsup_measureReal_closed_le_of_probability_tendsto
        μ μk hμ (hclosed N))
  have hmeasure :
      Tendsto
        (fun N : ℕ => (μ : Measure X).real (S N)) atTop
        (𝓝 ((μ : Measure X).real (⋂ N : ℕ, S N))) := by
    have hENN := tendsto_measure_iInter_atTop
      (μ := (μ : Measure X))
      (fun N : ℕ => (hclosed N).measurableSet.nullMeasurableSet)
      hanti ⟨0, measure_ne_top (μ : Measure X) (S 0)⟩
    simpa [Measure.real, Function.comp_def] using
      (ENNReal.tendsto_toReal
        (measure_ne_top (μ : Measure X)
          (⋂ N : ℕ, S N))).comp hENN
  have hlimit :
      Filter.limsup
          (fun k : ℕ =>
            (μk k : Measure X).real {x : X | t ≤ f k x}) atTop ≤
        (μ : Measure X).real (⋂ N : ℕ, S N) :=
    ge_of_tendsto hmeasure (Filter.Eventually.of_forall htail)
  exact hlimit.trans (measureReal_mono (hjoint t))
end Ehrhart.BergmanJetPortmanteauMovingUpperTailBridge
