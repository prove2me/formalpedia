-- Prove2me | solution 1 for Ehrhart.BergmanJetPortmanteauUpperTailBridge.measurable_measureReal_upperLevel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:23.737149+00:00
-- url     : https://prove2.me/submissions/27850bfb-c687-419c-83f4-025d609a5025

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetPortmanteauUpperTailBridge
open Set Function Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Topology
namespace Ehrhart.BergmanJetPortmanteauUpperTailBridge
theorem _root_.solution
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (g : X → ℝ) :
    Measurable (fun t : ℝ => μ.real {x : X | t ≤ g x}) := by
  apply Measurable.ennreal_toReal
  exact Antitone.measurable fun s t hst =>
    measure_mono fun x hx => le_trans hst hx
end Ehrhart.BergmanJetPortmanteauUpperTailBridge
