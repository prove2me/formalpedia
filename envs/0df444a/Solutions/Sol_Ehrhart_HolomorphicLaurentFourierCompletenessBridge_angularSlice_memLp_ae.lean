-- Prove2me | solution 1 for Ehrhart.HolomorphicLaurentFourierCompletenessBridge.angularSlice_memLp_ae
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:12.519086+00:00
-- url     : https://prove2.me/submissions/4ff8ef05-7d0f-44eb-87bd-6e20937f813a

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_HolomorphicLaurentFourierCompletenessBridge_angularSlice_sq_integrable_ae

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.HolomorphicLaurentFourierCompletenessBridge
open Set MeasureTheory Filter Complex
open scoped BigOperators ComplexConjugate ENNReal Topology InnerProductSpace
attribute [local instance] Ehrhart.HolomorphicLaurentFourierCompletenessBridge._p2m_local_instance_3610026555_13449
attribute [local instance] Ehrhart.HolomorphicLaurentFourierCompletenessBridge._p2m_local_instance_3610026555_13452
namespace Ehrhart.HolomorphicLaurentFourierCompletenessBridge
theorem _root_.solution {n k : ℕ}
    (φ : Space n → ℝ)
    (f : WeightedTorusHilbert.weightedHilbert k φ) :
    ∀ᵐ x ∂(WeightedTorusHilbert.radialMeasure k φ),
      MemLp
        (fun θ : TorusCharacters.AngularTorus n =>
          f (x, θ))
        2 (WeightedTorusHilbert.angularMeasure n) := by
  have hmeas :
      ∀ᵐ x ∂(WeightedTorusHilbert.radialMeasure k φ),
        AEStronglyMeasurable
          (fun θ : TorusCharacters.AngularTorus n =>
            f (x, θ))
          (WeightedTorusHilbert.angularMeasure n) := by
    have hf := (MeasureTheory.Lp.aestronglyMeasurable f)
    unfold WeightedTorusHilbert.weightedTorusMeasure at hf
    exact hf.prodMk_left
  filter_upwards [hmeas, angularSlice_sq_integrable_ae φ f]
    with x hx hsquare
  exact (MeasureTheory.memLp_two_iff_integrable_sq_norm hx).mpr hsquare
end Ehrhart.HolomorphicLaurentFourierCompletenessBridge
