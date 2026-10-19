-- Prove2me | solution 1 for Ehrhart.HolomorphicLaurentFourierCompletenessBridge.angularFourierCoefficient_sq_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:12.519086+00:00
-- url     : https://prove2.me/submissions/0d5e9b2c-8647-4d6f-9d0a-89651483c8fc

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_HolomorphicLaurentFourierCompletenessBridge_angularFourierCoefficient_aestronglyMeasurable
import Theorems.Thm_Ehrhart_HolomorphicLaurentFourierCompletenessBridge_angularFourierCoefficient_sq_le_slice_energy_ae

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
    (f : WeightedTorusHilbert.weightedHilbert k φ)
    (m : Fin n → ℤ) :
    Integrable
      (fun x : Space n =>
        ‖angularFourierCoefficient φ f m x‖ ^ 2)
      (WeightedTorusHilbert.radialMeasure k φ) := by
  have hsquare :
      Integrable
        (fun z : WeightedTorusHilbert.LogTorus n =>
          ‖f z‖ ^ 2)
        (WeightedTorusHilbert.weightedTorusMeasure k φ) :=
    (MeasureTheory.memLp_two_iff_integrable_sq_norm
      (MeasureTheory.Lp.aestronglyMeasurable f)).mp (MeasureTheory.Lp.memLp f)
  unfold WeightedTorusHilbert.weightedTorusMeasure at hsquare
  have hmajor := hsquare.integral_prod_left
  refine hmajor.mono'
    ((angularFourierCoefficient_aestronglyMeasurable φ f m).norm.pow 2) ?_
  filter_upwards [angularFourierCoefficient_sq_le_slice_energy_ae
    φ f m] with x hx
  rwa [Real.norm_of_nonneg (sq_nonneg _)]
end Ehrhart.HolomorphicLaurentFourierCompletenessBridge
