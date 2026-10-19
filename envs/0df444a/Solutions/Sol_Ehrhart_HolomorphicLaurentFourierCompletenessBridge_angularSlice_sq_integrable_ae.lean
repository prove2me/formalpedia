-- Prove2me | solution 1 for Ehrhart.HolomorphicLaurentFourierCompletenessBridge.angularSlice_sq_integrable_ae
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:12.519086+00:00
-- url     : https://prove2.me/submissions/98db3704-7e30-4e7e-94ba-3b105469a597

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

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
      Integrable
        (fun θ : TorusCharacters.AngularTorus n =>
          ‖f (x, θ)‖ ^ 2)
        (WeightedTorusHilbert.angularMeasure n) := by
  have hsquare :
      Integrable
        (fun z : WeightedTorusHilbert.LogTorus n =>
          ‖f z‖ ^ 2)
        (WeightedTorusHilbert.weightedTorusMeasure k φ) :=
    (MeasureTheory.memLp_two_iff_integrable_sq_norm
      (MeasureTheory.Lp.aestronglyMeasurable f)).mp (MeasureTheory.Lp.memLp f)
  unfold WeightedTorusHilbert.weightedTorusMeasure at hsquare
  exact hsquare.prod_right_ae
end Ehrhart.HolomorphicLaurentFourierCompletenessBridge
