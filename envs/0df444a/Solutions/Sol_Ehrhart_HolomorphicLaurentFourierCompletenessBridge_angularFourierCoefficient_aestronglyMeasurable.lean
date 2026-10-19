-- Prove2me | solution 1 for Ehrhart.HolomorphicLaurentFourierCompletenessBridge.angularFourierCoefficient_aestronglyMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:12.519086+00:00
-- url     : https://prove2.me/submissions/0618938d-b5e2-4be5-b477-6909a742902a

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
    (f : WeightedTorusHilbert.weightedHilbert k φ)
    (m : Fin n → ℤ) :
    AEStronglyMeasurable (angularFourierCoefficient φ f m)
      (WeightedTorusHilbert.radialMeasure k φ) := by
  have hchar :
      AEStronglyMeasurable
        (fun θ : TorusCharacters.AngularTorus n =>
          UnitAddTorus.mFourier (-m) θ)
        (WeightedTorusHilbert.angularMeasure n) := by
    exact (UnitAddTorus.mFourier (-m)).continuous.aestronglyMeasurable
  have hprod :
      AEStronglyMeasurable
        (fun z : WeightedTorusHilbert.LogTorus n =>
          UnitAddTorus.mFourier (-m) z.2 * f z)
        ((WeightedTorusHilbert.radialMeasure k φ).prod
          (WeightedTorusHilbert.angularMeasure n)) := by
    have hf := (MeasureTheory.Lp.aestronglyMeasurable f)
    unfold WeightedTorusHilbert.weightedTorusMeasure at hf
    exact hchar.comp_snd.mul hf
  have hcoeff := hprod.integral_prod_right'
  refine hcoeff.congr (Filter.Eventually.of_forall fun x => ?_)
  simp [angularFourierCoefficient, UnitAddTorus.mFourierCoeff,
    WeightedTorusHilbert.angularMeasure, smul_eq_mul]
end Ehrhart.HolomorphicLaurentFourierCompletenessBridge
