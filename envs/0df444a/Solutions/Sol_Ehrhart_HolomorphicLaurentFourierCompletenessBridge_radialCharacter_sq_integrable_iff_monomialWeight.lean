-- Prove2me | solution 1 for Ehrhart.HolomorphicLaurentFourierCompletenessBridge.radialCharacter_sq_integrable_iff_monomialWeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:12.519086+00:00
-- url     : https://prove2.me/submissions/6e4381dc-6a95-4117-af3b-7d8fb728584b

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
theorem _root_.solution
    {n : ℕ} (k : ℕ)
    {φ : Space n → ℝ} (hφ : Continuous φ)
    (m : Fin n → ℤ) (u : Space n)
    (hm : integerPoint n m = (k : ℝ) • u) :
    Integrable
      (fun x : Space n =>
        ‖WeightedTorusHilbert.radialCharacter m x‖ ^ 2)
      (WeightedTorusHilbert.radialMeasure k φ) ↔
    Integrable
      (MonomialIntegrability.monomialWeight (k : ℝ) u φ)
      (volume : Measure (Space n)) := by
  have hfinite :
      ∀ᵐ x ∂(volume : Measure (Space n)),
        WeightedTorusHilbert.radialWeight k φ x < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  unfold WeightedTorusHilbert.radialMeasure
  rw [MeasureTheory.integrable_withDensity_iff_integrable_smul'
    (WeightedTorusHilbert.radialWeight_measurable k hφ)
    hfinite]
  apply MeasureTheory.integrable_congr
  filter_upwards [] with x
  change
    (WeightedTorusHilbert.radialWeight k φ x).toReal *
        ‖WeightedTorusHilbert.radialCharacter m x‖ ^ 2 =
      MonomialIntegrability.monomialWeight
        (k : ℝ) u φ x
  unfold WeightedTorusHilbert.radialCharacter
  rw [TorusCharacters.norm_sq_torusCharacter_realLogSlice]
  simpa [SupportFunction.pairing, integerPoint] using
    WeightedTorusHilbert.radialWeight_mul_exp_pairing
      k φ m u hm x
end Ehrhart.HolomorphicLaurentFourierCompletenessBridge
