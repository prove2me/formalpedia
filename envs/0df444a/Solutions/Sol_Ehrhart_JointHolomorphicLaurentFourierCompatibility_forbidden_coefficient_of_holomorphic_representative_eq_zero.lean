-- Prove2me | solution 1 for Ehrhart.JointHolomorphicLaurentFourierCompatibility.forbidden_coefficient_of_holomorphic_representative_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:12.519086+00:00
-- url     : https://prove2.me/submissions/b5806879-6a54-46ba-97be-4a53c3b4d217

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_HolomorphicLaurentFourierCompletenessBridge_forbidden_angularFourierCoefficient_constant_eq_zero
import Theorems.Thm_Ehrhart_JointHolomorphicLaurentFourierCompatibility_angularFourierCoefficient_of_holomorphic_representative_ae

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.JointHolomorphicLaurentFourierCompatibility
open Set MeasureTheory Filter Complex
open scoped BigOperators ComplexConjugate ENNReal Topology InnerProductSpace
attribute [local instance] Ehrhart.JointHolomorphicLaurentFourierCompatibility._p2m_local_instance_3610026555_13915
attribute [local instance] Ehrhart.JointHolomorphicLaurentFourierCompatibility._p2m_local_instance_3610026555_13918
namespace Ehrhart.JointHolomorphicLaurentFourierCompatibility
theorem _root_.solution
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    {φ : Space n → ℝ} (hφ : Continuous φ)
    {C : ℝ}
    (hbounded : ∀ x : Space n,
      |φ x - SupportFunction.supportFunction K.carrier x| ≤ C)
    (f : WeightedTorusHilbert.weightedHilbert k φ)
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : Differentiable ℂ F)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F (TorusCharacters.imaginaryShift q))
    (hrepresentative :
      (fun z : WeightedTorusHilbert.LogTorus n => f z)
        =ᵐ[WeightedTorusHilbert.weightedTorusMeasure k φ]
      (fun z => coverRepresentative F z.1 z.2))
    (m : Fin n → ℤ) (u : Space n)
    (hm : integerPoint n m = (k : ℝ) • u)
    (hu : u ∉ interior K.carrier) :
    UnitAddTorus.mFourierCoeff
        (coverRepresentative F 0) m = 0 := by
  exact
    HolomorphicLaurentFourierCompletenessBridge.forbidden_angularFourierCoefficient_constant_eq_zero
      K hk hφ hbounded f m u hm hu
      (UnitAddTorus.mFourierCoeff (coverRepresentative F 0) m)
      (angularFourierCoefficient_of_holomorphic_representative_ae
        f hF hperiod hrepresentative m)
end Ehrhart.JointHolomorphicLaurentFourierCompatibility
