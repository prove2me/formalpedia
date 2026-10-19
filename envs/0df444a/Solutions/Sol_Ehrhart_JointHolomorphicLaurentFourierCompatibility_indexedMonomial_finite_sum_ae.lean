-- Prove2me | solution 1 for Ehrhart.JointHolomorphicLaurentFourierCompatibility.indexedMonomial_finite_sum_ae
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:12.519086+00:00
-- url     : https://prove2.me/submissions/a65f2c00-e6ea-442f-9d6f-e048808dab77

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusHilbert_indexedMonomialLp_ae

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
    (s : Finset (LatticeAsymptotics.monomialIndex K k))
    (c : LatticeAsymptotics.monomialIndex K k → ℂ) :
    (fun z : WeightedTorusHilbert.LogTorus n =>
      (∑ u ∈ s, c u •
        WeightedTorusHilbert.indexedMonomialLp
          K hk hφ hbounded u) z)
      =ᵐ[WeightedTorusHilbert.weightedTorusMeasure k φ]
    (fun z =>
      ∑ u ∈ s, c u *
        WeightedTorusHilbert.torusMonomial
          (WeightedTorusHilbert.integerExponent K hk u) z) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    filter_upwards [MeasureTheory.Lp.coeFn_zero ℂ 2
      (WeightedTorusHilbert.weightedTorusMeasure k φ)]
      with z hz
    simpa only [Finset.sum_empty, Pi.zero_apply] using hz
  | @insert u s hu ih =>
    have hadd :=
      MeasureTheory.Lp.coeFn_add
        (c u • WeightedTorusHilbert.indexedMonomialLp
          K hk hφ hbounded u)
        (∑ v ∈ s, c v •
          WeightedTorusHilbert.indexedMonomialLp
            K hk hφ hbounded v)
    have hsmul :=
      MeasureTheory.Lp.coeFn_smul (c u)
        (WeightedTorusHilbert.indexedMonomialLp
          K hk hφ hbounded u)
    have hmono :=
      WeightedTorusHilbert.indexedMonomialLp_ae
        K hk hφ hbounded u
    filter_upwards [hadd, hsmul, hmono, ih]
      with z hzadd hzsmul hzmono hzsum
    simp only [Finset.sum_insert hu]
    rw [hzadd]
    change
      (c u • WeightedTorusHilbert.indexedMonomialLp
        K hk hφ hbounded u) z +
        (∑ v ∈ s, c v •
          WeightedTorusHilbert.indexedMonomialLp
            K hk hφ hbounded v) z =
        c u * WeightedTorusHilbert.torusMonomial
          (WeightedTorusHilbert.integerExponent K hk u) z +
          ∑ v ∈ s, c v *
            WeightedTorusHilbert.torusMonomial
              (WeightedTorusHilbert.integerExponent K hk v) z
    rw [hzsmul, hzsum]
    change
      c u * WeightedTorusHilbert.indexedMonomialLp
          K hk hφ hbounded u z + _ = _
    rw [hzmono]
end Ehrhart.JointHolomorphicLaurentFourierCompatibility
