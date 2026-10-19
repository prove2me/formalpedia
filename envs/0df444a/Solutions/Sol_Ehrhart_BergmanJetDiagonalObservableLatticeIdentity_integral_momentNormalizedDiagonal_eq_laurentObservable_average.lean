-- Prove2me | solution 1 for Ehrhart.BergmanJetDiagonalObservableLatticeIdentity.integral_momentNormalizedDiagonal_eq_laurentObservable_average
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:26.272914+00:00
-- url     : https://prove2.me/submissions/24c85645-07d8-4015-9eef-a89aba7720d6

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetDiagonalObservableLatticeIdentity_momentNormalizedLaurentObservable_eq_integral_normalizedMonomialDensity

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetDiagonalObservableLatticeIdentity
open Set Function Filter MeasureTheory
open BergmanMonomials BergmanNormalization LatticeAsymptotics MonomialIntegrability MomentOptimizer
open MomentFirstVariation MomentTargetGeodesic MomentRegularity MomentWeakBergmanProbabilityEndpoint
open scoped BigOperators ENNReal NNReal Topology
namespace Ehrhart.BergmanJetDiagonalObservableLatticeIdentity
theorem _root_.solution
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (f : Space n → ℝ)
    (hf : Continuous f)
    (C : ℝ)
    (hC : ∀ x : Space n, |f x| ≤ C) :
    (∫ x : Space n,
      f x * normalizedDiagonalDensity
        K k (momentNormalizedPotential F) x
      ∂(volume : Measure (Space n))) =
      (∑' u : monomialIndex K k,
        momentNormalizedLaurentObservable
          F k f (u : Space n)) /
        (bergmanDimension K k : ℝ) := by
  classical
  let := (monomialIndex_finite K hk).fintype
  have hmono : ∀ u : monomialIndex K k,
      Integrable
        (fun x : Space n =>
          f x * normalizedMonomialDensity
            K k (momentNormalizedPotential F) u x)
        (volume : Measure (Space n)) := by
    intro u
    exact
      (normalizedMonomialDensity_momentNormalized_integrable
        K hk F htransport u).bdd_mul
        hf.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by
          simpa [Real.norm_eq_abs] using hC x)
  calc
    (∫ x : Space n,
      f x * normalizedDiagonalDensity
        K k (momentNormalizedPotential F) x
      ∂(volume : Measure (Space n))) =
        (∫ x : Space n,
          f x * weightedDiagonalKernel
            K k (momentNormalizedPotential F) x
          ∂(volume : Measure (Space n))) /
          (bergmanDimension K k : ℝ) := by
      unfold normalizedDiagonalDensity
      simp_rw [← mul_div_assoc]
      rw [MeasureTheory.integral_div]
    _ = (∑ u : monomialIndex K k,
          ∫ x : Space n,
            f x * normalizedMonomialDensity
              K k (momentNormalizedPotential F) u x
            ∂(volume : Measure (Space n))) /
          (bergmanDimension K k : ℝ) := by
      congr 1
      unfold weightedDiagonalKernel
      simp_rw [tsum_fintype]
      simp_rw [Finset.mul_sum]
      rw [MeasureTheory.integral_finsetSum]
      intro u _
      exact hmono u
    _ = (∑' u : monomialIndex K k,
          momentNormalizedLaurentObservable
            F k f (u : Space n)) /
          (bergmanDimension K k : ℝ) := by
      rw [tsum_fintype]
      congr 1
      apply Finset.sum_congr rfl
      intro u _
      exact
        (momentNormalizedLaurentObservable_eq_integral_normalizedMonomialDensity
          K F f u).symm
end Ehrhart.BergmanJetDiagonalObservableLatticeIdentity
