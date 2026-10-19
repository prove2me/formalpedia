-- Prove2me | solution 1 for Ehrhart.BergmanJetDiagonalObservableLatticeIdentity.abs_momentNormalizedLaurentObservable_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:26.272914+00:00
-- url     : https://prove2.me/submissions/cd5ddd96-d7a5-4624-af95-1f38209e5ebb

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MomentWeakBergmanProbabilityEndpoint_normalizedMonomialDensity_momentNormalized_pos
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
    (hC : ∀ x : Space n, |f x| ≤ C)
    (u : monomialIndex K k) :
    |momentNormalizedLaurentObservable
        F k f (u : Space n)| ≤ C := by
  rw [momentNormalizedLaurentObservable_eq_integral_normalizedMonomialDensity]
  let ρ : Space n → ℝ :=
    normalizedMonomialDensity
      K k (momentNormalizedPotential F) u
  have hρ : Integrable ρ
      (volume : Measure (Space n)) :=
    normalizedMonomialDensity_momentNormalized_integrable
      K hk F htransport u
  have hρpos : ∀ x : Space n, 0 ≤ ρ x := fun x =>
    (normalizedMonomialDensity_momentNormalized_pos
      K hk F htransport u x).le
  have hprod :
      Integrable (fun x : Space n => f x * ρ x)
        (volume : Measure (Space n)) :=
    hρ.bdd_mul hf.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        simpa [Real.norm_eq_abs] using hC x)
  change |∫ x : Space n, f x * ρ x
    ∂(volume : Measure (Space n))| ≤ C
  calc
    |∫ x : Space n, f x * ρ x
      ∂(volume : Measure (Space n))| ≤
        ∫ x : Space n, ‖f x * ρ x‖
          ∂(volume : Measure (Space n)) := by
      simpa [Real.norm_eq_abs] using
        (MeasureTheory.norm_integral_le_integral_norm
          (fun x : Space n => f x * ρ x))
    _ ≤ ∫ x : Space n, C * ρ x
          ∂(volume : Measure (Space n)) := by
      apply MeasureTheory.integral_mono_ae
        hprod.norm (hρ.const_mul C)
      filter_upwards [] with x
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (hρpos x)]
      exact mul_le_mul_of_nonneg_right (hC x) (hρpos x)
    _ = C := by
      rw [MeasureTheory.integral_const_mul]
      change C *
        (∫ x : Space n,
          normalizedMonomialDensity
            K k (momentNormalizedPotential F) u x
          ∂(volume : Measure (Space n))) = C
      rw [integral_normalizedMonomialDensity_momentNormalized
        K hk F htransport u]
      ring
end Ehrhart.BergmanJetDiagonalObservableLatticeIdentity
