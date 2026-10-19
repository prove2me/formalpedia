-- Prove2me | solution 1 for Ehrhart.BergmanJetMovingPhaseConcentration.momentNormalized_off_phase_setIntegral_le_exp_mul_base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.658478+00:00
-- url     : https://prove2.me/submissions/6e29baa3-d70a-4078-a1b4-9b8109d6d7bc

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetMovingPhaseConcentration
open Set Function Filter MeasureTheory Metric
open SupportFunction LaplaceAsymptotics MonomialIntegrability MomentOptimizer MomentFirstVariation
open MomentTargetGeodesic MomentRegularity MomentWeakBergman BergmanJetPhaseLaplace
open BergmanJetDualPhaseConcentration
open scoped BigOperators ENNReal NNReal Topology
namespace Ehrhart.BergmanJetMovingPhaseConcentration
theorem _root_.solution
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    {u : Space n} (hu : u ∈ interior K.carrier)
    {s : Set (Space n)} (hs : MeasurableSet s)
    {M : ℝ}
    (hphase : ∀ x ∈ s,
      phase u (momentNormalizedPotential F) x ≤ M)
    {k : ℝ} (hk : 1 ≤ k) :
    (∫ x : Space n in s,
      monomialWeight k u (momentNormalizedPotential F) x
      ∂(volume : Measure (Space n))) ≤
      Real.exp ((k - 1) * M) *
        monomialIntegral 1 u (momentNormalizedPotential F) := by
  have hkpos : 0 < k := lt_of_lt_of_le zero_lt_one hk
  have hkint :=
    integrable_monomialWeight_momentNormalized_of_mem_interior
      F htransport hu hkpos
  have hbase :=
    integrable_monomialWeight_momentNormalized_of_mem_interior
      F htransport hu (k := (1 : ℝ)) zero_lt_one
  have hmajor := hbase.const_mul (Real.exp ((k - 1) * M))
  calc
    (∫ x : Space n in s,
      monomialWeight k u (momentNormalizedPotential F) x
      ∂(volume : Measure (Space n))) ≤
      ∫ x : Space n in s,
        Real.exp ((k - 1) * M) *
          monomialWeight 1 u (momentNormalizedPotential F) x
        ∂(volume : Measure (Space n)) := by
      apply setIntegral_mono_on hkint.integrableOn
        hmajor.integrableOn hs
      intro x hx
      unfold monomialWeight
      change
        Real.exp (k *
          (pairing u x - momentNormalizedPotential F x)) ≤
          Real.exp ((k - 1) * M) *
            Real.exp (1 *
              (pairing u x - momentNormalizedPotential F x))
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h := hphase x hx
      unfold phase at h
      nlinarith
    _ ≤ ∫ x : Space n,
        Real.exp ((k - 1) * M) *
          monomialWeight 1 u (momentNormalizedPotential F) x
        ∂(volume : Measure (Space n)) := by
      apply setIntegral_le_integral hmajor
      exact Filter.Eventually.of_forall fun x =>
        mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
    _ = Real.exp ((k - 1) * M) *
          monomialIntegral 1 u (momentNormalizedPotential F) := by
      rw [integral_const_mul]
      rfl
end Ehrhart.BergmanJetMovingPhaseConcentration
