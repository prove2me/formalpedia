-- Prove2me | solution 1 for Ehrhart.BergmanJetPointwiseLogKernel.eventually_momentNormalized_moving_phase_le_max_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:14.10863+00:00
-- url     : https://prove2.me/submissions/66999626-3abf-4ddc-8b17-d972e8a867a4

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MonomialDivergence_pairing_sub_left
import Theorems.Thm_Ehrhart_BergmanJetPointwiseLogKernel_exists_eventual_momentNormalized_uniform_moving_phase_coercivity

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetPointwiseLogKernel
open Set Function Filter MeasureTheory Metric
open SupportFunction LaplaceAsymptotics MonomialIntegrability BergmanMonomials MomentOptimizer
open MomentTargetGeodesic MomentFirstVariation MomentRegularity MomentWeakBergman
open MomentWeakGlobalKernel BergmanJetPhaseLaplace BergmanJetMonomialEnvelopeLower
open MomentMoserTrudinger SpatialBergmanPointwiseAsymptotics
open scoped BigOperators ENNReal Topology
namespace Ehrhart.BergmanJetPointwiseLogKernel
theorem _root_.solution
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    {u₀ : Space n} (hu₀ : u₀ ∈ interior K.carrier)
    (u : ℕ → Space n)
    (hu : Tendsto u atTop (𝓝 u₀))
    (x : Space n)
    (hmax : ∀ z : Space n,
      phase u₀ (momentNormalizedPotential F) z ≤
        phase u₀ (momentNormalizedPotential F) x)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ z : Space n,
      phase (u k) (momentNormalizedPotential F) z ≤
        phase u₀ (momentNormalizedPotential F) x + ε := by
  obtain ⟨d, C, hd, hcoerce⟩ :=
    exists_eventual_momentNormalized_uniform_moving_phase_coercivity
      K F htransport hu₀ u hu
  let M : ℝ := phase u₀ (momentNormalizedPotential F) x
  let R : ℝ := max 1 ((C - M) / d)
  have hR : 0 < R :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hboundary : C - d * R ≤ M := by
    have hratio : (C - M) / d ≤ R := le_max_right _ _
    have hmul := (div_le_iff₀ hd).mp hratio
    nlinarith
  have hnorm :
      Tendsto (fun k : ℕ => ‖u k - u₀‖)
        atTop (𝓝 (0 : ℝ)) := by
    simpa using (hu.sub_const u₀).norm
  have herr :
      Tendsto
        (fun k : ℕ => (n : ℝ) * ‖u k - u₀‖ * R)
        atTop (𝓝 (0 : ℝ)) := by
    simpa using (hnorm.const_mul (n : ℝ)).mul_const R
  have hsmall :
      ∀ᶠ k : ℕ in atTop,
        (n : ℝ) * ‖u k - u₀‖ * R < ε :=
    herr (Iio_mem_nhds hε)
  filter_upwards [hcoerce, hsmall] with k hk herrk z
  by_cases hz : ‖z‖ ≤ R
  · have hpair :
        pairing (u k - u₀) z < ε := by
      calc
        pairing (u k - u₀) z ≤
            |pairing (u k - u₀) z| := le_abs_self _
        _ ≤ ((n : ℝ) * ‖u k - u₀‖) * ‖z‖ :=
          MonomialDivergence.abs_pairing_le_dimension_mul_norm
            (u k - u₀) z
        _ ≤ ((n : ℝ) * ‖u k - u₀‖) * R := by
          gcongr
        _ < ε := herrk
    have hsplit :
        phase (u k) (momentNormalizedPotential F) z =
          phase u₀ (momentNormalizedPotential F) z +
            pairing (u k - u₀) z := by
      unfold phase
      rw [MonomialDivergence.pairing_sub_left]
      ring
    rw [hsplit]
    dsimp [M] at *
    linarith [hmax z]
  · have hz' : R < ‖z‖ := lt_of_not_ge hz
    have hdecay : C - d * ‖z‖ ≤ M := by
      calc
        C - d * ‖z‖ ≤ C - d * R := by
          nlinarith
        _ ≤ M := hboundary
    exact (hk z).trans
      (hdecay.trans (by dsimp [M]; linarith))
end Ehrhart.BergmanJetPointwiseLogKernel
