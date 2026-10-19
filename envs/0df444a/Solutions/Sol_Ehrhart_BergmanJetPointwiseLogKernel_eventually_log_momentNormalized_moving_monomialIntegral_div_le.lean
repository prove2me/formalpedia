-- Prove2me | solution 1 for Ehrhart.BergmanJetPointwiseLogKernel.eventually_log_momentNormalized_moving_monomialIntegral_div_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:14.10863+00:00
-- url     : https://prove2.me/submissions/90ee7b14-f6e8-4aa1-9aa1-28362693bfd2

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetPointwiseLogKernel_exists_eventual_momentNormalized_moving_base_integral_bound
import Theorems.Thm_Ehrhart_BergmanJetPointwiseLogKernel_eventually_momentNormalized_moving_phase_le_max_add

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
    ∀ᶠ k : ℕ in atTop,
      Real.log
          (monomialIntegral (k : ℝ) (u k)
            (momentNormalizedPotential F)) / (k : ℝ) ≤
        phase u₀ (momentNormalizedPotential F) x + ε := by
  obtain ⟨B, hB, hbase⟩ :=
    exists_eventual_momentNormalized_moving_base_integral_bound
      K F htransport hu₀ u hu
  let M : ℝ :=
    phase u₀ (momentNormalizedPotential F) x + ε / 2
  have hphase :=
    eventually_momentNormalized_moving_phase_le_max_add
      K F htransport hu₀ u hu x hmax (half_pos hε)
  have hinterior :
      ∀ᶠ k : ℕ in atTop, u k ∈ interior K.carrier :=
    hu.eventually (isOpen_interior.mem_nhds hu₀)
  have herr :
      Tendsto
        (fun k : ℕ => (Real.log B - M) / (k : ℝ))
        atTop (𝓝 (0 : ℝ)) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).const_div_atTop
      (Real.log B - M)
  have hsmall :
      ∀ᶠ k : ℕ in atTop,
        (Real.log B - M) / (k : ℝ) < ε / 2 :=
    herr (Iio_mem_nhds (half_pos hε))
  filter_upwards
    [eventually_ge_atTop (1 : ℕ), hinterior,
      hbase, hphase, hsmall]
    with k hk hku hbasek hphasek hsmallk
  have hkreal : 0 < (k : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hknorm : (1 : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast hk
  have hI :
      0 < monomialIntegral (k : ℝ) (u k)
        (momentNormalizedPotential F) :=
    monomialIntegral_momentNormalized_pos
      F htransport hku hkreal
  have hupper :=
    momentNormalized_monomialIntegral_le_exp_mul_base
      F htransport hku hphasek hknorm
  have hIupper :
      monomialIntegral (k : ℝ) (u k)
          (momentNormalizedPotential F) ≤
        Real.exp (((k : ℝ) - 1) * M) * B := by
    exact hupper.trans
      (mul_le_mul_of_nonneg_left hbasek
        (Real.exp_pos _).le)
  have hlog := Real.log_le_log hI hIupper
  rw [Real.log_mul (Real.exp_ne_zero _) hB.ne',
    Real.log_exp] at hlog
  calc
    Real.log
        (monomialIntegral (k : ℝ) (u k)
          (momentNormalizedPotential F)) / (k : ℝ) ≤
      (((k : ℝ) - 1) * M + Real.log B) / (k : ℝ) :=
        (div_le_div_iff_of_pos_right hkreal).mpr hlog
    _ = M + (Real.log B - M) / (k : ℝ) := by
      field_simp
      ; ring
    _ ≤ phase u₀ (momentNormalizedPotential F) x + ε := by
      dsimp [M] at *
      linarith
end Ehrhart.BergmanJetPointwiseLogKernel
