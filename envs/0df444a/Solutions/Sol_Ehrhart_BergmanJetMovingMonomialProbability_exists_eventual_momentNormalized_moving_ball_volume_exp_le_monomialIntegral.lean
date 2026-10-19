-- Prove2me | solution 1 for Ehrhart.BergmanJetMovingMonomialProbability.exists_eventual_momentNormalized_moving_ball_volume_exp_le_monomialIntegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.658478+00:00
-- url     : https://prove2.me/submissions/484f2a87-ecd9-4eae-ba1a-114edc28c311

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetMovingMonomialProbability
open Set Function Filter MeasureTheory Metric
open SupportFunction LaplaceAsymptotics MonomialIntegrability MomentOptimizer MomentFirstVariation
open MomentTargetGeodesic MomentRegularity MomentWeakBergman
open scoped BigOperators ENNReal NNReal Topology
namespace Ehrhart.BergmanJetMovingMonomialProbability
theorem _root_.solution
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    {u₀ : Space n} (hu₀ : u₀ ∈ interior K.carrier)
    (u : ℕ → Space n)
    (hu : Tendsto u atTop (𝓝 u₀))
    (x₀ : Space n)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧
      0 < (volume : Measure (Space n)).real
        (Metric.ball x₀ r) ∧
      ∀ᶠ j : ℕ in atTop, ∀ {k : ℝ}, 0 < k →
        (volume : Measure (Space n)).real
            (Metric.ball x₀ r) *
          Real.exp
            (k *
              (phase (u j) (momentNormalizedPotential F) x₀ - ε)) ≤
        monomialIntegral k (u j) (momentNormalizedPotential F) := by
  let φ : Space n → ℝ := momentNormalizedPotential F
  have hopen : IsOpen
      {x : Space n |
        phase u₀ φ x₀ - ε / 2 < phase u₀ φ x} :=
    isOpen_lt continuous_const
      (continuous_phase u₀ (continuous_momentNormalizedPotential F))
  have hx₀ : x₀ ∈
      {x : Space n |
        phase u₀ φ x₀ - ε / 2 < phase u₀ φ x} := by
    change phase u₀ φ x₀ - ε / 2 < phase u₀ φ x₀
    linarith
  obtain ⟨r, hr, hball⟩ :=
    (Metric.isOpen_iff.mp hopen) x₀ hx₀
  have hballpos :
      0 < (volume : Measure (Space n))
        (Metric.ball x₀ r) := by
    apply (volume : Measure (Space n)).measure_pos_of_nonempty_interior
    rw [Metric.isOpen_ball.interior_eq]
    exact ⟨x₀, Metric.mem_ball_self hr⟩
  have hballfinite :
      (volume : Measure (Space n))
        (Metric.ball x₀ r) ≠ ⊤ :=
    (measure_ball_lt_top
      (μ := (volume : Measure (Space n)))
      (x := x₀) (r := r)).ne
  have hrealpos :
      0 < (volume : Measure (Space n)).real
        (Metric.ball x₀ r) :=
    ENNReal.toReal_pos hballpos.ne' hballfinite
  have hnorm :
      Tendsto
        (fun j : ℕ => ((n : ℝ) * ‖u j - u₀‖) * r)
        atTop (𝓝 (0 : ℝ)) := by
    simpa using
      (((hu.sub_const u₀).norm).const_mul (n : ℝ)).mul_const r
  have hsmall :
      ∀ᶠ j : ℕ in atTop,
        ((n : ℝ) * ‖u j - u₀‖) * r < ε / 2 :=
    hnorm (Iio_mem_nhds (half_pos hε))
  have hinterior :
      ∀ᶠ j : ℕ in atTop, u j ∈ interior K.carrier :=
    hu.eventually (isOpen_interior.mem_nhds hu₀)
  refine ⟨r, hr, hrealpos, ?_⟩
  filter_upwards [hsmall, hinterior] with j hj hju k hk
  have hkint :=
    integrable_monomialWeight_momentNormalized_of_mem_interior
      F htransport hju hk
  have hconst : IntegrableOn
      (fun _ : Space n =>
        Real.exp (k * (phase (u j) φ x₀ - ε)))
      (Metric.ball x₀ r)
      (volume : Measure (Space n)) :=
    integrableOn_const hballfinite
  calc
    (volume : Measure (Space n)).real
        (Metric.ball x₀ r) *
      Real.exp (k * (phase (u j) φ x₀ - ε)) =
        ∫ _x : Space n in Metric.ball x₀ r,
          Real.exp (k * (phase (u j) φ x₀ - ε))
          ∂(volume : Measure (Space n)) := by
      rw [setIntegral_const]
      simp [smul_eq_mul]
    _ ≤ ∫ x : Space n in Metric.ball x₀ r,
          monomialWeight k (u j) φ x
          ∂(volume : Measure (Space n)) := by
      apply setIntegral_mono_on hconst hkint.integrableOn
        Metric.isOpen_ball.measurableSet
      intro x hx
      have hxnorm : ‖x - x₀‖ < r := by
        simpa [Metric.mem_ball, dist_eq_norm] using hx
      have hpair :
          |pairing (u j - u₀) (x - x₀)| < ε / 2 := by
        calc
          |pairing (u j - u₀) (x - x₀)| ≤
              ((n : ℝ) * ‖u j - u₀‖) * ‖x - x₀‖ :=
            MonomialDivergence.abs_pairing_le_dimension_mul_norm
              (u j - u₀) (x - x₀)
          _ ≤ ((n : ℝ) * ‖u j - u₀‖) * r := by
            apply mul_le_mul_of_nonneg_left hxnorm.le
            positivity
          _ < ε / 2 := hj
      have hsplit :
          phase (u j) φ x - phase (u j) φ x₀ =
            (phase u₀ φ x - phase u₀ φ x₀) +
              pairing (u j - u₀) (x - x₀) := by
        simp only [phase, pairing, Pi.sub_apply, sub_mul, mul_sub,
          Finset.sum_sub_distrib]
        ring
      have hlocal := hball hx
      have hphase : phase (u j) φ x₀ - ε ≤ phase (u j) φ x := by
        have habs := (abs_lt.mp hpair).1
        change phase u₀ φ x₀ - ε / 2 < phase u₀ φ x at hlocal
        linarith
      unfold monomialWeight
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_left hphase hk.le
    _ ≤ monomialIntegral k (u j) φ := by
      unfold monomialIntegral
      apply setIntegral_le_integral hkint
      exact Filter.Eventually.of_forall fun x => (Real.exp_pos _).le
end Ehrhart.BergmanJetMovingMonomialProbability
