-- Prove2me | solution 1 for Ehrhart.BergmanJetMovingMonomialObservableConvergence.tendsto_integral_bounded_continuous_of_concentrating_normalized_density
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.658478+00:00
-- url     : https://prove2.me/submissions/a70a4a60-e859-48e7-ab8b-2fc4c6c7085b

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetMovingMonomialObservableConvergence
open Set Function Filter MeasureTheory Metric
open LaplaceAsymptotics MonomialIntegrability MomentOptimizer MomentFirstVariation
open MomentTargetGeodesic MomentRegularity MomentWeakBergman BergmanJetMovingMonomialTailConvergence
open scoped BigOperators ENNReal NNReal Topology
namespace Ehrhart.BergmanJetMovingMonomialObservableConvergence
theorem _root_.solution
    {n : ℕ}
    (w : ℕ → Space n → ℝ)
    (hw : ∀ᶠ k : ℕ in atTop,
      Integrable (w k) (volume : Measure (Space n)))
    (hwnonneg : ∀ k : ℕ, ∀ x : Space n, 0 ≤ w k x)
    (hwmass : ∀ᶠ k : ℕ in atTop,
      (∫ x : Space n, w k x
        ∂(volume : Measure (Space n))) = 1)
    (x₀ : Space n)
    (hwtail : ∀ {r : ℝ}, 0 < r →
      Tendsto
        (fun k : ℕ =>
          ∫ x : Space n in (Metric.ball x₀ r)ᶜ,
            w k x ∂(volume : Measure (Space n)))
        atTop (𝓝 (0 : ℝ)))
    (f : Space n → ℝ)
    (hf : Continuous f)
    (C : ℝ)
    (hC : ∀ x : Space n, |f x| ≤ C) :
    Tendsto
      (fun k : ℕ =>
        ∫ x : Space n, f x * w k x
          ∂(volume : Measure (Space n)))
      atTop (𝓝 (f x₀)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨r, hr, hclose⟩ :=
    (Metric.continuousAt_iff.mp hf.continuousAt)
      (ε / 2) (half_pos hε)
  have htail :
      ∀ᶠ k : ℕ in atTop,
        (2 * C) *
          (∫ x : Space n in (Metric.ball x₀ r)ᶜ,
            w k x ∂(volume : Measure (Space n))) < ε / 2 := by
    have ht :
        Tendsto
          (fun k : ℕ =>
            (2 * C) *
              (∫ x : Space n in (Metric.ball x₀ r)ᶜ,
                w k x ∂(volume : Measure (Space n))))
          atTop (𝓝 (0 : ℝ)) := by
      simpa using (hwtail hr).const_mul (2 * C)
    have hopen : Set.Iio (ε / 2) ∈ 𝓝 (0 : ℝ) :=
      Iio_mem_nhds (half_pos hε)
    simpa using ht hopen
  refine Filter.eventually_atTop.mp ?_
  filter_upwards [hw, hwmass, htail] with k hk hkmass hktail
  have hfint :
      Integrable (fun x : Space n => f x * w k x)
        (volume : Measure (Space n)) :=
    hk.bdd_mul hf.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        simpa [Real.norm_eq_abs] using hC x)
  have hcint :
      Integrable (fun x : Space n => f x₀ * w k x)
        (volume : Measure (Space n)) :=
    hk.const_mul (f x₀)
  have hdiffint :
      Integrable
        (fun x : Space n => (f x - f x₀) * w k x)
        (volume : Measure (Space n)) := by
    refine (hfint.sub hcint).congr ?_
    filter_upwards [] with x
    change
      f x * w k x - f x₀ * w k x =
        (f x - f x₀) * w k x
    ring
  have hdiff :
      (∫ x : Space n, f x * w k x
        ∂(volume : Measure (Space n))) - f x₀ =
        ∫ x : Space n,
          (f x - f x₀) * w k x
          ∂(volume : Measure (Space n)) := by
    calc
      (∫ x : Space n, f x * w k x
        ∂(volume : Measure (Space n))) - f x₀ =
          (∫ x : Space n, f x * w k x
            ∂(volume : Measure (Space n))) -
            f x₀ *
              (∫ x : Space n, w k x
                ∂(volume : Measure (Space n))) := by
          rw [hkmass]
          ring
      _ = (∫ x : Space n, f x * w k x
            ∂(volume : Measure (Space n))) -
            (∫ x : Space n, f x₀ * w k x
              ∂(volume : Measure (Space n))) := by
          rw [MeasureTheory.integral_const_mul]
      _ = ∫ x : Space n,
            (f x - f x₀) * w k x
            ∂(volume : Measure (Space n)) := by
          rw [← MeasureTheory.integral_sub hfint hcint]
          apply MeasureTheory.integral_congr_ae
          filter_upwards [] with x
          ring
  have hnormint := hdiffint.norm
  have hball :
      (∫ x : Space n in Metric.ball x₀ r,
        ‖(f x - f x₀) * w k x‖
        ∂(volume : Measure (Space n))) ≤
        (ε / 2) *
          (∫ x : Space n in Metric.ball x₀ r,
            w k x ∂(volume : Measure (Space n))) := by
    rw [← MeasureTheory.integral_const_mul]
    apply setIntegral_mono_on
      hnormint.integrableOn
      ((hk.const_mul (ε / 2)).integrableOn)
      Metric.isOpen_ball.measurableSet
    intro x hx
    have hnear : |f x - f x₀| < ε / 2 := by
      have hd := hclose (Metric.mem_ball.mp hx)
      simpa [Real.dist_eq] using hd
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (hwnonneg k x)]
    exact mul_le_mul_of_nonneg_right hnear.le (hwnonneg k x)
  have hfar :
      (∫ x : Space n in (Metric.ball x₀ r)ᶜ,
        ‖(f x - f x₀) * w k x‖
        ∂(volume : Measure (Space n))) ≤
        (2 * C) *
          (∫ x : Space n in (Metric.ball x₀ r)ᶜ,
            w k x ∂(volume : Measure (Space n))) := by
    rw [← MeasureTheory.integral_const_mul]
    apply setIntegral_mono_on
      hnormint.integrableOn
      ((hk.const_mul (2 * C)).integrableOn)
      Metric.isOpen_ball.measurableSet.compl
    intro x _
    have habs : |f x - f x₀| ≤ 2 * C := by
      calc
        |f x - f x₀| ≤ |f x| + |f x₀| := abs_sub _ _
        _ ≤ C + C := add_le_add (hC x) (hC x₀)
        _ = 2 * C := by ring
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (hwnonneg k x)]
    exact mul_le_mul_of_nonneg_right habs (hwnonneg k x)
  have hballmass :
      (∫ x : Space n in Metric.ball x₀ r,
        w k x ∂(volume : Measure (Space n))) ≤ 1 := by
    rw [← hkmass]
    exact setIntegral_le_integral hk
      (Filter.Eventually.of_forall fun x => hwnonneg k x)
  rw [Real.dist_eq, hdiff]
  calc
    |∫ x : Space n,
        (f x - f x₀) * w k x
        ∂(volume : Measure (Space n))| ≤
        ∫ x : Space n,
          ‖(f x - f x₀) * w k x‖
          ∂(volume : Measure (Space n)) := by
      simpa [Real.norm_eq_abs] using
        (MeasureTheory.norm_integral_le_integral_norm
          (fun x : Space n => (f x - f x₀) * w k x))
    _ =
        (∫ x : Space n in Metric.ball x₀ r,
          ‖(f x - f x₀) * w k x‖
          ∂(volume : Measure (Space n))) +
        (∫ x : Space n in (Metric.ball x₀ r)ᶜ,
          ‖(f x - f x₀) * w k x‖
          ∂(volume : Measure (Space n))) :=
      (integral_add_compl Metric.isOpen_ball.measurableSet hnormint).symm
    _ ≤ (ε / 2) *
          (∫ x : Space n in Metric.ball x₀ r,
            w k x ∂(volume : Measure (Space n))) +
        (2 * C) *
          (∫ x : Space n in (Metric.ball x₀ r)ᶜ,
            w k x ∂(volume : Measure (Space n))) :=
      add_le_add hball hfar
    _ ≤ ε / 2 +
        (2 * C) *
          (∫ x : Space n in (Metric.ball x₀ r)ᶜ,
            w k x ∂(volume : Measure (Space n))) := by
      have hb :=
        mul_le_mul_of_nonneg_left hballmass (half_pos hε).le
      nlinarith
    _ < ε := by linarith
end Ehrhart.BergmanJetMovingMonomialObservableConvergence
