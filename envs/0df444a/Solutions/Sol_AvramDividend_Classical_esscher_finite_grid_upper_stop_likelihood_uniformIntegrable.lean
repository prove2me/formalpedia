-- Prove2me | solution 1 for AvramDividend.Classical.esscher_finite_grid_upper_stop_likelihood_uniformIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T18:27:19.282997+00:00
-- url     : https://prove2.me/submissions/964e0e59-207c-49ed-8a7f-f7a12e4614db

import Mathlib
import Theorems.Thm_AvramDividend_Classical_uniformIntegrable_one_of_uniform_l2_seminorm_bound
import Theorems.Thm_AvramDividend_Classical_esscher_finite_grid_stop_likelihood_l2_seminorm_bound
import Theorems.Thm_AvramDividend_Classical_finite_grid_adapted_fibres_isStoppingTime
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter
open scoped ENNReal NNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (hθ : 0 ≤ θ)
    (T H : ℝ≥0)
    (τn : ℕ → Ω → ℝ≥0) (grid : ℕ → Finset ℝ≥0)
    (hgrid : ∀ n ω, τn n ω ∈ grid n)
    (hT : ∀ n s, s ∈ grid n → s ≤ T)
    (hstop : ∀ n s, s ∈ grid n →
      MeasurableSet[𝓕 s] {ω : Ω | τn n ω = s})
    (hbound : ∀ n ω, τn n ω ≤ H) :
    UniformIntegrable (fun n ω =>
      Real.exp (θ * X.X (τn n ω) ω -
        (τn n ω : ℝ) * X.ψ θ)) 1 P := by
  let f : ℕ → Ω → ℝ := fun n ω =>
    Real.exp (θ * X.X (τn n ω) ω -
      (τn n ω : ℝ) * X.ψ θ)
  let C : ℝ≥0 := ⟨Real.exp
    (((H : ℝ) * |X.ψ (2 * θ) - 2 * X.ψ θ|) / 2),
    (Real.exp_pos _).le⟩
  have hC : (C : ℝ≥0∞) = ENNReal.ofReal
      (Real.exp
        (((H : ℝ) * |X.ψ (2 * θ) - 2 * X.ψ θ|) / 2)) := by
    change (C : ℝ≥0∞) = ENNReal.ofReal (C : ℝ)
    exact ENNReal.ofReal_coe_nnreal.symm
  have hmeas (n : ℕ) : AEStronglyMeasurable (f n) P := by
    have hStopN : IsStoppingTime 𝓕
        (fun ω => (τn n ω : WithTop ℝ≥0)) :=
      finite_grid_adapted_fibres_isStoppingTime
        (τn n) (grid n) (hgrid n)
        (fun s hs => hstop n s hs)
    have hτtop : Measurable (fun ω : Ω =>
        (τn n ω : WithTop ℝ≥0)) := hStopN.measurable'
    have hτm : Measurable (τn n) := by
      have hh : Measurable (fun ω : Ω =>
          WithTop.untopD (0 : ℝ≥0)
            (τn n ω : WithTop ℝ≥0)) :=
        (WithTop.measurable_untopD (0 : ℝ≥0)).comp hτtop
      simpa only [WithTop.untopD_coe] using hh
    have hXm : Measurable (fun ω : Ω =>
        X.X (τn n ω) ω) :=
      (chat04_levy_joint_time_state_measurable X).comp
        (hτm.prodMk measurable_id)
    have hτr : Measurable (fun ω : Ω =>
        (τn n ω : ℝ)) :=
      NNReal.continuous_coe.measurable.comp hτm
    exact (Real.measurable_exp.comp
      ((measurable_const.mul hXm).sub
        (hτr.mul measurable_const))).aestronglyMeasurable
  have hnorm (n : ℕ) : eLpNorm (f n) (2 : ℝ≥0∞) P ≤ C := by
    rw [hC]
    exact esscher_finite_grid_stop_likelihood_l2_seminorm_bound
      X θ hθ T H (τn n) (grid n)
      (hgrid n)
      (fun s hs => hT n s hs)
      (fun s hs => hstop n s hs)
      (hbound n)
  exact uniformIntegrable_one_of_uniform_l2_seminorm_bound
    P f C hmeas hnorm
