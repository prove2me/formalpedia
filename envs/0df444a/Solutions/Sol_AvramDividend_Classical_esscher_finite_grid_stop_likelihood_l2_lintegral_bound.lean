-- Prove2me | solution 1 for AvramDividend.Classical.esscher_finite_grid_stop_likelihood_l2_lintegral_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T14:35:40.465066+00:00
-- url     : https://prove2.me/submissions/845a5aa4-7b0d-446e-b10d-ca36134c1d6d

import Mathlib
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_likelihood_square_domination
import Theorems.Thm_AvramDividend_Classical_esscher_finite_grid_stopped_density_probability
import Theorems.Thm_AvramDividend_Classical_finite_grid_adapted_fibres_isStoppingTime
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (T H : ℝ≥0) (τ : Ω → ℝ≥0) (grid : Finset ℝ≥0)
    (hgrid : ∀ ω, τ ω ∈ grid)
    (hT : ∀ s ∈ grid, s ≤ T)
    (hstop : ∀ s ∈ grid, MeasurableSet[𝓕 s] {ω : Ω | τ ω = s})
    (hbound : ∀ ω, τ ω ≤ H) :
    (∫⁻ ω, ENNReal.ofReal
      (Real.exp ((2 * θ) * X.X (τ ω) ω -
        2 * (τ ω : ℝ) * X.ψ θ)) ∂P) ≤
      ENNReal.ofReal
        (Real.exp ((H : ℝ) * |X.ψ (2 * θ) - 2 * X.ψ θ|)) := by
  have hθ2 : 0 ≤ (2 : ℝ) * θ := mul_nonneg (by norm_num) hθ
  have hQ2 : IsProbabilityMeasure (P.withDensity
      (fun ω : Ω => ENNReal.ofReal
        (Real.exp ((2 * θ) * X.X (τ ω) ω -
          (τ ω : ℝ) * X.ψ (2 * θ))))) :=
    esscher_finite_grid_stopped_density_probability
      X (2 * θ) hθ2 T τ grid hgrid hT hstop
  have hτm : Measurable τ := by
    have hτtop : Measurable (fun ω : Ω => (τ ω : WithTop ℝ≥0)) :=
      (finite_grid_adapted_fibres_isStoppingTime τ grid hgrid hstop).measurable'
    have hh : Measurable (fun ω : Ω =>
        WithTop.untopD (0 : ℝ≥0) (τ ω : WithTop ℝ≥0)) :=
      (WithTop.measurable_untopD (0 : ℝ≥0)).comp hτtop
    simpa only [WithTop.untopD_coe] using hh
  have hXm : Measurable (fun ω : Ω => X.X (τ ω) ω) :=
    (chat04_levy_joint_time_state_measurable X).comp
      (hτm.prodMk measurable_id)
  have hτr : Measurable (fun ω : Ω => (τ ω : ℝ)) :=
    NNReal.continuous_coe.measurable.comp hτm
  have hDensity : Measurable (fun ω : Ω => ENNReal.ofReal
      (Real.exp ((2 * θ) * X.X (τ ω) ω -
        (τ ω : ℝ) * X.ψ (2 * θ)))) :=
    ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp
        ((measurable_const.mul hXm).sub (hτr.mul measurable_const)))
  have hmass : (∫⁻ ω, ENNReal.ofReal
      (Real.exp ((2 * θ) * X.X (τ ω) ω -
        (τ ω : ℝ) * X.ψ (2 * θ))) ∂P) = 1 := by
    haveI := hQ2
    have hu : (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp ((2 * θ) * X.X (τ ω) ω -
          (τ ω : ℝ) * X.ψ (2 * θ))))) Set.univ = 1 := measure_univ
    rw [withDensity_apply _ MeasurableSet.univ] at hu
    simpa using hu
  let c : ℝ := (H : ℝ) * |X.ψ (2 * θ) - 2 * X.ψ θ|
  have hnonneg : 0 ≤ Real.exp c := (Real.exp_pos c).le
  have hdom : ∀ ω,
      Real.exp ((2 * θ) * X.X (τ ω) ω -
        2 * (τ ω : ℝ) * X.ψ θ) ≤
      Real.exp c *
        Real.exp ((2 * θ) * X.X (τ ω) ω -
          (τ ω : ℝ) * X.ψ (2 * θ)) := by
    intro ω
    exact esscher_bounded_stop_likelihood_square_domination
      X θ hθ τ H hbound ω
  calc
    (∫⁻ ω, ENNReal.ofReal (Real.exp ((2 * θ) * X.X (τ ω) ω -
        2 * (τ ω : ℝ) * X.ψ θ)) ∂P) ≤
      (∫⁻ ω, ENNReal.ofReal (Real.exp c *
        Real.exp ((2 * θ) * X.X (τ ω) ω -
          (τ ω : ℝ) * X.ψ (2 * θ))) ∂P) := by
        apply lintegral_mono
        intro ω
        exact ENNReal.ofReal_le_ofReal (hdom ω)
    _ = (∫⁻ ω, ENNReal.ofReal (Real.exp c) *
        ENNReal.ofReal (Real.exp ((2 * θ) * X.X (τ ω) ω -
          (τ ω : ℝ) * X.ψ (2 * θ))) ∂P) := by
        apply lintegral_congr
        intro ω
        rw [ENNReal.ofReal_mul hnonneg]
    _ = ENNReal.ofReal (Real.exp c) *
        (∫⁻ ω, ENNReal.ofReal (Real.exp ((2 * θ) * X.X (τ ω) ω -
          (τ ω : ℝ) * X.ψ (2 * θ))) ∂P) := by
        exact lintegral_const_mul _ hDensity
    _ = ENNReal.ofReal
        (Real.exp ((H : ℝ) * |X.ψ (2 * θ) - 2 * X.ψ θ|)) := by
        rw [hmass, mul_one]
