-- Prove2me | solution 2 for AvramDividend.Classical.bv_esscher_positive_tail_real_integrable_of_root
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T08:39:22.576008+00:00
-- url     : https://prove2.me/submissions/dc4aa04c-a45d-40f7-ac13-a9707bc6aa98

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Theorems.Thm_AvramDividend_Classical_bv_esscher_root_subcritical_kernel_mass
import Theorems.Thm_AvramDividend_Classical_esscher_tail_kernel_mass_as_discounted_first_moment
import Theorems.Thm_AvramDividend_Classical_positive_jump_tail_density_total_mass
import Theorems.Thm_AvramDividend_Classical_positive_jump_tail_real_integrable_of_finite_firstMoment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- At a BV Esscher root, the real discounted strict jump-tail is L1. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hbv : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    IntegrableOn (fun t : ℝ =>
      ENNReal.toReal (((X.ν.map (fun y : ℝ => Real.toNNReal (-y))).withDensity
        (fun z : ℝ≥0 => ENNReal.ofReal
          (Real.exp (-(φ * (z : ℝ))))))
        {z : ℝ≥0 | t < (z : ℝ)}))
      (Ioi (0 : ℝ)) volume := by
  let μ : Measure ℝ≥0 := X.ν.map (fun y : ℝ => Real.toNNReal (-y))
  let μφ : Measure ℝ≥0 :=
    μ.withDensity (fun z : ℝ≥0 =>
      ENNReal.ofReal (Real.exp (-(φ * (z : ℝ)))))
  obtain ⟨hA, _⟩ :=
    bv_esscher_root_subcritical_kernel_mass X hbv q hq φ hφ hroot
  have hpos : 0 ≤ᵐ[μ] (fun z : ℝ≥0 =>
      (z : ℝ) * Real.exp (-(φ * (z : ℝ)))) := by
    filter_upwards with z
    exact mul_nonneg (NNReal.coe_nonneg z) (Real.exp_pos _).le
  have htoReal :
      ENNReal.ofReal (∫ z : ℝ≥0,
        (z : ℝ) * Real.exp (-(φ * (z : ℝ))) ∂μ) =
      ∫⁻ z : ℝ≥0, ENNReal.ofReal
        ((z : ℝ) * Real.exp (-(φ * (z : ℝ)))) ∂μ :=
    ofReal_integral_eq_lintegral_ofReal hA hpos
  have heq :
      (∫⁻ z : ℝ≥0, ENNReal.ofReal (z : ℝ) ∂μφ) =
      (∫⁻ z : ℝ≥0, ENNReal.ofReal
        ((z : ℝ) * Real.exp (-(φ * (z : ℝ)))) ∂μ) := by
    calc
      _ = ((volume.restrict (Ioi (0 : ℝ))).withDensity
          (fun t : ℝ => μφ {z : ℝ≥0 | t < (z : ℝ)})) Set.univ :=
          (positive_jump_tail_density_total_mass μφ).symm
      _ = _ := esscher_tail_kernel_mass_as_discounted_first_moment μ φ
  have hfirst :
      (∫⁻ z : ℝ≥0, ENNReal.ofReal (z : ℝ) ∂μφ) < ⊤ := by
    rw [heq, ← htoReal]
    exact ENNReal.ofReal_lt_top
  simpa only [μ, μφ] using
    positive_jump_tail_real_integrable_of_finite_firstMoment μφ hfirst
