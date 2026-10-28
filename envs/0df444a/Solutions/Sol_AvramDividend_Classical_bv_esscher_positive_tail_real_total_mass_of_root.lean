-- Prove2me | solution 1 for AvramDividend.Classical.bv_esscher_positive_tail_real_total_mass_of_root
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T09:10:08.218986+00:00
-- url     : https://prove2.me/submissions/19a02e6c-eb83-4ca9-aa20-bfb484cc6552

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.ENNReal.Real
import Theorems.Thm_AvramDividend_Classical_bv_esscher_root_subcritical_kernel_mass
import Theorems.Thm_AvramDividend_Classical_esscher_tail_kernel_mass_as_discounted_first_moment
import Theorems.Thm_AvramDividend_Classical_positive_jump_tail_density_total_mass
import Theorems.Thm_AvramDividend_Classical_positive_jump_tail_real_integral_eq_firstMoment_toReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The positive-time real Esscher strict tail has exactly the finite
root-discounted jump-magnitude first moment as its total mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hbv : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    (∫ t in Ioi (0 : ℝ),
      ENNReal.toReal (((X.ν.map (fun y : ℝ => Real.toNNReal (-y))).withDensity
        (fun z : ℝ≥0 => ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))))
        {z : ℝ≥0 | t < (z : ℝ)}) ∂volume) =
      ∫ z : ℝ≥0, (z : ℝ) * Real.exp (-(φ * (z : ℝ)))
        ∂(X.ν.map (fun y : ℝ => Real.toNNReal (-y))) := by
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
  have hmass :
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
    rw [hmass, ← htoReal]
    exact ENNReal.ofReal_lt_top
  have hreal :=
    positive_jump_tail_real_integral_eq_firstMoment_toReal μφ hfirst
  have hIpos :
      0 ≤ ∫ z : ℝ≥0,
        (z : ℝ) * Real.exp (-(φ * (z : ℝ))) ∂μ :=
    integral_nonneg_of_ae hpos
  rw [hmass, ← htoReal] at hreal
  simpa only [μ, μφ, ENNReal.toReal_ofReal hIpos] using hreal
