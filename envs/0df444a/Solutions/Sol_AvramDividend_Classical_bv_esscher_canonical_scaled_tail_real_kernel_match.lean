-- Prove2me | solution 1 for AvramDividend.Classical.bv_esscher_canonical_scaled_tail_real_kernel_match
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T22:36:53.590002+00:00
-- url     : https://prove2.me/submissions/cce1584f-ac1c-4cb4-abd6-71e9ec0a896e

import Theorems.Thm_AvramDividend_Classical_bv_esscher_root_positive_subunit_kernel_package
import Theorems.Thm_AvramDividend_Classical_positive_strict_tail_scaled_drift_real_density
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_positive_jump_tail_density_total_mass
import Theorems.Thm_AvramDividend_Classical_esscher_tail_kernel_mass_as_discounted_first_moment
import Theorems.Thm_AvramDividend_Classical_bv_esscher_root_subcritical_kernel_mass
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The canonical Esscher kernel and the positive subunit real renewal kernel coincide after drift scaling. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hbv : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ∃ (k : ℝ → ℝ) (ρ : ℝ),
      0 < ρ ∧ ρ < 1 ∧
      ContinuousOn k (Ioi (0 : ℝ)) ∧
      AntitoneOn k (Ioi (0 : ℝ)) ∧
      (∀ t : ℝ, t ≤ 0 → k t = 0) ∧
      (∀ t : ℝ, 0 ≤ k t) ∧
      IntegrableOn k (Ioi (0 : ℝ)) volume ∧
      (∫ t in Ioi (0 : ℝ), k t ∂volume) = ρ ∧
      (ENNReal.ofReal X.drift)⁻¹ •
        (volume.restrict (Ioi (0 : ℝ))).withDensity (fun t : ℝ =>
          ((X.ν.map (fun y : ℝ => Real.toNNReal (-y))).withDensity
            (fun z : ℝ≥0 => ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))))
              {z : ℝ≥0 | t < (z : ℝ)}) =
        (volume : Measure ℝ).withDensity
          (fun t : ℝ => ENNReal.ofReal (k t)) := by
  obtain ⟨k, ρ, hkdef, hρpos, hρlt, hcont, hanti,
    hzero, hkpos, hint, hmass⟩ :=
    bv_esscher_root_positive_subunit_kernel_package
      X hX hbv q hq φ hφ hroot
  have hd : 0 < X.drift := (bv_standing_drift_pos X hX hbv).1
  let μ : Measure ℝ≥0 := X.ν.map (fun y : ℝ => Real.toNNReal (-y))
  let μφ : Measure ℝ≥0 := μ.withDensity
    (fun z : ℝ≥0 => ENNReal.ofReal (Real.exp (-(φ * (z : ℝ)))))
  have hfirst : (∫⁻ z : ℝ≥0, ENNReal.ofReal (z : ℝ) ∂μφ) < ⊤ := by
    rw [← positive_jump_tail_density_total_mass,
      esscher_tail_kernel_mass_as_discounted_first_moment μ φ]
    exact (bv_esscher_root_subcritical_kernel_mass
      X hbv q hq φ hφ hroot).1.lintegral_lt_top
  have hscaled :=
    positive_strict_tail_scaled_drift_real_density μφ hfirst X.drift hd
  have hmatch : (ENNReal.ofReal X.drift)⁻¹ •
      (volume.restrict (Ioi (0 : ℝ))).withDensity (fun t : ℝ =>
        ((X.ν.map (fun y : ℝ => Real.toNNReal (-y))).withDensity
          (fun z : ℝ≥0 => ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))))
            {z : ℝ≥0 | t < (z : ℝ)}) =
      (volume : Measure ℝ).withDensity (fun t : ℝ => ENNReal.ofReal (k t)) := by
    simpa only [μ, μφ, hkdef] using hscaled
  exact ⟨k, ρ, hρpos, hρlt, hcont, hanti, hzero, hkpos, hint, hmass, hmatch⟩