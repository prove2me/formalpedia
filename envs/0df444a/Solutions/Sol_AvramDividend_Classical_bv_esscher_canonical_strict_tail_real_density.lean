-- Prove2me | solution 1 for AvramDividend.Classical.bv_esscher_canonical_strict_tail_real_density
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T22:12:22.280544+00:00
-- url     : https://prove2.me/submissions/09a40d55-3f5a-46a0-81fe-e26dd71f5209

import Theorems.Thm_AvramDividend_Classical_positive_jump_tail_density_total_mass
import Theorems.Thm_AvramDividend_Classical_esscher_tail_kernel_mass_as_discounted_first_moment
import Theorems.Thm_AvramDividend_Classical_bv_esscher_root_subcritical_kernel_mass
import Theorems.Thm_AvramDividend_Classical_positive_strict_tail_measure_real_density
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The exact discounted Esscher jump-tail measure has its truncated real density. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hbv : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (φ : ℝ) (hφ : 0 < φ)
    (hroot : X.ψ φ = q) :
    (volume.restrict (Ioi (0 : ℝ))).withDensity (fun t : ℝ =>
      ((X.ν.map (fun y : ℝ => Real.toNNReal (-y))).withDensity
        (fun z : ℝ≥0 => ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))))
        {z : ℝ≥0 | t < (z : ℝ)}) =
    volume.withDensity (fun t : ℝ =>
      ENNReal.ofReal (if 0 < t then
        (((X.ν.map (fun y : ℝ => Real.toNNReal (-y))).withDensity
          (fun z : ℝ≥0 => ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))))
          {z : ℝ≥0 | t < (z : ℝ)}).toReal else 0)) := by
  let μ : Measure ℝ≥0 := X.ν.map (fun y : ℝ => Real.toNNReal (-y))
  let μφ : Measure ℝ≥0 := μ.withDensity
    (fun z : ℝ≥0 => ENNReal.ofReal (Real.exp (-(φ * (z : ℝ)))))
  have hfirst : (∫⁻ z : ℝ≥0, ENNReal.ofReal (z : ℝ) ∂μφ) < ⊤ := by
    rw [← positive_jump_tail_density_total_mass,
      esscher_tail_kernel_mass_as_discounted_first_moment μ φ]
    exact (bv_esscher_root_subcritical_kernel_mass
      X hbv q hq φ hφ hroot).1.lintegral_lt_top
  exact positive_strict_tail_measure_real_density μφ hfirst