-- Prove2me | solution 1 for AvramDividend.Classical.zero_scale_kernel_tilt_all_parameter_laplace
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T23:32:00.417826+00:00
-- url     : https://prove2.me/submissions/1daae8d6-9ceb-4d1b-959a-1fcce0202e51

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Any exponential tilt of a zero-discount scale has the expected shifted Laplace mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (W₀ : ℝ → ℝ) (hW₀ : IsScaleFunction X 0 W₀)
    (q θ η : ℝ) (hη0 : 0 ≤ η) (hψη : 0 < X.ψ η) :
    IntegrableOn
      (fun x : ℝ => Real.exp (-((η - θ) * x)) *
        (q * (Real.exp (-(θ * x)) * W₀ x)))
      (Ioi (0 : ℝ)) volume ∧
    (∫ x in Ioi (0 : ℝ),
      Real.exp (-((η - θ) * x)) *
        (q * (Real.exp (-(θ * x)) * W₀ x)) ∂volume) =
      q / X.ψ η := by
  obtain ⟨hWi, hWmass⟩ := hW₀.2.2.2.2 η hη0 hψη
  have hid (x : ℝ) :
      Real.exp (-((η - θ) * x)) *
        (q * (Real.exp (-(θ * x)) * W₀ x)) =
      q * (Real.exp (-(η * x)) * W₀ x) := by
    calc
      _ = q * ((Real.exp (-((η - θ) * x)) *
            Real.exp (-(θ * x))) * W₀ x) := by ring
      _ = q * (Real.exp (-(η * x)) * W₀ x) := by
        rw [← Real.exp_add]
        rw [show -((η - θ) * x) + -(θ * x) = -(η * x) by ring]
  have heq :
      (fun x : ℝ => Real.exp (-((η - θ) * x)) *
        (q * (Real.exp (-(θ * x)) * W₀ x))) =
      (fun x : ℝ => q * (Real.exp (-(η * x)) * W₀ x)) :=
    funext hid
  constructor
  · change Integrable _ (volume.restrict (Ioi (0 : ℝ)))
    simpa only [heq] using hWi.const_mul q
  · rw [heq, integral_const_mul, hWmass]
    simp only [sub_zero, div_eq_mul_inv]
