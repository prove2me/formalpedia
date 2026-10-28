-- Prove2me | solution 2 for AvramDividend.Classical.bv_esscher_positive_tail_real_total_mass_of_root
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T09:10:28.682119+00:00
-- url     : https://prove2.me/submissions/be1238e4-be86-4e2f-9d55-cb527c741039

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.ENNReal.Real
import Theorems.Thm_AvramDividend_Classical_bv_esscher_root_subcritical_kernel_mass
import Theorems.Thm_AvramDividend_Classical_esscher_tail_kernel_mass_as_discounted_first_moment
import Theorems.Thm_AvramDividend_Classical_positive_jump_tail_density_total_mass
import Theorems.Thm_AvramDividend_Classical_positive_jump_tail_real_integral_eq_firstMoment_toReal
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
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
  set μ := X.ν.map (fun y : ℝ => Real.toNNReal (-y))
  set μφ := μ.withDensity (fun z : ℝ≥0 => ENNReal.ofReal (Real.exp (-(φ * (z : ℝ)))))
  have hint := (AvramDividend.Classical.bv_esscher_root_subcritical_kernel_mass X hbv q hq φ hφ
      hroot).1
  have hmass : (∫⁻ z : ℝ≥0, ENNReal.ofReal (z : ℝ) ∂μφ) =
      ∫⁻ z : ℝ≥0, ENNReal.ofReal ((z : ℝ) * Real.exp (-(φ * (z : ℝ)))) ∂μ := by
    rw [← AvramDividend.Classical.positive_jump_tail_density_total_mass,
      AvramDividend.Classical.esscher_tail_kernel_mass_as_discounted_first_moment μ φ]
  have hfirst : (∫⁻ z : ℝ≥0, ENNReal.ofReal (z : ℝ) ∂μφ) < ⊤ := by
    rw [hmass]; exact hint.lintegral_lt_top
  rw [AvramDividend.Classical.positive_jump_tail_real_integral_eq_firstMoment_toReal μφ hfirst,
    hmass, integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun z => mul_nonneg z.2 (Real.exp_pos _).le)
      hint.aestronglyMeasurable]
