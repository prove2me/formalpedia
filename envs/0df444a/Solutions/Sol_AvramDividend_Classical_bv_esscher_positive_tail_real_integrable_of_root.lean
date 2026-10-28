-- Prove2me | solution 1 for AvramDividend.Classical.bv_esscher_positive_tail_real_integrable_of_root
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T08:38:34.152011+00:00
-- url     : https://prove2.me/submissions/d0922d99-2180-4856-bcec-735756feb19c

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Theorems.Thm_AvramDividend_Classical_bv_esscher_root_subcritical_kernel_mass
import Theorems.Thm_AvramDividend_Classical_esscher_tail_kernel_mass_as_discounted_first_moment
import Theorems.Thm_AvramDividend_Classical_positive_jump_tail_density_total_mass
import Theorems.Thm_AvramDividend_Classical_positive_jump_tail_real_integrable_of_finite_firstMoment
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
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
  set μ := X.ν.map (fun y : ℝ => Real.toNNReal (-y))
  apply AvramDividend.Classical.positive_jump_tail_real_integrable_of_finite_firstMoment
  rw [← AvramDividend.Classical.positive_jump_tail_density_total_mass,
    AvramDividend.Classical.esscher_tail_kernel_mass_as_discounted_first_moment μ φ]
  exact (AvramDividend.Classical.bv_esscher_root_subcritical_kernel_mass X hbv q hq φ hφ
    hroot).1.lintegral_lt_top
