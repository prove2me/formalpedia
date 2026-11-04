-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_original_controlled_pre_source_discounted_HJB_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:16:59.321002+00:00
-- url     : https://prove2.me/submissions/3b98860c-7498-44e6-a84b-6bcbeeb4cbcd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_discounted_HJB_source_jump_residual_nonpos
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Localised signed HJB compensation at the original controlled reserve's
left source state; dividend right payments are kept in the actual state. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (x : ℝ) (w : ℝ → ℝ) (q : ℝ) (s : ℝ≥0)
    (Upre : Ω → ℝ)
    (hUpre : ∀ ω, Upre ω = Function.leftLim
      (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) s)
    (E : Set Ω)
    (hGen : ∀ ω ∈ E, X.GeneratorIntegrable w (Upre ω))
    (hHJB : ∀ ω ∈ E, X.generator w (Upre ω) - q * w (Upre ω) ≤ 0) :
    ∀ ω ∈ E,
      Real.exp (-(q * (s : ℝ))) *
        (X.drift * deriv w (Upre ω) +
          (∫ z in Iio (0 : ℝ), w (Upre ω + z) - w (Upre ω) ∂X.ν) -
          q * w (Upre ω)) ≤ 0 := by
  intro ω hω
  exact avram_p3_b_bvjump_original_discounted_HJB_source_jump_residual_nonpos
    X hBV w (Upre ω) q (s : ℝ) (hGen ω hω) (hHJB ω hω)
