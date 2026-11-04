-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_original_controlled_pre_source_integrable_HJB_expected_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:26:30.817575+00:00
-- url     : https://prove2.me/submissions/23cdd092-7b8e-4060-882f-430b5bb0e8dd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_controlled_pre_source_discounted_HJB_nonpos
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical Filter
open scoped NNReal ENNReal
noncomputable section

/-- At an original controlled source clock, the genuinely integrable localised
HJB jump residual has a nonpositive expected signed value. -/
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
    (hHJB : ∀ ω ∈ E, X.generator w (Upre ω) - q * w (Upre ω) ≤ 0)
    (F : Ω → ℝ)
    (hF : ∀ ω ∈ E, F ω =
      Real.exp (-(q * (s : ℝ))) *
        (X.drift * deriv w (Upre ω) +
          (∫ z in Iio (0 : ℝ), w (Upre ω + z) - w (Upre ω) ∂X.ν) -
          q * w (Upre ω)))
    (hFzero : ∀ ω ∉ E, F ω = 0)
    (hFint : Integrable F P) : (∫ ω, F ω ∂P) ≤ 0 := by
  have hpoint :=
    avram_p3_b_bvjump_original_controlled_pre_source_discounted_HJB_nonpos
      X hBV D hD x w q s Upre hUpre E hGen hHJB
  apply integral_nonpos_of_ae
  exact Filter.Eventually.of_forall (by
    intro ω
    by_cases hω : ω ∈ E
    · rw [hF ω hω]
      exact hpoint ω hω
    · rw [hFzero ω hω]
      exact le_refl 0)
