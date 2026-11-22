-- Prove2me | solution 1 for AvramDividend.Classical.avram_mathfin22_original_true_z_weighted_negativeband_countable_stop_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T19:22:22.611206+00:00
-- url     : https://prove2.me/submissions/c6e6a211-b6c7-4eaf-b4e7-420d1b60ce29

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mathfin22_original_true_z_weighted_negativeband_countable_stop_mean_zero_of_clock_L1
import Theorems.Thm_AvramDividend_Classical_avram_mathfin22_original_bounded_rightCont_stopping_clock_real_integrable
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

/-- The genuine physical stopped signed z-weighted Levy jump integral is centred. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (a b : ℕ) (hab : a ≤ b)
    (τ : Ω → WithTop ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont τ)
    (hτbound : ∀ ω, τ ω ≤ (T : WithTop ℝ≥0))
    (hτcount : (Set.range τ).Countable)
    :
    let B : Set ℝ :=
      Ioc (-(1 / ((a : ℝ) + 1))) (-(1 / ((b : ℝ) + 1)))
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {s : ℝ≥0 |
        0 < s ∧ X.X s ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) s ≠ 0}).map
        (fun s : ℝ≥0 => (s, X.X s ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) s)))
    let J : Ω → ℝ := fun ω =>
      (∫ p in Ioc 0 (τ ω).untopA ×ˢ B, p.2 ∂NX ω) -
        (((τ ω).untopA : ℝ) * (∫ z in B, z ∂X.ν))
    Integrable J P ∧ (∫ ω, J ω ∂P) = 0 := by
  classical
  intro B NX J
  have hClock :=
    avram_mathfin22_original_bounded_rightCont_stopping_clock_real_integrable
      (P := P) (𝓕 := 𝓕) T τ hτ hτbound
  simpa only [B, NX, J] using
    (avram_mathfin22_original_true_z_weighted_negativeband_countable_stop_mean_zero_of_clock_L1
      X T a b hab τ hτ hτbound hτcount hClock)
