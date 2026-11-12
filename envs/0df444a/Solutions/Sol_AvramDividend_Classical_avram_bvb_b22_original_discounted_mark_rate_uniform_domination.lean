-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_b22_original_discounted_mark_rate_uniform_domination
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T22:11:10.494696+00:00
-- url     : https://prove2.me/submissions/3de478ff-5503-450d-bbe2-5d277e031d8a

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva20_original_closed_cap_mark_kernel_uniform_bound
import Theorems.Thm_AvramDividend_Classical_avram_bva20_masked_discounted_mark_rate_uniform_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A single compact-reserve bound dominates every original stopped discounted negative-mark sample. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (C : ℝ≥0∞) (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ)
    (hKernel : ∀ s : Set ℝ, IsCompact s →
      s ⊆ {b : ℝ | 0 ≤ b ∧ ENNReal.ofReal b ≤ C} →
      UniformContinuousOn
        (fun b : ℝ => ∫ z in Iio (0 : ℝ), w (b + z) - w b ∂X.ν) s)
    (q : ℝ) (hq : 0 ≤ q) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω),
        let U : ℝ≥0 → ℝ := fun r => Function.leftLim
          (fun z : ℝ≥0 => x + X.X z ω - rightLimit D z ω) r
        |if (t : ℝ≥0∞) < ruinTime X x D ω ∧
             0 ≤ U t ∧ ENNReal.ofReal (U t) ≤ C then
             Real.exp (-(q * (t : ℝ))) *
               ∫ z in Iio (0 : ℝ), w (U t + z) - w (U t) ∂X.ν
           else 0| ≤ B := by
  obtain ⟨B, hB, hψ⟩ :=
    avram_bva20_original_closed_cap_mark_kernel_uniform_bound C hFinite
      (fun b : ℝ => ∫ z in Iio (0 : ℝ), w (b + z) - w b ∂X.ν)
      hKernel
  refine ⟨B, hB, ?_⟩
  intro x D t ω
  dsimp only
  exact avram_bva20_masked_discounted_mark_rate_uniform_bound
    C (ruinTime X x D ω)
    (fun r : ℝ≥0 => Function.leftLim
      (fun z : ℝ≥0 => x + X.X z ω - rightLimit D z ω) r)
    (fun b : ℝ => ∫ z in Iio (0 : ℝ), w (b + z) - w b ∂X.ν)
    B q hB hq hψ t
