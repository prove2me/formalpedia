-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03_actual_discounted_ruin_clock_generator_residual_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T08:36:18.0194+00:00
-- url     : https://prove2.me/submissions/a28aea26-7555-4b4b-b9f9-f26a73a5faba

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Source discounted generator drift has the required sign on actual stopped interior states. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (T : ℝ≥0)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (A : Set (ℝ≥0 × Ω))
    (hA : MeasurableSet[𝓕.rightCont.predictable] A)
    (hregion : ∀ p ∈ A,
      0 < Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∧
      ENNReal.ofReal (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) < C)
    (hInt : IntegrableOn
      (fun p : ℝ≥0 × Ω =>
        (if p.1 ≤ T then
          Real.exp (-(q * (p.1 : ℝ))) *
            (if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then
              (1 : ℝ) else 0)
         else 0) *
        (X.generator w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) -
          q * w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1)))
      A μ) :
    (∫ p in A,
      (if p.1 ≤ T then
        Real.exp (-(q * (p.1 : ℝ))) *
          (if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then
            (1 : ℝ) else 0)
       else 0) *
      (X.generator w (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) -
        q * w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1)) ∂μ) ≤ 0 := by
  classical
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  let ρ : ℝ≥0 × Ω → ℝ := fun p =>
    if p.1 ≤ T then
      Real.exp (-(q * (p.1 : ℝ))) *
        (if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then
          (1 : ℝ) else 0)
    else 0
  change (∫ p in A, ρ p * (X.generator w (Y p) - q * w (Y p)) ∂μ) ≤ 0
  apply MeasureTheory.integral_nonpos_of_ae
  filter_upwards [MeasureTheory.ae_restrict_mem hA] with p hp
  have hY : 0 < Y p ∧ ENNReal.ofReal (Y p) < C := hregion p hp
  have hg : X.generator w (Y p) - q * w (Y p) ≤ 0 :=
    (hw_gen (Y p) hY.1 hY.2).2
  have hρ : 0 ≤ ρ p := by
    by_cases ht : p.1 ≤ T
    · by_cases hs : (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2
      · simpa [ρ, ht, hs] using
          (le_of_lt (Real.exp_pos (-(q * (p.1 : ℝ)))))
      · simp [ρ, ht, hs]
    · simp [ρ, ht]
  exact mul_nonpos_of_nonneg_of_nonpos hρ hg
