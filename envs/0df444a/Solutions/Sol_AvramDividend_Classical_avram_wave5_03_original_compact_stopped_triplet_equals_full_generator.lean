-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03_original_compact_stopped_triplet_equals_full_generator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T15:45:59.432232+00:00
-- url     : https://prove2.me/submissions/6df8602f-741f-4382-8e03-942f0ec1c6bb

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact source triplet identity, with original ruin and original prepayment reserve. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (u v δ q : ℝ) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let ρ : ℝ≥0 × Ω → ℝ := fun p =>
      if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then 1 else 0
    let G : ℝ≥0 × Ω → ℝ := fun p =>
      if Y p ∈ Icc (u + δ) v then X.σ ^ 2 / 2 * iteratedDeriv 2 w (Y p)
      else 0
    let L : ℝ≥0 × Ω → ℝ := fun p =>
      if Y p ∈ Icc (u + δ) v then X.c * deriv w (Y p) - q * w (Y p)
      else 0
    let JG : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      ρ p.1 * (if Y p.1 ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
    ∀ p : ℝ≥0 × Ω,
      (ρ p * G p + ρ p * L p) +
        (∫ z in Iio (0 : ℝ), JG (p,z) ∂X.ν) =
      ρ p * (if Y p ∈ Icc (u + δ) v then
        X.generator w (Y p) - q * w (Y p) else 0) := by
  classical
  let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  let ρ : ℝ≥0 × Ω → ℝ := fun p =>
    if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then 1 else 0
  let G : ℝ≥0 × Ω → ℝ := fun p =>
    if Y p ∈ Icc (u + δ) v then X.σ ^ 2 / 2 * iteratedDeriv 2 w (Y p)
    else 0
  let L : ℝ≥0 × Ω → ℝ := fun p =>
    if Y p ∈ Icc (u + δ) v then X.c * deriv w (Y p) - q * w (Y p)
    else 0
  let JG : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    ρ p.1 * (if Y p.1 ∈ Icc (u + δ) v then
      SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
  change ∀ p : ℝ≥0 × Ω,
    (ρ p * G p + ρ p * L p) +
      (∫ z in Iio (0 : ℝ), JG (p,z) ∂X.ν) =
    ρ p * (if Y p ∈ Icc (u + δ) v then
      X.generator w (Y p) - q * w (Y p) else 0)
  intro p
  by_cases hs : (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2
  · by_cases hb : Y p ∈ Icc (u + δ) v
    · simp only [ρ, G, L, JG, if_pos hs, if_pos hb, one_mul]
      unfold SpectrallyNegativeLevy.generator
      ring
    · simp only [ρ, G, L, JG, if_pos hs, if_neg hb,
        one_mul, mul_zero, integral_zero, zero_add, add_zero]
  · simp only [ρ, JG, if_neg hs, zero_mul, integral_zero, zero_add]
