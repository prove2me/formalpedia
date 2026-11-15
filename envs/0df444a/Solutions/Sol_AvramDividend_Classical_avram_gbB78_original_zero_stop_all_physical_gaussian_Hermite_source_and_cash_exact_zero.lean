-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB78_original_zero_stop_all_physical_gaussian_Hermite_source_and_cash_exact_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T23:52:07.963679+00:00
-- url     : https://prove2.me/submissions/36cb606d-d88c-4c61-bd8f-316f213cdc32

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ)
    (ρ : Ω → ℝ≥0) (δ : ℝ) (j n : ℕ) :
  let M : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
      let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
      let a : ℝ := δ / 2
      let b : ℝ := C.toReal *
        (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
      let Y : ℕ → Ω → ℝ := fun i η =>
        x + X.X (s i) η - rightLimit D (s i) η
      let Z : ℕ → Ω → ℝ := fun i η =>
        X.X (s i + Δ) η - X.X (s i) η - (Δ : ℝ) * X.c
      let G : ℕ → Ω → ℝ := fun i η =>
        if s i < ρ η then Real.exp (-(q * (s i : ℝ))) *
          (if Y i η ∈ Icc a b then deriv w (Y i η) else 1)
        else 0
      let H : ℕ → Ω → ℝ := fun i η =>
        if s i < ρ η then (1 / 2 : ℝ) *
          Real.exp (-(q * (s i : ℝ))) *
          (if Y i η ∈ Icc a b then iteratedDeriv 2 w (Y i η) else 0)
        else 0
      (Finset.range (m + 1)).sum (fun i =>
        G i ω * Z i ω + H i ω *
          (Z i ω ^ 2 - (Δ : ℝ) * X.σ ^ 2))
    let b : ℝ := C.toReal *
        (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
    let F : Ω → ℝ := fun ω =>
        if ρ ω = 0 then w x else
          Real.exp (-(q * (ρ ω : ℝ))) *
            w (riskProcess X x D (ρ ω) ω) +
          (∫⁻ z in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
            ENNReal.ofReal (Real.exp (-(q * z)))
            ∂(dividendMeasure D ω)).toReal
    ∀ (m : ℕ) (ω : Ω), ρ ω = 0 →
      F ω = w x ∧ M m ω = 0 := by
  dsimp only
  intro m ω hρ
  constructor
  · simp [hρ]
  · simp [hρ]
