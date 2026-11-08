-- Prove2me | solution 1 for AvramDividend.Classical.avram_coord9_uniform_initial_generator_sum_exact_first_row
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T19:17:32.719339+00:00
-- url     : https://prove2.me/submissions/62391c67-a5a8-40ca-8147-db91250454cf

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q T x : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ)
    (u : ℕ → ℕ → ℝ≥0) (B : ℕ → Ω → ℝ) (K : Ω → ℝ)
    (hzero : u 0 0 = 0)
    (hone : (u 0 1 : ℝ) = T / 2)
    (hBraw : ∀ ω, B 0 ω =
      (let Z : ℕ → ℝ := fun i => Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u 0 i)
       ∑ i ∈ Finset.range (0 + 1),
         if (u 0 i : ℝ≥0∞) < ruinTime X x D ω ∧
             0 < Z i ∧ ENNReal.ofReal (Z i) < C then
           Real.exp (-(q * (u 0 i : ℝ))) *
             (X.generator w (Z i) - q * w (Z i)) *
             ((u 0 (i + 1) : ℝ) - (u 0 i : ℝ))
         else 0) + K ω) :
    ∀ ω, B 0 ω =
      (let Z := Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) 0
       if (0 : ℝ≥0∞) < ruinTime X x D ω ∧
           0 < Z ∧ ENNReal.ofReal Z < C then
         Real.exp (-(q * (0 : ℝ))) *
           (X.generator w Z - q * w Z) * (T / 2)
       else 0) + K ω := by
  intro ω
  rw [hBraw ω]
  simp [hzero, hone]
