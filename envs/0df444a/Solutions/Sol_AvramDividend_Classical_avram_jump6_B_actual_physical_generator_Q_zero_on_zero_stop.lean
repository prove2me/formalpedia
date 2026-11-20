-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_actual_physical_generator_Q_zero_on_zero_stop
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T21:54:54.179819+00:00
-- url     : https://prove2.me/submissions/c2618079-ba28-4dd7-8f48-ec68ccc1bc5f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (σ : Ω → ℝ≥0) (u : ℕ → ℕ → ℝ≥0) (m : ℕ → ℕ)
    (j : ℕ) (ω : Ω) (hzero : σ ω = 0) :
    let v : ℕ → ℝ≥0 := fun i => min (u j i) (σ ω)
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
    (∑ i ∈ Finset.range (m j),
      E (v (i + 1)) * (((v (i + 1) - v i : ℝ≥0) : ℝ)) *
        (if 0 < Y (v i) ∧ ENNReal.ofReal (Y (v i)) < C then
          X.generator w (Y (v i)) - q * w (Y (v i))
         else 0)) = 0 := by
  have hv : ∀ i : ℕ, min (u j i) (σ ω) = 0 := by
    intro i
    simp [hzero]
  apply Finset.sum_eq_zero
  intro i hi
  simp [hv]