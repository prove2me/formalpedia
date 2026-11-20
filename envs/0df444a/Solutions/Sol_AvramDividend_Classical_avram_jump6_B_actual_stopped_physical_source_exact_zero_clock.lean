-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_actual_stopped_physical_source_exact_zero_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T22:24:48.57165+00:00
-- url     : https://prove2.me/submissions/e205f2b1-af16-49ef-b1ac-b84e30a154a2

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
    (x q : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ)
    (σ : Ω → ℝ≥0) (u : ℕ → ℕ → ℝ≥0) (m : ℕ → ℕ)
    (j : ℕ) (ω : Ω) (hzero : σ ω = 0) :
    let v : ℕ → ℝ≥0 := fun i => min (u j i) (σ ω)
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t =>
      x + X.X t ω - rightLimit D t ω
    let Z : ℕ → ℝ := fun i =>
      x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
    Finset.sum (Finset.range (m j)) (fun i =>
      (E (v (i + 1)) - E (v i)) * w (Y (v i)) +
        E (v (i + 1)) * (w (Z i) - w (Y (v i)))) = 0 := by
  have hv : ∀ i : ℕ, min (u j i) (σ ω) = 0 := by
    intro i
    simp [hzero]
  apply Finset.sum_eq_zero
  intro i hi
  simp [hv]