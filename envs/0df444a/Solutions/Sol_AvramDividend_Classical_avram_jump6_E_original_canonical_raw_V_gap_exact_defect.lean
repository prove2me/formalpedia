-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_E_original_canonical_raw_V_gap_exact_defect
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T07:51:49.648879+00:00
-- url     : https://prove2.me/submissions/7b8c8489-3feb-435c-9220-524a935040cd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ)
    (w V : ℝ → ℝ) (D : ℝ≥0 → Ω → ℝ)
    (τ : Ω → ℝ≥0) (ω : Ω) (n j : ℕ) :
    let v : ℕ → ℝ≥0 := fun i =>
      min ((i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) (τ ω)
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
    let Z : ℕ → ℝ := fun i => x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
    let m : ℕ := (n + 1) * (j + 1)
    (∑ i ∈ Finset.range m,
      E (v (i + 1)) * (w (Y (v (i + 1))) - w (Z i))) =
    (∑ i ∈ Finset.range m,
      E (v (i + 1)) * (V (Y (v (i + 1))) - V (Z i))) +
    (∑ i ∈ Finset.range m,
      E (v (i + 1)) *
        ((w (Y (v (i + 1))) - V (Y (v (i + 1)))) -
         (w (Z i) - V (Z i)))) := by
  dsimp only
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring
