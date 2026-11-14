-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a131_b0_original_clipped_spatial_m_vs_succ_last_source_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T11:26:24.584201+00:00
-- url     : https://prove2.me/submissions/6c648b96-bf27-4ace-a075-3733f78c3424

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

/-- Exact final-source-cell correction between the m-cell original positive-interior Gaussian root and the earlier m+1-cell integrability theorem. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ)
    (q : ℝ) (n m : ℕ) (ρ : ℝ≥0) (ω : Ω) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) ρ
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
    let Z : ℕ → ℝ := fun i =>
      x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
    (∑ i ∈ Finset.range (m + 1),
      E (v (i + 1)) * (w (Z i) - w (Y (v i)))) =
    (∑ i ∈ Finset.range m,
      E (v (i + 1)) * (w (Z i) - w (Y (v i)))) +
    E (v (m + 1)) * (w (Z m) - w (Y (v m))) := by
  dsimp only
  rw [Finset.sum_range_succ]
