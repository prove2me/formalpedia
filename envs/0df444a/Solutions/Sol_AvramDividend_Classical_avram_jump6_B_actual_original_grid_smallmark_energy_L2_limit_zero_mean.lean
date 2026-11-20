-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_actual_original_grid_smallmark_energy_L2_limit_zero_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T11:06:05.165415+00:00
-- url     : https://prove2.me/submissions/3c21f2a9-4016-4196-94b6-ae21c64e93e9

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_smallmark_Lp2_limit_from_physical_band_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_finite_grid_martingale_L2_limit_mean_zero
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (n : ℕ → ℕ) (s t : ℕ → ℕ → ℝ≥0)
    (W : ℕ → ℕ → Ω → ℝ)
    (hWPast : ∀ k, ∀ i ∈ Finset.range (n k),
      Measurable[𝓕 (s k i)] (W k i))
    (hWI : ∀ k, ∀ i ∈ Finset.range (n k), Integrable (W k i) P)
    (hXI : ∀ k, ∀ i ∈ Finset.range (n k), Integrable (X.X (t k i)) P)
    (hCellI : ∀ k, ∀ i ∈ Finset.range (n k), Integrable (fun ω =>
      W k i ω * (X.X (s k i + t k i) ω - X.X (s k i) ω -
        (∫ η, X.X (t k i) η ∂P))) P)
    (M : ℕ → Lp ℝ (2 : ℝ≥0∞) P)
    (hSource : ∀ k, (M k : Ω → ℝ) =ᵐ[P] fun ω =>
      ∑ i ∈ Finset.range (n k),
        W k i ω * (X.X (s k i + t k i) ω - X.X (s k i) ω -
          (∫ η, X.X (t k i) η ∂P)))
    (Cband : ℝ)
    (hBandBound : ∀ i j : ℕ, i ≤ j →
      dist (M i) (M j) ≤
        Cband * Real.sqrt ((∫⁻ z in Ioc (-(1 / ((i : ℝ) + 1))) (0 : ℝ),
          ENNReal.ofReal (z ^ 2) ∂X.ν).toReal)) :
    ∃ L : Lp ℝ (2 : ℝ≥0∞) P,
      Tendsto M Filter.atTop (𝓝 L) ∧
      (∫ ω, L ω ∂P) = 0 := by
  obtain ⟨L, hLim⟩ :=
    avram_f6_original_smallmark_Lp2_limit_from_physical_band_bound X
      (fun i (_ : ℝ≥0) => M i) Cband
      (by
        intro u i j hij
        exact hBandBound i j hij) (0 : ℝ≥0)
  have hc : CauchySeq M := hLim.cauchySeq
  exact avram_wave7_06_original_finite_grid_martingale_L2_limit_mean_zero
    X n s t W hWPast hWI hXI hCellI M hSource hc
