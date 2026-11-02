-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04b_original_preruin_complete_signed_discounted_grid_correction_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T11:07:55.727203+00:00
-- url     : https://prove2.me/submissions/48cc6bed-0276-40e2-bcdd-c59836b0f43a

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_original_time_zero_signed_atom_control_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_original_preruin_interval_signed_stieltjes_control_nonpos

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The original source's complete signed real Stieltjes correction, including time zero and full grid cells. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x c : ℝ) (hc : 0 < c) (q : ℝ) (hq : 0 ≤ q)
    (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < ENNReal.ofReal c})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < ENNReal.ofReal c → 1 ≤ deriv w z)
    (hV : ∀ z : ℝ, V z = if z ≤ c then w z else w c + (z - c))
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (ω : Ω) (u : ℕ → ℝ≥0) (n : ℕ)
    (hgrid : ∀ i : ℕ, i < n → u i ≤ u (i + 1))
    (hPre : ∀ i : ℕ, i < n →
      u (i + 1) = 0 ∨
        (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω) :
    ((∫⁻ s in Icc (0 : ℝ) (0 : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal +
      V (x + X.X 0 ω - rightLimit D 0 ω) -
      V (x + X.X 0 ω)) +
    ∑ i ∈ Finset.range n,
      ((∫⁻ s in Ioc (u i : ℝ) (u (i + 1) : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal +
        V (x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω) -
        V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω)) ≤ 0 := by
  have hZero := avram_wave5_04b_original_time_zero_signed_atom_control_nonpos
    X x c hc q hq w V hw_cont hw_smooth hw_grad hV D hD ω
  have hCells :
      (∑ i ∈ Finset.range n,
        ((∫⁻ s in Ioc (u i : ℝ) (u (i + 1) : ℝ),
            ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal +
          V (x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω) -
          V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω))) ≤ 0 := by
    calc
      _ ≤ ∑ i ∈ Finset.range n, (0 : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        have hii : i < n := Finset.mem_range.mp hi
        exact avram_wave5_04b_original_preruin_interval_signed_stieltjes_control_nonpos
          X x c hc q hq w V hw_cont hw_smooth hw_grad hV
          D hD ω (u i) (u (i + 1)) (hgrid i hii) (hPre i hii)
      _ = 0 := by simp
  linarith only [hZero, hCells]
