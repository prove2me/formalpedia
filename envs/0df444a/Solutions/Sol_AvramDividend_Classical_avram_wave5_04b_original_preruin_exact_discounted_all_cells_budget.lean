-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04b_original_preruin_exact_discounted_all_cells_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:47:17.267891+00:00
-- url     : https://prove2.me/submissions/9430a6a3-7ee2-4980-96a1-31b5b4228ddb

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_caplinear_interval_full_stieltjes_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_original_preruin_time_zero_dividend_atom_caplinear_bound
open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
/-- The complete original-source exponentially discounted dividend Stieltjes budget on a pre-ruin grid. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x c : ℝ) (hc : 0 < c) (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < ENNReal.ofReal c})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < ENNReal.ofReal c → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (ω : Ω) (u : ℕ → ℝ≥0) (n : ℕ)
    (hgrid : ∀ i : ℕ, i < n → u i ≤ u (i + 1))
    (hPre : ∀ i : ℕ, i < n →
      u (i + 1) = 0 ∨
        (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω)
    :
    (∫⁻ s in Icc (0 : ℝ) (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) +
    ∑ i ∈ Finset.range n,
      (∫⁻ s in Ioc (u i : ℝ) (u (i + 1) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
    ENNReal.ofReal (
      (if x + X.X 0 ω ≤ c then w (x + X.X 0 ω)
        else w c + (x + X.X 0 ω - c)) -
      (if x + X.X 0 ω - rightLimit D 0 ω ≤ c
        then w (x + X.X 0 ω - rightLimit D 0 ω)
        else w c + ((x + X.X 0 ω - rightLimit D 0 ω) - c))) +
    ∑ i ∈ Finset.range n,
      ENNReal.ofReal (
        (if x + X.X (u (i + 1)) ω - rightLimit D (u i) ω ≤ c
          then w (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω)
          else w c +
            ((x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) - c)) -
        (if x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω ≤ c
          then w (x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω)
          else w c +
            ((x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω) - c))) := by
  have hAdmissible : IsAdmissible X x D := hD.1
  have hStrategy : IsDividendStrategy 𝓕 D := hAdmissible.1
  have hZero := avram_wave5_04b_original_preruin_time_zero_dividend_atom_caplinear_bound
    X x c hc q hq w hw_cont hw_smooth hw_grad D hD ω
  apply add_le_add hZero
  apply Finset.sum_le_sum
  intro i hi
  have hii : i < n := Finset.mem_range.mp hi
  have hJump := hAdmissible.2 ω (u (i + 1)) (hPre i hii)
  have hCover : rightLimit D (u (i + 1)) ω ≤
      x + X.X (u (i + 1)) ω := by
    dsimp [riskProcess] at hJump
    linarith only [hJump]
  exact avram_wave5_04b_caplinear_interval_full_stieltjes_budget
    c hc q hq w hw_cont hw_smooth hw_grad D hStrategy ω
    (u i) (u (i + 1)) (hgrid i hii)
    (x + X.X (u (i + 1)) ω) hCover
