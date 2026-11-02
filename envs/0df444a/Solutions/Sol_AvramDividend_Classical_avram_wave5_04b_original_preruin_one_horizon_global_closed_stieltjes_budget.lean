-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04b_original_preruin_one_horizon_global_closed_stieltjes_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T11:15:52.916037+00:00
-- url     : https://prove2.me/submissions/bc5e36b1-0278-4feb-ac5a-952a3dfb16c7

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_original_preruin_global_closed_discounted_stieltjes_grid_budget

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The actual discounted complete dividend Stieltjes integral up to one time is bounded by the initial and terminal cap-linear drops. -/
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
    (ω : Ω) (t : ℝ≥0)
    (hPre : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    (∫⁻ s in Icc (0 : ℝ) (t : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
    ENNReal.ofReal (
      (if x + X.X 0 ω ≤ c then w (x + X.X 0 ω)
        else w c + (x + X.X 0 ω - c)) -
      (if x + X.X 0 ω - rightLimit D 0 ω ≤ c
        then w (x + X.X 0 ω - rightLimit D 0 ω)
        else w c + ((x + X.X 0 ω - rightLimit D 0 ω) - c))) +
    ENNReal.ofReal (
        (if x + X.X t ω - rightLimit D 0 ω ≤ c
          then w (x + X.X t ω - rightLimit D 0 ω)
          else w c + (x + X.X t ω - rightLimit D 0 ω - c)) -
        (if x + X.X t ω - rightLimit D t ω ≤ c
          then w (x + X.X t ω - rightLimit D t ω)
          else w c + (x + X.X t ω - rightLimit D t ω - c))) := by
  let u : ℕ → ℝ≥0 := fun k => if k = 0 then 0 else t
  have hu : Monotone u := by
    intro i j hij
    by_cases hi : i = 0
    · simp [u, hi]
    · have hj : j ≠ 0 := by omega
      simp [u, hi, hj]
  have hu0 : u 0 = 0 := by simp [u]
  have hPreGrid : ∀ i : ℕ, i < 1 →
      u (i + 1) = 0 ∨ (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω := by
    intro i hi
    have hi0 : i = 0 := by omega
    subst i
    simpa [u] using hPre
  have hMain := avram_wave5_04b_original_preruin_global_closed_discounted_stieltjes_grid_budget
    X x c hc q hq w hw_cont hw_smooth hw_grad D hD ω u 1 hu hu0 hPreGrid
  simpa [u] using hMain
