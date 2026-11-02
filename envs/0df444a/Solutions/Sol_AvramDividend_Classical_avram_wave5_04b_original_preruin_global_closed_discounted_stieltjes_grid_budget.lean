-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04b_original_preruin_global_closed_discounted_stieltjes_grid_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T11:07:59.467266+00:00
-- url     : https://prove2.me/submissions/68b25153-4b2e-4641-95c1-85043e0e7098

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_closed_horizon_stieltjes_grid_partition_exact
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_original_preruin_exact_discounted_all_cells_budget

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The exact full closed-horizon original-source dividend Stieltjes mass is bounded by chronological cap-linear drops. -/
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
    (hu : Monotone u) (hu0 : u 0 = 0)
    (hPre : ∀ i : ℕ, i < n →
      u (i + 1) = 0 ∨
        (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω)
    :
    (∫⁻ s in Icc (0 : ℝ) (u n : ℝ),
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
  have huReal : Monotone (fun i : ℕ => (u i : ℝ)) := by
    intro i j hij
    exact_mod_cast hu hij
  have h0Real : (u 0 : ℝ) = 0 := by
    exact_mod_cast hu0
  have hGrid : ∀ i : ℕ, i < n → u i ≤ u (i + 1) := by
    intro i hi
    exact hu (Nat.le_succ i)
  have hBudget := avram_wave5_04b_original_preruin_exact_discounted_all_cells_budget
    X x c hc q hq w hw_cont hw_smooth hw_grad D hD ω u n hGrid hPre
  have hPartition := avram_wave5_04b_closed_horizon_stieltjes_grid_partition_exact
    (dividendMeasure D ω)
    (fun s : ℝ => ENNReal.ofReal (Real.exp (-(q * s))))
    (fun i : ℕ => (u i : ℝ)) huReal h0Real n
  have hSingle : Icc (0 : ℝ) (0 : ℝ) = ({(0 : ℝ)} : Set ℝ) := by
    ext r
    simp
  rw [hSingle] at hBudget
  rw [hPartition]
  exact hBudget
