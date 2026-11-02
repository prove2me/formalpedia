-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04b_original_preruin_global_discounted_signed_cell_upper_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:48:06.12949+00:00
-- url     : https://prove2.me/submissions/d29b7e8d-917a-43ae-bcbf-baebe84f833a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_original_preruin_discounted_cell_left_weighted_signed_domination
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_closed_horizon_stieltjes_grid_partition_exact
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_original_preruin_time_zero_dividend_atom_caplinear_bound

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Exact full-horizon discounted dividend measure, including the time-zero atom, is bounded by the chronological left-weighted cap-linear value-drop upper sum with zero and cap contacts. -/
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
    (hu : Monotone u) (hu0 : u 0 = 0)
    (hPre : ∀ i : ℕ, i < n →
      u (i + 1) = 0 ∨
        (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω) :
    (∫⁻ s in Icc (0 : ℝ) (u n : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
      ENNReal.ofReal
        (V (x + X.X 0 ω) -
          V (x + X.X 0 ω - rightLimit D 0 ω)) +
      ∑ i ∈ Finset.range n,
        ENNReal.ofReal (Real.exp (-(q * (u i : ℝ)))) *
          ENNReal.ofReal
            (V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
              V (x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω)) := by
  have huReal : Monotone (fun k : ℕ => (u k : ℝ)) := by
    intro i j hij
    exact_mod_cast hu hij
  have huReal0 : (u 0 : ℝ) = 0 := by
    exact_mod_cast hu0
  have hPartition := avram_wave5_04b_closed_horizon_stieltjes_grid_partition_exact
    (dividendMeasure D ω)
    (fun s : ℝ => ENNReal.ofReal (Real.exp (-(q * s))))
    (fun k : ℕ => (u k : ℝ)) huReal huReal0 n
  have hAtom := avram_wave5_04b_original_preruin_time_zero_dividend_atom_caplinear_bound
    X x c hc q hq w hw_cont hw_smooth hw_grad D hD ω
  rw [←hV (x + X.X 0 ω),
      ←hV (x + X.X 0 ω - rightLimit D 0 ω)] at hAtom
  have hZero :
      (∫⁻ s in ({0} : Set ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
        ENNReal.ofReal
          (V (x + X.X 0 ω) -
            V (x + X.X 0 ω - rightLimit D 0 ω)) := by
    simpa only [Icc_self] using hAtom
  rw [hPartition]
  apply add_le_add hZero
  apply Finset.sum_le_sum
  intro i hi
  exact avram_wave5_04b_original_preruin_discounted_cell_left_weighted_signed_domination
    X x c hc q hq w V hw_cont hw_smooth hw_grad hV
    D hD ω (u i) (u (i + 1)) (hu (Nat.le_succ i))
    (hPre i (Finset.mem_range.mp hi))
