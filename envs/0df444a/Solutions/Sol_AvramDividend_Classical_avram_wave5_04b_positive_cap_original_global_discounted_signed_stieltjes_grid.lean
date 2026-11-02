-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04b_positive_cap_original_global_discounted_signed_stieltjes_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:53:45.668237+00:00
-- url     : https://prove2.me/submissions/5ecfabfd-71f5-4eee-b429-04c87d678ba5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_cap_original_discounted_full_stieltjes_cell_domination
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_cap_original_global_closed_stieltjes_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_closed_horizon_stieltjes_grid_partition_exact

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Any positive ENNReal cap: the complete original discounted dividend Stieltjes measure on a closed pre-ruin horizon is bounded by the exact time-zero atom value drop and chronological left-discount weighted source-frozen value drops. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (q : ℝ) (hq : 0 ≤ q) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
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
  have hAtom := avram_wave5_04b_positive_cap_original_global_closed_stieltjes_budget
    X x C hC q hq w V hw_cont hw_smooth hw_grad hVtop hVfinite
    D hD ω 0 (Or.inl rfl)
  have hZero :
      (∫⁻ s in ({0} : Set ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
        ENNReal.ofReal
          (V (x + X.X 0 ω) -
            V (x + X.X 0 ω - rightLimit D 0 ω)) := by
    simpa using hAtom
  rw [hPartition]
  apply add_le_add hZero
  apply Finset.sum_le_sum
  intro i hi
  exact avram_wave5_04b_positive_cap_original_discounted_full_stieltjes_cell_domination
    X x C hC q hq w V hw_cont hw_smooth hw_grad hVtop hVfinite
    D hD ω (u i) (u (i + 1)) (hu (Nat.le_succ i))
    (hPre i (Finset.mem_range.mp hi))
