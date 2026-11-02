-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04b_original_preruin_global_closed_signed_stieltjes_correction_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T11:20:26.016794+00:00
-- url     : https://prove2.me/submissions/eb345bff-103f-49ea-9dac-2bf275c1e4b7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_original_preruin_global_closed_discounted_stieltjes_grid_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_closed_horizon_real_stieltjes_partition_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_original_preruin_complete_signed_discounted_grid_correction_nonpos

set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

set_option pp.explicit true

/-- True source-specific signed real Stieltjes control on the complete closed horizon including time zero. -/
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
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal +
    (V (x + X.X 0 ω - rightLimit D 0 ω) - V (x + X.X 0 ω)) +
    ∑ i ∈ Finset.range n,
      (V (x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω) -
        V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω)) ≤ 0 := by
  have hGrid : ∀ i : ℕ, i < n → u i ≤ u (i + 1) := by
    intro i hi; exact hu (Nat.le_succ i)
  have hBudget := avram_wave5_04b_original_preruin_global_closed_discounted_stieltjes_grid_budget
    X x c hc q hq w hw_cont hw_smooth hw_grad D hD ω u n hu hu0 hPre
  have hFinite :
      (∫⁻ s in Icc (0 : ℝ) (u n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ hBudget
    simp
  have huReal : Monotone (fun i : ℕ => (u i : ℝ)) := by
    intro i j hij; exact_mod_cast hu hij
  have hu0Real : (u 0 : ℝ) = 0 := by exact_mod_cast hu0
  have hPartition := avram_wave5_04b_closed_horizon_real_stieltjes_partition_finite
    (dividendMeasure D ω)
    (fun s : ℝ => ENNReal.ofReal (Real.exp (-(q * s))))
    (fun i : ℕ => (u i : ℝ)) huReal hu0Real n hFinite
  have hSingleton : Icc (0 : ℝ) (0 : ℝ) = ({0} : Set ℝ) := by
    ext s; simp
  rw [← hSingleton] at hPartition
  have hSigned := avram_wave5_04b_original_preruin_complete_signed_discounted_grid_correction_nonpos
    X x c hc q hq w V hw_cont hw_smooth hw_grad hV D hD ω u n hGrid hPre
  rw [hPartition]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hSigned ⊢
  linarith only [hSigned]
