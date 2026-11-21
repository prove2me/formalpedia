-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_original_stopped_fullnegative_marked_grid_fullsum_uniform_L1_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T16:23:53.678642+00:00
-- url     : https://prove2.me/submissions/bb31e070-88f5-4550-916b-f9a16129bb86

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_pj_original_fullnegative_stopped_clipped_physical_grid_Z_measurable
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_each_stopped_clipped_physical_marked_cell_MemLp2
import Theorems.Thm_AvramDividend_Classical_avram_pj_original_marked_grid_L2_each_cell_implies_all_cross_products_integrable
import Theorems.Thm_AvramDividend_Classical_avram_pj_original_fullnegative_stopped_clipped_physical_grid_martingale_uniform_L2_no_extra_hypotheses
import Theorems.Thm_AvramDividend_Classical_avram_pj_original_physical_fullmark_grid_cross_integrable_L2_budget_gives_L1
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q K : ℝ) (hK : 0 ≤ K)
    (cut : ℕ) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (n m : ℕ) (hn : 0 < n) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let grid : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let N : ℕ → Ω → ℝ≥0∞ := fun i ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (grid i) (grid (i + 1)) ×ˢ Iic (-(1 / ((cut : ℝ) + 1))))
    let r : ℕ → ℝ := fun i =>
      (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
        X.ν (Iic (-(1 / ((cut : ℝ) + 1))))).toReal
    let H : ℕ → Ω → ℝ := fun i ω =>
      max (-K) (min K (Real.exp (-(q * (grid i : ℝ))) *
        deriv w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω)
          (grid i))))
    let Z : ℕ → Ω → ℝ := fun i ω =>
      (if (ρ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
        then (0 : ℝ) else H i ω) * ((N i ω).toReal - r i)
    (∫ ω, |∑ i ∈ Finset.range m, Z i ω| ∂P) ≤
      Real.sqrt (K^2 * ((n : ℝ) *
        (X.ν (Iic (-(1 / ((cut : ℝ) + 1))))).toReal)) := by
  intro Δ grid N r H Z
  have hZmeas : ∀ i ∈ Finset.range m, Measurable (Z i) := by
    intro i hi
    exact avram_pj_original_fullnegative_stopped_clipped_physical_grid_Z_measurable
      X x D hD w q K hK cut ρ hρstop n m hn i
  have hPair : ∀ i ∈ Finset.range m, ∀ j ∈ Finset.range m,
      Integrable (fun ω => Z i ω * Z j ω) P :=
    avram_pj_original_marked_grid_L2_each_cell_implies_all_cross_products_integrable
      P (Finset.range m) Z (by
        intro i hi
        exact avram_pj_workerC_original_each_stopped_clipped_physical_marked_cell_MemLp2
          X x D hD w q K hK cut ρ hρstop n m hn i)
  have hBudget :=
    avram_pj_original_fullnegative_stopped_clipped_physical_grid_martingale_uniform_L2_no_extra_hypotheses
      X x D hD w q K hK cut ρ hρstop n m hn
  exact avram_pj_original_physical_fullmark_grid_cross_integrable_L2_budget_gives_L1
    P m Z hZmeas hPair
    (K^2 * ((n : ℝ) *
      (X.ν (Iic (-(1 / ((cut : ℝ) + 1))))).toReal)) hBudget
