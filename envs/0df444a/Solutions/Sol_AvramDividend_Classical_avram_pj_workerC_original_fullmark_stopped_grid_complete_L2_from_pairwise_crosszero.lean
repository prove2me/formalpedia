-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_original_fullmark_stopped_grid_complete_L2_from_pairwise_crosszero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T10:16:54.317661+00:00
-- url     : https://prove2.me/submissions/6460c9c2-81de-462a-a82b-2c114277914d

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_clipped_stopped_negative_mark_grid_L2_energy_unconditional
import Theorems.Thm_AvramDividend_Classical_avram_pj_original_marked_grid_pairwise_L2_orthogonality_yields_full_sum_energy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_each_stopped_clipped_physical_marked_cell_MemLp2
import Theorems.Thm_AvramDividend_Classical_avram_pj_original_marked_grid_L2_each_cell_implies_all_cross_products_integrable
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
    (∀ i ∈ Finset.range m, ∀ j ∈ Finset.range m, i ≠ j →
      (∫ ω, Z i ω * Z j ω ∂P) = 0) →
    (∫ ω, (∑ i ∈ Finset.range m, Z i ω)^2 ∂P) ≤
      K^2 * ((n : ℝ) *
        (X.ν (Iic (-(1 / ((cut : ℝ) + 1))))).toReal) := by
  intro Δ grid N r H Z hCross
  have hOne : ∀ i ∈ Finset.range m, MemLp (Z i) 2 P := by
    intro i hi
    exact avram_pj_workerC_original_each_stopped_clipped_physical_marked_cell_MemLp2
      X x D hD w q K hK cut ρ hρstop n m hn i
  have hPair : ∀ i ∈ Finset.range m, ∀ j ∈ Finset.range m,
      Integrable (fun ω => Z i ω * Z j ω) P :=
    avram_pj_original_marked_grid_L2_each_cell_implies_all_cross_products_integrable
      P (Finset.range m) Z hOne
  have hOrth :=
    avram_pj_original_marked_grid_pairwise_L2_orthogonality_yields_full_sum_energy
      P (Finset.range m) Z hPair hCross
  have hDiag :=
    avram_pj_workerC_original_clipped_stopped_negative_mark_grid_L2_energy_unconditional
      X x D hD w q K hK cut ρ hρstop n m hn
  have hSum : (∑ i ∈ Finset.range m, ∫ ω, (Z i ω)^2 ∂P) ≤
      K^2 * ((n : ℝ) *
        (X.ν (Iic (-(1 / ((cut : ℝ) + 1))))).toReal) := by
    rw [← integral_finset_sum]
    · exact hDiag
    · intro i hi
      simpa [pow_two] using hPair i hi i hi
  exact hOrth.le.trans hSum
