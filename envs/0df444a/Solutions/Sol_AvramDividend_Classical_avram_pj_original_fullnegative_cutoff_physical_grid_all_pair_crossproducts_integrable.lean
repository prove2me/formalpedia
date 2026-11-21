-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_original_fullnegative_cutoff_physical_grid_all_pair_crossproducts_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T10:21:12.524256+00:00
-- url     : https://prove2.me/submissions/dc9be330-9705-41dc-87a7-f51dd959046e

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_full_cutoff_bounded_weight_physical_L2_auto
import Theorems.Thm_AvramDividend_Classical_avram_pj_original_marked_grid_L2_each_cell_implies_all_cross_products_integrable
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original genuine full negative-cutoff finite-grid compensated
increments are pairwise integrable under bounded past-predictable weights. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (m cut : ℕ) (Δ : ℝ≥0) (grid : ℕ → ℝ≥0)
    (hStep : ∀ j, grid (j + 1) = grid j + Δ)
    (H : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[𝓕.rightCont (grid i)] (H i))
    (L : ℝ) (hBound : ∀ i ω, |H i ω| ≤ L) :
    let N : ℕ → Ω → ℝ≥0∞ := fun j ω =>
      ((Measure.count.restrict {t : ℝ≥0 |
        0 < t ∧ X.X t ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) t ≠ 0}).map
        (fun t : ℝ≥0 => (t,
          X.X t ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) t)))
        (Ioc (grid j) (grid (j + 1)) ×ˢ
          Iic (-(1 / ((cut : ℝ) + 1))))
    let r : ℝ :=
      ((Δ : ℝ≥0∞) *
        X.ν (Iic (-(1 / ((cut : ℝ) + 1))))).toReal
    let Z : ℕ → Ω → ℝ := fun i ω =>
      H i ω * ((N i ω).toReal - r)
    ∀ i ∈ Finset.range m, ∀ j ∈ Finset.range m,
      Integrable (fun ω => Z i ω * Z j ω) P := by
  intro N r Z
  have hL2 (i : ℕ) : MemLp (Z i) 2 P := by
    have hs :=
      avram_p4_s3_interval_h_original_full_cutoff_bounded_weight_physical_L2_auto
        X (grid i) Δ cut (H i) (hH i) L (hBound i)
    simpa only [Z, N, r, hStep i] using hs
  exact avram_pj_original_marked_grid_L2_each_cell_implies_all_cross_products_integrable
    P (Finset.range m) Z (fun i hi => hL2 i)
