-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_original_physical_bounded_predictable_grid_L2_mean_zero_auto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:21:15.555582+00:00
-- url     : https://prove2.me/submissions/2f9ac808-3ba7-4908-a9cd-cb6acc3d9238

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_predictable_negative_grid_sum_mean_zero_auto
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_negative_borel_cell_centred_L2_from_full_band

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The genuine original bounded predictable finite-grid compensated sum lies in L². -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (cut : ℕ)
    (grid : ℕ → ℝ≥0) (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (hTime : ∀ i, grid i ≤ T)
    (ε : ℝ) (hε : 0 < ε) (C : ℕ → Set ℝ)
    (hC : ∀ i, MeasurableSet (C i))
    (hBand : ∀ i, C i ⊆ Ioo (-1 : ℝ) (-ε))
    (hCut : ∀ i, C i ⊆ Iic (-(1 / ((cut : ℝ) + 1))))
    (N : ℕ → Ω → ℝ≥0∞)
    (hActual : ∀ i, N i = fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (grid i) (grid (i + 1)) ×ˢ C i))
    (H : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[𝓕 (grid i)] (H i))
    (hHL2 : ∀ i, MemLp (H i) 2 P)
    (L : ℝ) (hL : ∀ i ω, |H i ω| ≤ L)
    (n : ℕ) :
    MemLp (fun ω =>
      ∑ i ∈ Finset.range n, H i ω *
        ((N i ω).toReal -
          (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
            X.ν (C i)).toReal)) 2 P ∧
    (∫ ω, (∑ i ∈ Finset.range n, H i ω *
      ((N i ω).toReal -
        (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
          X.ν (C i)).toReal)) ∂P) = 0 := by
  have hEach (i : ℕ) : MemLp (fun ω =>
      H i ω * ((N i ω).toReal -
        (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
          X.ν (C i)).toReal)) 2 P := by
    have hCount : MemLp (fun ω =>
        (N i ω).toReal -
          (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
            X.ν (C i)).toReal) 2 P := by
      rw [hActual i]
      exact avram_p4_s3_original_negative_borel_cell_centred_L2_from_full_band
        X T cut (grid i) (grid (i + 1)) (hGrid i)
          (hTime (i + 1)) (C i) (hC i) (hCut i)
    have hHTop : MemLp (H i) ⊤ P :=
      MemLp.of_bound (hHL2 i).aestronglyMeasurable L
        (Filter.Eventually.of_forall (fun ω => by
          simpa only [Real.norm_eq_abs] using hL i ω))
    exact hCount.mul hHTop
  have hSum : MemLp (fun ω =>
      ∑ i ∈ Finset.range n, H i ω *
        ((N i ω).toReal -
          (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
            X.ν (C i)).toReal)) 2 P := by
    exact memLp_finset_sum (Finset.range n) (by
      intro i hi
      exact hEach i)
  exact ⟨hSum,
    (avram_p4_s3_original_predictable_negative_grid_sum_mean_zero_auto
      X T cut grid hGrid hTime ε hε C hC hBand hCut
        N hActual H hH hHL2 n).2⟩
