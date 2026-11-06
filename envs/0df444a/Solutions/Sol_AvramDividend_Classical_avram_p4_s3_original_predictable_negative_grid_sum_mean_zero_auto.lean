-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_original_predictable_negative_grid_sum_mean_zero_auto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T10:46:04.696311+00:00
-- url     : https://prove2.me/submissions/9bb883a3-5e2f-4388-8e5e-1ac6fb0b7d73

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_separated_marked_future_past_rectangle_L1_rate
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_separated_borel_nu_finite
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_intrinsic_general_time_mark_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_negative_borel_cell_centred_L2_from_full_band
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_raw_finite_grid_zero_mean
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Physical predictable finite-grid jump sums are integrable and centred. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (cut : ℕ)
    (grid : ℕ → ℝ≥0) (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (hBound : ∀ i, grid i ≤ T)
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
    (n : ℕ) :
    Integrable (fun ω =>
      ∑ i ∈ Finset.range n, H i ω *
        ((N i ω).toReal -
          (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
            X.ν (C i)).toReal)) P ∧
    (∫ ω, (∑ i ∈ Finset.range n, H i ω *
      ((N i ω).toReal -
        (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
          X.ν (C i)).toReal)) ∂P) = 0 := by
  have hν (i : ℕ) : X.ν (C i) < ⊤ := by
    apply avram_p2_a_zero_rate_separated_borel_nu_finite
      X (C i) (hC i) ε hε
    intro z hz
    exact (hBand i hz).2.le
  have hMeas (i : ℕ) : Measurable (N i) := by
    rw [hActual i]
    exact avram_p2_d_future_intrinsic_general_time_mark_measurable
      X (Ioc (grid i) (grid (i + 1)) ×ˢ C i)
        (measurableSet_Ioc.prod (hC i))
  have hRect : ∀ (i : ℕ) (A : Set Ω),
      MeasurableSet[𝓕 (grid i)] A →
        (∫⁻ ω in A, N i ω ∂P) =
          P A * ((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
            X.ν (C i) := by
    intro i A hA
    rw [hActual i]
    have hSep : C i ⊆ Iic (-ε) := by
      intro z hz
      exact (hBand i hz).2.le
    have h := avram_wave7_06_original_separated_marked_future_past_rectangle_L1_rate
      X (grid i) (grid (i + 1) - grid i) A hA (C i) (hC i)
        ε hε hSep
    have hs : grid i + (grid (i + 1) - grid i) = grid (i + 1) := by
      simpa only [add_comm] using (tsub_add_cancel_of_le (hGrid i))
    simpa only [hs, mul_assoc] using h
  have hCountL2 (i : ℕ) : MemLp (fun ω =>
      (N i ω).toReal -
        (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
          X.ν (C i)).toReal) 2 P := by
    rw [hActual i]
    exact avram_p4_s3_original_negative_borel_cell_centred_L2_from_full_band
      X T cut (grid i) (grid (i + 1)) (hGrid i) (hBound (i + 1))
        (C i) (hC i) (hCut i)
  exact avram_p4_g_isometry_original_raw_finite_grid_zero_mean
    X grid hGrid ε hε C hC hBand hν N hActual hMeas hRect
      H hH hHL2 hCountL2 n
