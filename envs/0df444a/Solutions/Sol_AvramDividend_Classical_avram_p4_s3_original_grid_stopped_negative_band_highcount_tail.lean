-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_original_grid_stopped_negative_band_highcount_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T10:12:58.116101+00:00
-- url     : https://prove2.me/submissions/39850cbb-98ab-43ce-a285-3500c9e4d771

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_grid_selected_negative_band_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_grid_stopped_negative_band_square_budget

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original stopped band counts have a uniform quadratic probability tail. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ)
    (tick : Ω → ℕ) (htick : Measurable tick)
    (grid : ℕ → ℝ≥0) (hgrid : ∀ ω, grid (tick ω) ≤ T)
    (m : ℕ) (hm : 0 < m) :
    let K : Ω → ℕ := fun ω =>
      {u : ℝ≥0 | 0 < u ∧ u ≤ grid (tick ω) ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard
    let r : ℝ :=
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    P.real {ω : Ω | m ≤ K ω} ≤ (r ^ 2 + r) / (m : ℝ) ^ 2 := by
  let K : Ω → ℕ := fun ω =>
    {u : ℝ≥0 | 0 < u ∧ u ≤ grid (tick ω) ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))}.ncard
  let r : ℝ :=
    ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
  change P.real {ω : Ω | m ≤ K ω} ≤ (r ^ 2 + r) / (m : ℝ) ^ 2
  have hK : Measurable K :=
    avram_p4_s3_original_grid_selected_negative_band_count_measurable
      X n tick htick grid
  have hEvent : MeasurableSet {ω : Ω | m ≤ K ω} := by
    change MeasurableSet (K ⁻¹' Ici m)
    exact hK measurableSet_Ici
  have hMoment :=
    avram_p4_s3_original_grid_stopped_negative_band_square_budget
      X T n tick htick grid hgrid
  change Integrable (fun ω => (K ω : ℝ) ^ 2) P ∧
    (∫ ω, (K ω : ℝ) ^ 2 ∂P) ≤ r ^ 2 + r at hMoment
  have hmReal : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hmSq : (0 : ℝ) < (m : ℝ) ^ 2 := sq_pos_of_pos hmReal
  have hPoint (k : ℕ) :
      (if m ≤ k then (1 : ℝ) else 0) ≤
        (k : ℝ) ^ 2 / (m : ℝ) ^ 2 := by
    by_cases hk : m ≤ k
    · simp only [if_pos hk]
      have hle : (m : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have hprod : 0 ≤ ((k : ℝ) - (m : ℝ)) *
          ((k : ℝ) + (m : ℝ)) :=
        mul_nonneg (by linarith) (by linarith)
      apply (le_div_iff₀ hmSq).2
      nlinarith
    · simp only [if_neg hk]
      positivity
  have hIf :
      (fun ω : Ω => if m ≤ K ω then (1 : ℝ) else 0) =
      ({ω : Ω | m ≤ K ω}).indicator (fun _ => (1 : ℝ)) := by
    funext ω
    by_cases hk : m ≤ K ω <;> simp [Set.indicator, hk]
  have hIfInt : Integrable
      (fun ω : Ω => if m ≤ K ω then (1 : ℝ) else 0) P := by
    rw [hIf]
    exact (integrable_const (1 : ℝ)).indicator hEvent
  have hIfMean :
      (∫ ω, (if m ≤ K ω then (1 : ℝ) else 0) ∂P) =
        P.real {ω : Ω | m ≤ K ω} := by
    rw [hIf]
    exact integral_indicator_one hEvent
  have hBound :=
    integral_mono_ae hIfInt (hMoment.1.div_const ((m : ℝ) ^ 2))
      (Filter.Eventually.of_forall (fun ω => hPoint (K ω)))
  rw [hIfMean, integral_div] at hBound
  exact le_trans hBound
    ((div_le_div_iff_of_pos_right hmSq).2 hMoment.2)
