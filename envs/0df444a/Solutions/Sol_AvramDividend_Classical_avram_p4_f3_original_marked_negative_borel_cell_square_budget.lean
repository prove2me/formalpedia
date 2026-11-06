-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_marked_negative_borel_cell_square_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T11:51:27.657176+00:00
-- url     : https://prove2.me/submissions/bb27384e-0d62-4cfc-96ed-61278c7fb400

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_bounded_stop_negative_band_square_budget
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_marked_negative_borel_cell_dominated_by_full_band
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original marked negative Borel cell has a physical full-band L² envelope. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ)
    (s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T)
    (B : Set ℝ) (hBsep : B ⊆ Iic (-(1 / ((n : ℝ) + 1))))
    (A : Ω → ℝ)
    (hAeq : ∀ ω, A ω =
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal)
    (hAmeas : Measurable A)
    (hKmeas : Measurable (fun ω : Ω =>
      {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard)) :
    let r : ℝ :=
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    Integrable (fun ω => (A ω) ^ 2) P ∧
      (∫ ω, (A ω) ^ 2 ∂P) ≤ r ^ 2 + r := by
  let K : Ω → ℕ := fun ω =>
    {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))}.ncard
  let r : ℝ :=
    ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
  change Integrable (fun ω => (A ω) ^ 2) P ∧
    (∫ ω, (A ω) ^ 2 ∂P) ≤ r ^ 2 + r
  have hCount := avram_p4_s3_original_bounded_stop_negative_band_square_budget
    X T n (fun _ => T) (by intro ω; rfl) hKmeas
  change Integrable (fun ω => (K ω : ℝ) ^ 2) P ∧
    (∫ ω, (K ω : ℝ) ^ 2 ∂P) ≤ r ^ 2 + r at hCount
  have hDom := avram_p4_s3_original_marked_negative_borel_cell_dominated_by_full_band
    X T n s t hst htT B hBsep
  have hPointwise (ω : Ω) : (A ω) ^ 2 ≤ (K ω : ℝ) ^ 2 := by
    have hBound : A ω ≤ (K ω : ℝ) := by
      rw [hAeq ω]
      exact hDom ω
    have hApos : 0 ≤ A ω := by
      rw [hAeq ω]
      exact ENNReal.toReal_nonneg
    have hKpos : 0 ≤ (K ω : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hA2meas : Measurable (fun ω => (A ω) ^ 2) :=
    hAmeas.pow_const 2
  have hA2 : Integrable (fun ω => (A ω) ^ 2) P := by
    apply Integrable.mono hCount.1 hA2meas.aestronglyMeasurable
    filter_upwards [] with ω
    change ‖(A ω) ^ 2‖ ≤ ‖(K ω : ℝ) ^ 2‖
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hPointwise ω
  refine ⟨hA2, ?_⟩
  exact le_trans
    (integral_mono_ae hA2 hCount.1 (Filter.Eventually.of_forall hPointwise))
    hCount.2
