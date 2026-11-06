-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_original_future_negative_borel_rectangle_all_cells
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T10:03:29.105541+00:00
-- url     : https://prove2.me/submissions/baef9a0e-33ec-49b7-bc82-7851885f7d77

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_separated_marked_future_past_rectangle_L1_rate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The physical negative-band jump rate on each predictable past rectangle. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (B : Set ℝ) (hB : MeasurableSet B)
    (ε : ℝ) (hε : 0 < ε) (hBsep : B ⊆ Iic (-ε)) :
    ∀ (s t : ℝ≥0), s ≤ t →
      ∀ (A : Set Ω), MeasurableSet[𝓕 s] A →
        (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
            (Ioc s t ×ˢ B) ∂P) =
          P A * (((t - s : ℝ≥0) : ℝ≥0∞)) * X.ν B := by
  intro s t hst A hA
  have h := avram_wave7_06_original_separated_marked_future_past_rectangle_L1_rate
    X s (t - s) A hA B hB ε hε hBsep
  have hs : s + (t - s) = t := by
    simpa only [add_comm] using (tsub_add_cancel_of_le hst)
  simpa only [hs, mul_assoc] using h
