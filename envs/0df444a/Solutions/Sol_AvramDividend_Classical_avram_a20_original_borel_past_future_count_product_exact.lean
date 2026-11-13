-- Prove2me | solution 1 for AvramDividend.Classical.avram_a20_original_borel_past_future_count_product_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T12:28:09.789747+00:00
-- url     : https://prove2.me/submissions/15f74348-af51-4723-9665-b22abdc5f603

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_borel_past_count_raw_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_Ioc_st_future_past_factor
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_borel_marked_unconditional_levy_rate
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    (∫⁻ ω, NX ω (Ioc 0 s ×ˢ B) *
      NX ω (Ioc s t ×ˢ B) ∂P) =
      ((s : ℝ≥0∞) * X.ν B) *
        (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B) := by
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  change (∫⁻ ω, NX ω (Ioc 0 s ×ˢ B) *
    NX ω (Ioc s t ×ˢ B) ∂P) =
    ((s : ℝ≥0∞) * X.ν B) *
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B)
  have hPast :
      Measurable[𝓕 s] (fun ω => NX ω (Ioc 0 s ×ˢ B)) := by
    simpa only [NX] using
      (avram_a20_original_borel_past_count_raw_measurable X s B hB)
  have hFactor :
      (∫⁻ ω, NX ω (Ioc 0 s ×ˢ B) * NX ω (Ioc s t ×ˢ B) ∂P) =
      (∫⁻ ω, NX ω (Ioc 0 s ×ˢ B) ∂P) *
      (∫⁻ ω, NX ω (Ioc s t ×ˢ B) ∂P) := by
    simpa only [NX] using
      (avram_p2_f_weighted_original_intrinsic_Ioc_st_future_past_factor
        X s t hst B hB (fun ω => NX ω (Ioc 0 s ×ˢ B)) hPast)
  have hPastRate :
      (∫⁻ ω, NX ω (Ioc 0 s ×ˢ B) ∂P) =
      (s : ℝ≥0∞) * X.ν B := by
    simpa only [NX, tsub_zero] using
      (avram_wave7_01_original_intrinsic_borel_marked_unconditional_levy_rate
        X 0 s (show (0 : ℝ≥0) ≤ s from zero_le) B hB)
  have hFutureRate :
      (∫⁻ ω, NX ω (Ioc s t ×ˢ B) ∂P) =
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B) := by
    simpa only [NX] using
      (avram_wave7_01_original_intrinsic_borel_marked_unconditional_levy_rate
        X s t hst B hB)
  rw [hFactor, hPastRate, hFutureRate]
