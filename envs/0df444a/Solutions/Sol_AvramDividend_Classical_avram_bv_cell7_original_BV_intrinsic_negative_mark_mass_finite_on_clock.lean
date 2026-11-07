-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_cell7_original_BV_intrinsic_negative_mark_mass_finite_on_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T18:57:19.71477+00:00
-- url     : https://prove2.me/submissions/c0ba9209-0639-4f29-bad7-c9b19517971c

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_negative_jump_tsum_lt_top
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_halfopen_physical_signed_jump_count_tsum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual original BV Lévy marked jump measure has finite negative
    mark magnitude on every bounded half-open physical clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (T : ℝ≥0),
      let Δ : ℝ≥0 → ℝ := fun u =>
        X.X u ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) u
      let NT : Measure (ℝ≥0 × ℝ) :=
        ((Measure.count.restrict
          ({u : ℝ≥0 | 0 < u ∧ Δ u ≠ 0} ∩ Ioc 0 T)).map
            (fun u : ℝ≥0 => (u, Δ u)))
      (∫⁻ p, ENNReal.ofReal (-p.2) ∂NT) < ⊤ := by
  filter_upwards
    [AvramDividend.Classical.avram_p3_a_bvdrift_original_interval_negative_jump_tsum_lt_top
      X hBV] with ω hω
  intro T
  let Δ : ℝ≥0 → ℝ := fun u =>
    X.X u ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) u
  let NT : Measure (ℝ≥0 × ℝ) :=
    ((Measure.count.restrict
      ({u : ℝ≥0 | 0 < u ∧ Δ u ≠ 0} ∩ Ioc 0 T)).map
        (fun u : ℝ≥0 => (u, Δ u)))
  have hCount : (∫⁻ p, ENNReal.ofReal (-p.2) ∂NT) =
      ∑' u : ℝ≥0,
        if (0 < u ∧ Δ u ≠ 0) ∧ u ∈ Ioc 0 T then
          ENNReal.ofReal (-Δ u) else 0 := by
    simpa only [NT, Δ] using
      (AvramDividend.Classical.avram_p3_2_original_halfopen_physical_signed_jump_count_tsum
        X ω 0 T (fun p : ℝ≥0 × ℝ => -p.2) measurable_snd.neg).1
  have hTerms :
      (∑' u : ℝ≥0,
        if (0 < u ∧ Δ u ≠ 0) ∧ u ∈ Ioc 0 T then
          ENNReal.ofReal (-Δ u) else 0) =
      ∑' u : ℝ≥0,
        if 0 < u ∧ u ≤ T then ENNReal.ofReal (-Δ u) else 0 := by
    apply tsum_congr
    intro u
    by_cases hu0 : 0 < u
    · by_cases huT : u ≤ T
      · by_cases hΔ : Δ u = 0
        · simp [hu0, huT, hΔ, Set.mem_Ioc]
        · simp [hu0, huT, hΔ, Set.mem_Ioc]
      · simp [hu0, huT, Set.mem_Ioc]
    · simp [hu0, Set.mem_Ioc]
  change (∫⁻ p, ENNReal.ofReal (-p.2) ∂NT) < ⊤
  rw [hCount, hTerms]
  simpa only [Δ, neg_sub] using (hω 0 T (show 0 ≤ T from zero_le))
