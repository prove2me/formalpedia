-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04a_bv_actual_intrinsic_negative_jump_magnitude_integrable_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T11:46:56.196629+00:00
-- url     : https://prove2.me/submissions/d163fb78-33cf-42a1-8e9e-5d67d0e0f282

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_lintegral_eq_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_total_source_jump_magnitudes_le_residual

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (T : ℝ≥0),
      (∫⁻ p,
        (if 0 < p.1 ∧ p.1 ≤ T then ENNReal.ofReal (-p.2) else 0) ∂
        ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) ≤
      ENNReal.ofReal ((T : ℝ) * X.drift - X.X T ω) := by
  filter_upwards
    [avram_wave4_04a_bv_actual_total_source_jump_magnitudes_le_residual X hBV]
    with ω hvariation
  intro T
  have hmeas :
      Measurable (fun p : ℝ≥0 × ℝ =>
        if 0 < p.1 ∧ p.1 ≤ T then ENNReal.ofReal (-p.2) else 0) := by
    apply Measurable.ite
      ((measurableSet_lt measurable_const measurable_fst).inter
        (measurableSet_le measurable_fst measurable_const))
    · exact ENNReal.measurable_ofReal.comp (measurable_snd.neg)
    · exact measurable_const
  rw [avram_wave4_04a_actual_intrinsic_lintegral_eq_jump_sum X ω
    (fun p : ℝ≥0 × ℝ =>
      if 0 < p.1 ∧ p.1 ≤ T then ENNReal.ofReal (-p.2) else 0) hmeas]
  calc
    (∑' u : ℝ≥0,
      if 0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 then
        (if 0 < u ∧ u ≤ T then
          ENNReal.ofReal (-(X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) else 0)
      else 0) =
      (∑' u : ℝ≥0,
        if 0 < u ∧ u ≤ T then
          ENNReal.ofReal (Function.leftLim
            (fun v : ℝ≥0 => X.X v ω) u - X.X u ω)
        else 0) := by
        apply tsum_congr
        intro u
        by_cases hpos : 0 < u
        · by_cases hT : u ≤ T
          · by_cases hmark :
                X.X u ω - Function.leftLim
                  (fun v : ℝ≥0 => X.X v ω) u = 0
            · have hzero : Function.leftLim
                  (fun v : ℝ≥0 => X.X v ω) u - X.X u ω = 0 := by
                linarith
              simp [hpos, hT, hmark, hzero]
            · simpa [hpos, hT, hmark, neg_sub]
          · simp [hpos, hT]
        · simp [hpos]
    _ ≤ _ := hvariation T
