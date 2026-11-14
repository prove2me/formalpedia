-- Prove2me | solution 1 for AvramDividend.Classical.avram_a23_uniform_signed_negative_band_window_borel_20261113
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:28:11.726658+00:00
-- url     : https://prove2.me/submissions/d41efde0-3b0b-4b8c-97b1-daeff4fcdc70

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin14_original_negative_band_shift_integral_exact
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_generic_negative_mark_window_integral_formula
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_cadlag_mark_weight_lintegral_borel
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_shifted_future_increment_path_cadlag
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A single Borel future-path functional works for every original starting time at fixed horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (n : ℕ) (T : ℝ≥0) :
    ∃ J : (ℝ≥0 → ℝ) → ℝ, Measurable J ∧
      ∀ (s : ℝ≥0) (ω : Ω),
        let B : Set ℝ := Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))
        let μ : Measure (ℝ≥0 × ℝ) :=
          (Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u, X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
        (∫ p in (Ioc s (s + T) ×ˢ B), p.2 ∂μ) =
          J (fun u : ℝ≥0 => X.X (s + u) ω - X.X s ω) := by
  classical
  let B : Set ℝ := Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))
  let g : ℝ → ℝ≥0∞ := fun z =>
    if z ∈ B then ENNReal.ofReal (-z) else 0
  have hg : Measurable g := by
    dsimp [g, B]
    exact Measurable.ite measurableSet_Ioc (by fun_prop) measurable_const
  obtain ⟨V, hV, hVpath⟩ :=
    avram_bv_jump8_cadlag_mark_weight_lintegral_borel T g hg
  let J : (ℝ≥0 → ℝ) → ℝ := fun Y => -((V Y).toReal)
  refine ⟨J, (ENNReal.measurable_toReal.comp hV).neg, ?_⟩
  intro s ω
  let Y : ℝ≥0 → ℝ := fun u => X.X (s + u) ω - X.X s ω
  let μ : Measure (ℝ≥0 × ℝ) :=
    (Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ Y u - Function.leftLim Y u ≠ 0}).map
      (fun u : ℝ≥0 => (u, Y u - Function.leftLim Y u))
  have hNeg : ∀ z ∈ B, z ≤ 0 := by
    intro z hz
    have hn : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
    exact hz.2.trans (neg_nonpos.mpr hn)
  have hPath := avram_wave7_01_original_shifted_future_increment_path_cadlag
    X ω s
  have hVformula := hVpath Y hPath.1 hPath.2
  have hShift := avram_mix_fin14_original_negative_band_shift_integral_exact
    X ω s T B measurableSet_Ioc hNeg
  have hSign := avram_mix_gauss14_generic_negative_mark_window_integral_formula
    μ (0 : ℝ≥0) T B measurableSet_Ioc hNeg
  change _ = -((V Y).toReal)
  calc
    (∫ p in (Ioc s (s + T) ×ˢ B), p.2 ∂
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) =
      (∫ p in (Ioc 0 T ×ˢ B), p.2 ∂μ) := by
        simpa [μ, Y] using hShift.symm
    _ = -((V Y).toReal) := by
      rw [hSign, hVformula]
