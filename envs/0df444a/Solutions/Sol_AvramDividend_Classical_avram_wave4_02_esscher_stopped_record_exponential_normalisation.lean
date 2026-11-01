-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_02_esscher_stopped_record_exponential_normalisation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T10:22:40.629373+00:00
-- url     : https://prove2.me/submissions/63e13a72-2634-41c7-b003-b7c91769b11e

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_exponential_hazard
import Theorems.Thm_AvramDividend_Classical_avram_wave4_02_source_esscher_record_height_rate_nonneg_continuous
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The genuine stopped first-record Esscher weight is an exact exponential
in record height, positive and at most one at every positive killing depth. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (a h : ℝ) (ha : 0 < a) (hh : 0 < h) :
    let G := Real.exp (φ * h) *
      (∫⁻ ω, if twoSidedExitUpTime X h ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
      else 0 ∂P).toReal
    let rate := -Real.log ((∫⁻ ω, if twoSidedExitUpTime X 1 ω <
        barrierRuinTime X a ω then
        ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
      else 0 ∂P).toReal) - φ
    0 < G ∧ G = Real.exp (-(h * rate)) ∧ G ≤ 1 := by
  let F : ℝ → ℝ≥0∞ := fun j =>
    ∫⁻ ω, if twoSidedExitUpTime X j ω < barrierRuinTime X a ω then
      ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X j ω).toReal)))
    else 0 ∂P
  let G : ℝ := Real.exp (φ * h) * (F h).toReal
  let rate : ℝ := -Real.log ((F 1).toReal) - φ
  change 0 < G ∧ G = Real.exp (-(h * rate)) ∧ G ≤ 1
  have hrecord : (F h).toReal =
      Real.exp (-h * (-Real.log ((F 1).toReal))) :=
    avram_wave4_01_original_record_exponential_hazard
      X q hq W hW hvar a ha h hh
  have hrate : 0 ≤ rate :=
    (avram_wave4_02_source_esscher_record_height_rate_nonneg_continuous
      X q hq W hW hvar φ hφ hroot).2 a ha
  have hG : G = Real.exp (-(h * rate)) := by
    dsimp only [G, rate]
    rw [hrecord, ← Real.exp_add]
    congr 1
    ring
  have hGle : Real.exp (-(h * rate)) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr
      (neg_nonpos.mpr (mul_nonneg hh.le hrate))
  exact ⟨by rw [hG]; exact Real.exp_pos _,
    hG, by rw [hG]; exact hGle⟩
