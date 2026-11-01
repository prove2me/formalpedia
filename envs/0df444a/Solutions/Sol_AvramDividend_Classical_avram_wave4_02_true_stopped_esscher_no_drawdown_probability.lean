-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_02_true_stopped_esscher_no_drawdown_probability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T01:13:15.869272+00:00
-- url     : https://prove2.me/submissions/46c80aad-0ce2-4cf0-9d25-95b2d3ccfbea

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_02_esscher_stopped_record_exponential_normalisation
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_measurable
import Theorems.Thm_AvramDividend_Classical_chat08_upper_passage_clock_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Actual source stopped-Esscher probability of surviving the real
    reflected drawdown until the first local-time level h. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (a h : ℝ) (ha : 0 < a) (hh : 0 < h) :
    let τ := twoSidedExitUpTime X h
    let D := barrierRuinTime X a
    let Q := P.withDensity (fun ω : Ω =>
      if τ ω < (⊤ : ℝ≥0∞)
      then ENNReal.ofReal (Real.exp (φ * h - q * (τ ω).toReal))
      else 0)
    let rate := -Real.log ((∫⁻ ω, if twoSidedExitUpTime X 1 ω <
        barrierRuinTime X a ω then
        ENNReal.ofReal
          (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
      else 0 ∂P).toReal) - φ
    Q {ω : Ω | τ ω < D ω} =
      ENNReal.ofReal (Real.exp (-(h * rate))) := by
  let τ := twoSidedExitUpTime X h
  let D := barrierRuinTime X a
  let E : Set Ω := {ω | τ ω < D ω}
  let F : ℝ≥0∞ := ∫⁻ ω,
    if τ ω < D ω then ENNReal.ofReal (Real.exp (-(q * (τ ω).toReal)))
    else 0 ∂P
  let rate : ℝ := -Real.log ((∫⁻ ω, if twoSidedExitUpTime X 1 ω <
    barrierRuinTime X a ω then
    ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
    else 0 ∂P).toReal) - φ
  let c : ℝ≥0∞ := ENNReal.ofReal (Real.exp (φ * h))
  let f : Ω → ℝ≥0∞ := fun ω =>
    if τ ω < D ω then ENNReal.ofReal (Real.exp (-(q * (τ ω).toReal)))
    else 0
  let g : Ω → ℝ≥0∞ := fun ω =>
    if τ ω < (⊤ : ℝ≥0∞)
    then ENNReal.ofReal (Real.exp (φ * h - q * (τ ω).toReal))
    else 0
  have hE : MeasurableSet E :=
    measurableSet_lt (chat08_upper_passage_clock_measurable X h)
      (barrierRuinTime_measurable X a)
  have hpoint (ω : Ω) : (if ω ∈ E then g ω else 0) = c * f ω := by
    by_cases he : ω ∈ E
    · have he' : τ ω < D ω := he
      have ht : τ ω < (⊤ : ℝ≥0∞) :=
        lt_of_lt_of_le he' le_top
      simp only [g, f, c, if_pos he, if_pos he', if_pos ht]
      rw [← ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _))]
      congr 1
      rw [← Real.exp_add]
      congr 1
    · have he' : ¬ τ ω < D ω := he
      simp [f, E, he']
  have hSrc :=
    avram_wave4_02_esscher_stopped_record_exponential_normalisation
      X q hq W hW hvar φ hφ hroot a h ha hh
  have hGpos : 0 < Real.exp (φ * h) * F.toReal := hSrc.1
  have hG :
      Real.exp (φ * h) * F.toReal = Real.exp (-(h * rate)) := hSrc.2.1
  have hFfin : F ≠ ⊤ := by
    intro ht
    have hhpos := hGpos
    simp [ht] at hhpos
  have hmass : c * F =
      ENNReal.ofReal (Real.exp (-(h * rate))) := by
    dsimp only [c]
    rw [← ENNReal.ofReal_toReal hFfin]
    rw [← ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _))]
    exact congrArg ENNReal.ofReal hG
  change (P.withDensity g) E =
    ENNReal.ofReal (Real.exp (-(h * rate)))
  calc
    (P.withDensity g) E = (∫⁻ ω in E, g ω ∂P) := by
      exact withDensity_apply _ hE
    _ = (∫⁻ ω, if ω ∈ E then g ω else 0 ∂P) := by
      rw [← lintegral_indicator hE]
      apply lintegral_congr
      intro ω
      by_cases he : ω ∈ E <;> simp [Set.indicator, he]
    _ = (∫⁻ ω, c * f ω ∂P) := by
      apply lintegral_congr
      exact hpoint
    _ = c * (∫⁻ ω, f ω ∂P) := by
      rw [lintegral_const_mul' _ _ (by simp [c])]
    _ = ENNReal.ofReal (Real.exp (-(h * rate))) := by
      change c * F = _
      exact hmass
