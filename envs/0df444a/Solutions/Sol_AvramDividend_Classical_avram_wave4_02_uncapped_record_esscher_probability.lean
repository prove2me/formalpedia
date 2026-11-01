-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_02_uncapped_record_esscher_probability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T01:06:34.23234+00:00
-- url     : https://prove2.me/submissions/1b1f9333-b8fb-4c86-96c6-151b7dfcde26

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_levy_positive_root_exact_strict_upcrossing_discount

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Genuine local-time-level Esscher likelihood stopped at the first positive record.
    No claim of a global tilted law or excursion Poisson compensation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (h : ℝ) (hh : 0 < h) :
    IsProbabilityMeasure
      (P.withDensity (fun ω : Ω =>
        if twoSidedExitUpTimeCorrected X h ω < (⊤ : ℝ≥0∞)
        then ENNReal.ofReal (Real.exp
          (φ * h - q * (twoSidedExitUpTimeCorrected X h ω).toReal))
        else 0)) := by
  let T : Ω → ℝ≥0∞ := twoSidedExitUpTimeCorrected X h
  let f : Ω → ℝ≥0∞ := fun ω =>
    if T ω < (⊤ : ℝ≥0∞)
    then ENNReal.ofReal (Real.exp (-(q * (T ω).toReal)))
    else 0
  let g : Ω → ℝ≥0∞ := fun ω =>
    if T ω < (⊤ : ℝ≥0∞)
    then ENNReal.ofReal (Real.exp (φ * h - q * (T ω).toReal))
    else 0
  have hfg : ∀ ω, g ω = ENNReal.ofReal (Real.exp (φ * h)) * f ω := by
    intro ω
    by_cases ht : T ω < (⊤ : ℝ≥0∞)
    · simp only [f, g, if_pos ht]
      rw [← ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _))]
      congr 1
      rw [← Real.exp_add]
      congr 1
    · simp [f, g, ht]
  have hf : (∫⁻ ω, f ω ∂P) =
      ENNReal.ofReal (Real.exp (-(φ * h))) := by
    exact levy_positive_root_exact_strict_upcrossing_discount
      X q hq φ hφ hroot h hh
  have hg : (∫⁻ ω, g ω ∂P) = 1 := by
    simp_rw [hfg]
    rw [lintegral_const_mul' _ _ (by simp)]
    rw [hf]
    rw [← ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _))]
    have he : Real.exp (φ * h) * Real.exp (-(φ * h)) = 1 := by
      rw [← Real.exp_add]
      simp
    simp [he]
  have hQ : (P.withDensity g) Set.univ = 1 := by
    rw [withDensity_apply _ MeasurableSet.univ]
    simpa using hg
  constructor
  simpa only [g, T] using hQ
