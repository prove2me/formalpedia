-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_original_record_weighted_esscher_pointwise_domination
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T19:13:49.085169+00:00
-- url     : https://prove2.me/submissions/75f782a6-f93e-4f51-8467-3fbe7fc55670

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_survival_uniform_esscher_envelope
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Topology

/-- The actual killed first-record density, after an arbitrary real
spatial Esscher weighting, has a nonnegative depth-uniform envelope. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (θ a h : ℝ) (ha : 0 < a) (hh : 0 < h) :
    0 ≤ Real.exp (-(θ * h)) *
      (∫⁻ ω, if twoSidedExitUpTime X h ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (Real.exp (-(q *
          (twoSidedExitUpTime X h ω).toReal)))
      else 0 ∂P).toReal ∧
    Real.exp (-(θ * h)) *
      (∫⁻ ω, if twoSidedExitUpTime X h ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (Real.exp (-(q *
          (twoSidedExitUpTime X h ω).toReal)))
      else 0 ∂P).toReal ≤
      Real.exp (-((θ + φ) * h)) := by
  have hbound :=
    avram_wave4_01_original_record_survival_uniform_esscher_envelope
      X q hq W hW hvar φ hφ hroot a h ha hh
  constructor
  · exact mul_nonneg (le_of_lt (Real.exp_pos _)) ENNReal.toReal_nonneg
  · calc
      Real.exp (-(θ * h)) *
          (∫⁻ ω, if twoSidedExitUpTime X h ω <
              barrierRuinTime X a ω then
            ENNReal.ofReal (Real.exp (-(q *
              (twoSidedExitUpTime X h ω).toReal)))
          else 0 ∂P).toReal
          ≤ Real.exp (-(θ * h)) * Real.exp (-(φ * h)) :=
            mul_le_mul_of_nonneg_left hbound (le_of_lt (Real.exp_pos _))
      _ = Real.exp (-((θ + φ) * h)) := by
        rw [← Real.exp_add]
        congr 1
        ring
