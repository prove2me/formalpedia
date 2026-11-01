-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_original_record_weighted_depth_difference_esscher_dominated
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T19:28:13.613988+00:00
-- url     : https://prove2.me/submissions/469869d0-0e60-4eb3-b1fc-ac538bfe90b0

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_weighted_esscher_pointwise_domination
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Topology

/-- A single depth-uniform Esscher envelope dominates the absolute
difference of any two genuine killed first-record spatial rewards. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (θ a b h : ℝ) (ha : 0 < a) (hb : 0 < b) (hh : 0 < h) :
    |(Real.exp (-(θ * h)) *
      (∫⁻ ω, if twoSidedExitUpTime X h ω <
          barrierRuinTime X b ω then
        ENNReal.ofReal (Real.exp (-(q *
          (twoSidedExitUpTime X h ω).toReal)))
      else 0 ∂P).toReal) - (Real.exp (-(θ * h)) *
      (∫⁻ ω, if twoSidedExitUpTime X h ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (Real.exp (-(q *
          (twoSidedExitUpTime X h ω).toReal)))
      else 0 ∂P).toReal)| ≤
      Real.exp (-((θ + φ) * h)) := by
  have hba :=
    avram_wave4_01_original_record_weighted_esscher_pointwise_domination
      X q hq W hW hvar φ hφ hroot θ b h hb hh
  have haa :=
    avram_wave4_01_original_record_weighted_esscher_pointwise_domination
      X q hq W hW hvar φ hφ hroot θ a h ha hh
  exact abs_sub_le_iff.mpr ⟨by linarith [hba.1, haa.2],
    by linarith [haa.1, hba.2]⟩
