-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_original_record_weighted_depth_difference_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T19:32:42.191059+00:00
-- url     : https://prove2.me/submissions/3109bd05-d383-4ebf-8fe4-ab5ef7ae4685

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_weighted_esscher_height_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Topology

/-- The L1 distance between any two actual stopped-record Esscher
spatial reward kernels is finite for every admissible real tilt. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (θ a b : ℝ) (hθ : -φ < θ) (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (fun h : ℝ =>
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
        else 0 ∂P).toReal)|) (Ioi 0) := by
  have hbi :=
    avram_wave4_01_original_record_weighted_esscher_height_integrable
      X q hq W hW hvar φ hφ hroot b θ hb hθ
  have hai :=
    avram_wave4_01_original_record_weighted_esscher_height_integrable
      X q hq W hW hvar φ hφ hroot a θ ha hθ
  exact (hbi.sub hai).abs
