-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_original_record_discount_depth_tendsto_unrestricted_root
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T14:53:17.108886+00:00
-- url     : https://prove2.me/submissions/dc51d4cd-2b4a-4163-9f54-e24169e24aed

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_exponential_hazard
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_hazard_tendsto_esscher_root
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

/-- Real stopped first-record discount loses its drawdown killing at infinity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (h : ℝ) (hh : 0 < h) :
    Tendsto
      (fun a : ℝ =>
        (∫⁻ ω, if twoSidedExitUpTime X h ω <
                    barrierRuinTime X a ω then
            ENNReal.ofReal
              (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
          else 0 ∂P).toReal)
      atTop (nhds (Real.exp (-(h * φ)))) := by
  let K : ℝ → ℝ := fun a => -Real.log ((∫⁻ ω,
    if twoSidedExitUpTime X 1 ω < barrierRuinTime X a ω then
      ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
    else 0 ∂P).toReal)
  have hK : Tendsto K atTop (nhds φ) :=
    avram_wave4_01_original_record_hazard_tendsto_esscher_root
      X q hq W hW hvar φ hφ hroot
  have hmul : Tendsto (fun a : ℝ => (-h) * K a)
      atTop (nhds ((-h) * φ)) := tendsto_const_nhds.mul hK
  have hexp : Tendsto (fun a : ℝ => Real.exp (-h * K a))
      atTop (nhds (Real.exp (-(h * φ)))) := by
    simpa only [Function.comp_def, neg_mul] using
      (Real.continuous_exp.tendsto ((-h) * φ)).comp hmul
  have heq :
      (fun a : ℝ =>
        (∫⁻ ω, if twoSidedExitUpTime X h ω <
                    barrierRuinTime X a ω then
            ENNReal.ofReal
              (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
          else 0 ∂P).toReal) =ᶠ[atTop]
      (fun a : ℝ => Real.exp (-h * K a)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
    exact avram_wave4_01_original_record_exponential_hazard
      X q hq W hW hvar a ha h hh
  exact hexp.congr' heq.symm
