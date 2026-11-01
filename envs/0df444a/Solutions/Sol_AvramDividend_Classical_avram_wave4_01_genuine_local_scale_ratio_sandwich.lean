-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_genuine_local_scale_ratio_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T09:36:14.880579+00:00
-- url     : https://prove2.me/submissions/3ec7ef64-bcbe-4319-b873-de3542abd6d9

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_infinite_small_jump_not_bv
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_unbounded_genuine_record_scale_sandwich
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_original_record_discount_le_one
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_exponential_hazard

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Topology

/-- Genuine original-record scale-ratio sandwich in exponential real form. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂X.ν = ⊤)
    (F : ℝ → ℝ → ℝ≥0∞)
    (hF : ∀ a h : ℝ, F a h =
      ∫⁻ ω, if twoSidedExitUpTime X h ω < barrierRuinTime X a ω then
        ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
      else 0 ∂P)
    (κ : ℝ → ℝ) (hκ : ∀ a : ℝ, κ a = -Real.log ((F a 1).toReal)) :
    ∀ a b : ℝ, 0 < a → a < b → b - a < a →
      Real.exp (-(κ a * (b - a))) ≤ W a / W b ∧
      W a / W b ≤ Real.exp (-(κ b * (b - a))) := by
  have hnbv : ¬ X.BoundedVariation :=
    avram_wave3_01_infinite_small_jump_not_bv X hvar
  intro a b ha hab hsmall
  have hb : 0 < b := lt_trans ha hab
  have hh : 0 < b - a := sub_pos.mpr hab
  have hsmallb : b - a < b := by linarith
  have heqA : a + (b - a) = b := by ring
  have heqB : b - (b - a) = a := by ring
  have hUP : F a (b - a) ≤ ENNReal.ofReal (W a / W b) := by
    simpa only [hF, heqA] using
      (avram_wave3_01_unbounded_genuine_record_scale_sandwich
        X q hq W hW hnbv a (b - a) ha hh hsmall).2
  have hLP : ENNReal.ofReal (W a / W b) ≤ F b (b - a) := by
    simpa only [hF, heqB] using
      (avram_wave3_01_unbounded_genuine_record_scale_sandwich
        X q hq W hW hnbv b (b - a) hb hh hsmallb).1
  have hratio : 0 ≤ W a / W b := by
    apply (div_pos
      (scaleFunction_strict_pos_of_unbounded_variation X q W hW hnbv a ha)
      (scaleFunction_strict_pos_of_unbounded_variation X q W hW hnbv b hb)).le
  have htopB : F b (b - a) ≠ ⊤ := by
    have hle : F b (b - a) ≤ 1 := by
      simpa only [hF] using
        (avram_wave3_01_original_record_discount_le_one X q hq b (b - a))
    exact (lt_top_iff_ne_top).mp (lt_of_le_of_lt hle (by simp))
  have hupperReal : (F a (b - a)).toReal ≤ W a / W b := by
    have hh' := ENNReal.toReal_mono ENNReal.ofReal_ne_top hUP
    simpa only [ENNReal.toReal_ofReal hratio] using hh'
  have hlowerReal : W a / W b ≤ (F b (b - a)).toReal := by
    have hh' := ENNReal.toReal_mono htopB hLP
    simpa only [ENNReal.toReal_ofReal hratio] using hh'
  have hFa0 : (F a (b - a)).toReal = Real.exp (-(b - a) * κ a) := by
    simpa only [hF, hκ] using
      (avram_wave4_01_original_record_exponential_hazard
        X q hq W hW hvar a ha (b - a) hh)
  have hFb0 : (F b (b - a)).toReal = Real.exp (-(b - a) * κ b) := by
    simpa only [hF, hκ] using
      (avram_wave4_01_original_record_exponential_hazard
        X q hq W hW hvar b hb (b - a) hh)
  constructor
  · calc
      Real.exp (-(κ a * (b - a))) =
        Real.exp (-(b - a) * κ a) := by congr 1; ring
      _ = (F a (b - a)).toReal := hFa0.symm
      _ ≤ W a / W b := hupperReal
  · calc
      W a / W b ≤ (F b (b - a)).toReal := hlowerReal
      _ = Real.exp (-(b - a) * κ b) := hFb0
      _ = Real.exp (-(κ b * (b - a))) := by congr 1; ring
