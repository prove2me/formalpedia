-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_original_record_exponential_hazard
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T09:27:13.378828+00:00
-- url     : https://prove2.me/submissions/6ab7a1f7-4b53-4e47-9540-dab8ba8f3a81

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_infinite_small_jump_not_bv
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_reflected_record_discount_strict_pos
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_original_record_discount_le_one
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_original_record_toReal_semigroup
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_original_record_factor_tendsto_one_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_zero_extended_log_continuous_at_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_positive_semigroup_exp_law

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Topology

/-- The genuine original-Lévy killed record factor has exponential
height dependence at each positive reflected drawdown barrier. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (hjump : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤)
    (a : ℝ) (ha : 0 < a) :
    ∀ h : ℝ, 0 < h →
      (∫⁻ ω, if twoSidedExitUpTime X h ω < barrierRuinTime X a ω then
        ENNReal.ofReal
          (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
      else 0 ∂P).toReal =
      Real.exp (-h * (-Real.log
        ((∫⁻ ω, if twoSidedExitUpTime X 1 ω <
            barrierRuinTime X a ω then
          ENNReal.ofReal
            (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
        else 0 ∂P).toReal))) := by
  let F : ℝ → ℝ≥0∞ := fun h =>
    ∫⁻ ω, if twoSidedExitUpTime X h ω < barrierRuinTime X a ω then
      ENNReal.ofReal
        (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
    else 0 ∂P
  let R : ℝ → ℝ := fun h => (F h).toReal
  have hnbv : ¬ X.BoundedVariation :=
    avram_wave3_01_infinite_small_jump_not_bv X hjump
  have hFpos (h : ℝ) (hh : 0 < h) : 0 < F h := by
    exact avram_wave3_01_reflected_record_discount_strict_pos
      X q hq W hW hnbv a ha h hh
  have hFle (h : ℝ) : F h ≤ 1 := by
    exact avram_wave3_01_original_record_discount_le_one X q hq a h
  have hRpos (h : ℝ) (hh : 0 < h) : 0 < R h := by
    have htop : F h ≠ ⊤ := by
      exact (lt_top_iff_ne_top).mp
        (lt_of_le_of_lt (hFle h) (by simp))
    exact ENNReal.toReal_pos (ne_of_gt (hFpos h hh)) htop
  have hsem (b c : ℝ) (hb : 0 < b) (hc : 0 < c) :
      R (b + c) = R b * R c := by
    simpa only [R, F] using
      (avram_wave3_01_original_record_toReal_semigroup
        X a b c q ha hb hc hq)
  have hone : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ≥0∞)) := by
    simpa only [F] using
      (avram_wave3_01_original_record_factor_tendsto_one_zero
        X q hq W hW hjump a ha)
  have hcont : ContinuousAt (fun t : ℝ =>
      if 0 < t then Real.log (R t) else 0) 0 := by
    exact avram_wave3_01_zero_extended_log_continuous_at_zero F hone
  have hlaw := avram_wave4_01_positive_semigroup_exp_law
    R hRpos hsem hcont
  intro h hh
  have hidentity : (F h).toReal =
      Real.exp (h * Real.log ((F 1).toReal)) := by
    simpa only [R] using hlaw h hh
  change (F h).toReal =
    Real.exp (-h * (-Real.log ((F 1).toReal)))
  calc
    (F h).toReal = Real.exp (h * Real.log ((F 1).toReal)) := hidentity
    _ = Real.exp (-h * (-Real.log ((F 1).toReal))) := by
      congr 1
      ring
