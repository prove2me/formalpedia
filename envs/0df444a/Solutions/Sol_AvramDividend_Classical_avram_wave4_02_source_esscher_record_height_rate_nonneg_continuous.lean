-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_02_source_esscher_record_height_rate_nonneg_continuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T09:46:43.830382+00:00
-- url     : https://prove2.me/submissions/b23e306a-41a0-4d5a-9060-606a9bc4b395

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_infinite_small_jump_not_bv
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_canonical_infinite_jump_log_rate_continuous
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_genuine_local_scale_ratio_sandwich
import Theorems.Thm_AvramDividend_Classical_unbounded_esscher_root_first_passage_scale_decay
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal
/-- The actual killed first-record rate, normalised by the positive Esscher
root, is a nonnegative continuous source-derived height-hazard candidate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ContinuousOn (fun a : ℝ =>
      -Real.log ((∫⁻ ω, if twoSidedExitUpTime X 1 ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal
          (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
      else 0 ∂P).toReal) - φ) (Ioi (0 : ℝ)) ∧
    ∀ a : ℝ, 0 < a →
      0 ≤ -Real.log ((∫⁻ ω, if twoSidedExitUpTime X 1 ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal
          (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
      else 0 ∂P).toReal) - φ := by
  let F : ℝ → ℝ → ℝ≥0∞ := fun a h =>
    ∫⁻ ω, if twoSidedExitUpTime X h ω < barrierRuinTime X a ω then
      ENNReal.ofReal
        (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
    else 0 ∂P
  let κ : ℝ → ℝ := fun a => -Real.log ((F a 1).toReal)
  have hF : ∀ a h : ℝ, F a h =
      ∫⁻ ω, if twoSidedExitUpTime X h ω < barrierRuinTime X a ω then
        ENNReal.ofReal
          (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
      else 0 ∂P := by intros; rfl
  have hκ : ∀ a : ℝ, κ a = -Real.log ((F a 1).toReal) := by intro; rfl
  change ContinuousOn (fun a => κ a - φ) (Ioi (0 : ℝ)) ∧
    ∀ a : ℝ, 0 < a → 0 ≤ κ a - φ
  constructor
  · have hc :=
      avram_wave3_01_canonical_infinite_jump_log_rate_continuous
        X q hq W hW hvar
    change ContinuousOn κ (Ioi (0 : ℝ)) at hc
    exact hc.sub continuousOn_const
  · intro a ha
    have hnbv : ¬ X.BoundedVariation :=
      avram_wave3_01_infinite_small_jump_not_bv X hvar
    let b : ℝ := a + a / 2
    have hab : a < b := by dsimp [b]; linarith
    have hsmall : b - a < a := by dsimp [b]; linarith
    have hb : 0 < b := lt_trans ha hab
    have hWb : 0 < W b :=
      scaleFunction_strict_pos_of_unbounded_variation X q W hW hnbv b hb
    have hsand :=
      (avram_wave4_01_genuine_local_scale_ratio_sandwich
        X q hq W hW hvar F hF κ hκ a b ha hab hsmall).1
    have hdec := unbounded_esscher_root_first_passage_scale_decay
      X q hq W hW hnbv φ hφ hroot a b ha hab.le
    have hratio : W a / W b ≤ Real.exp (-(φ * (b - a))) :=
      (div_le_iff₀ hWb).2 hdec
    have hκle : -(κ a * (b - a)) ≤ -(φ * (b - a)) :=
      Real.exp_le_exp.mp (le_trans hsand hratio)
    have hφκ : φ ≤ κ a := by
      by_contra hNot
      have hlt : κ a < φ := lt_of_not_ge hNot
      have hprod := mul_lt_mul_of_pos_right hlt (sub_pos.mpr hab)
      linarith
    exact sub_nonneg.mpr hφκ
