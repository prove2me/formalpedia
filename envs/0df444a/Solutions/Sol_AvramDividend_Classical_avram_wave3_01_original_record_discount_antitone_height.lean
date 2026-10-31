-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_01_original_record_discount_antitone_height
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T22:18:19.032266+00:00
-- url     : https://prove2.me/submissions/88d202e8-b113-4155-9d6d-533fc2dc9a21

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_uncapped_reflected_record_discount_semigroup

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The genuine killed first-record discount decreases with height. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a q : ℝ) (ha : 0 < a) (hq : 0 < q) :
    ∀ h k : ℝ, 0 < h → h ≤ k →
      (∫⁻ ω, if twoSidedExitUpTime X k ω < barrierRuinTime X a ω then
        ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X k ω).toReal)))
      else 0 ∂P) ≤
      (∫⁻ ω, if twoSidedExitUpTime X h ω < barrierRuinTime X a ω then
        ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
      else 0 ∂P) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let F : ℝ → ℝ≥0∞ := fun h =>
    ∫⁻ ω, if twoSidedExitUpTime X h ω < barrierRuinTime X a ω then
      ENNReal.ofReal
        (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
    else 0 ∂P
  have hFle (h : ℝ) : F h ≤ 1 := by
    have hpt (ω : Ω) :
        (if twoSidedExitUpTime X h ω < barrierRuinTime X a ω then
          ENNReal.ofReal (Real.exp
            (-(q * (twoSidedExitUpTime X h ω).toReal)))
        else 0) ≤ (1 : ℝ≥0∞) := by
      split_ifs
      · have ht : 0 ≤ (twoSidedExitUpTime X h ω).toReal :=
          ENNReal.toReal_nonneg
        have hqt : 0 ≤ q * (twoSidedExitUpTime X h ω).toReal :=
          mul_nonneg hq.le ht
        have he : Real.exp
            (-(q * (twoSidedExitUpTime X h ω).toReal)) ≤ 1 := by
          simpa only [Real.exp_zero] using
            (Real.exp_le_exp.mpr (neg_nonpos.mpr hqt))
        simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal he
      · exact zero_le_one
    calc
      F h ≤ ∫⁻ _ : Ω, (1 : ℝ≥0∞) ∂P := lintegral_mono hpt
      _ = 1 := by simp
  intro h k hh hhk
  change F k ≤ F h
  by_cases he : h = k
  · simpa only [he] using (le_refl (F k))
  · have hlt : h < k := lt_of_le_of_ne hhk he
    have hdiff : 0 < k - h := sub_pos.mpr hlt
    have hsem : F (h + (k - h)) = F h * F (k - h) := by
      simpa only [F] using
        avram_wave3_01_uncapped_reflected_record_discount_semigroup
          X a h (k - h) q ha hh hdiff hq
    have heq : h + (k - h) = k := by ring
    rw [heq] at hsem
    rw [hsem]
    calc
      F h * F (k - h) ≤ F h * 1 := by
        gcongr <;> exact hFle (k - h)
      _ = F h := mul_one _
