-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_02_source_esscher_record_height_rate_antitone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T10:08:58.127582+00:00
-- url     : https://prove2.me/submissions/a78e405d-8964-4d7a-b8e2-001347cd5208

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_mono_barrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_infinite_small_jump_not_bv
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_reflected_record_discount_strict_pos
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_original_record_discount_le_one
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Actual reflected stopping-time monotonicity forces the shifted positive
Esscher killed-record height rate to be nonincreasing in height. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ∀ a b : ℝ, 0 < a → a ≤ b →
      -Real.log ((∫⁻ ω, if twoSidedExitUpTime X 1 ω <
          barrierRuinTime X b ω then
          ENNReal.ofReal
            (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
        else 0 ∂P).toReal) - φ ≤
      -Real.log ((∫⁻ ω, if twoSidedExitUpTime X 1 ω <
          barrierRuinTime X a ω then
          ENNReal.ofReal
            (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
        else 0 ∂P).toReal) - φ := by
  let F : ℝ → ℝ≥0∞ := fun d =>
    ∫⁻ ω, if twoSidedExitUpTime X 1 ω < barrierRuinTime X d ω then
      ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
    else 0 ∂P
  change ∀ a b : ℝ, 0 < a → a ≤ b →
    -Real.log ((F b).toReal) - φ ≤ -Real.log ((F a).toReal) - φ
  intro a b ha hab
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hnbv : ¬ X.BoundedVariation :=
    avram_wave3_01_infinite_small_jump_not_bv X hvar
  have hFa : 0 < F a := by
    exact (avram_wave3_01_reflected_record_discount_strict_pos
      X q hq W hW hnbv a ha) 1 (by norm_num)
  have hFb : 0 < F b := by
    exact (avram_wave3_01_reflected_record_discount_strict_pos
      X q hq W hW hnbv b hb) 1 (by norm_num)
  have hFaLe : F a ≤ 1 := by
    exact avram_wave3_01_original_record_discount_le_one X q hq a 1
  have hFbLe : F b ≤ 1 := by
    exact avram_wave3_01_original_record_discount_le_one X q hq b 1
  have hFaFinite : F a ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt hFaLe ENNReal.one_lt_top)
  have hFbFinite : F b ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt hFbLe ENNReal.one_lt_top)
  have hpt (ω : Ω) :
      (if twoSidedExitUpTime X 1 ω < barrierRuinTime X a ω then
        ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
      else 0) ≤
      (if twoSidedExitUpTime X 1 ω < barrierRuinTime X b ω then
        ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
      else 0) := by
    split_ifs with hA hB
    · exact le_rfl
    · exact (hB (lt_of_lt_of_le hA
        (barrierRuinTime_mono_barrier X a b hab ω))).elim
    · exact bot_le
    · exact le_rfl
  have hmono : F a ≤ F b := by
    exact lintegral_mono hpt
  have hR : (F a).toReal ≤ (F b).toReal :=
    ENNReal.toReal_mono hFbFinite hmono
  have hRpos : 0 < (F a).toReal :=
    ENNReal.toReal_pos (ne_of_gt hFa) hFaFinite
  have hLog : Real.log ((F a).toReal) ≤ Real.log ((F b).toReal) :=
    Real.log_le_log hRpos hR
  linarith
