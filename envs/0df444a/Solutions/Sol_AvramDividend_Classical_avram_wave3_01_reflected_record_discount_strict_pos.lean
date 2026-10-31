-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_01_reflected_record_discount_strict_pos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T17:44:00.509222+00:00
-- url     : https://prove2.me/submissions/9667c811-64d8-4490-a18a-151b06f1febb

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_unbounded_genuine_record_scale_sandwich
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_uncapped_reflected_record_discount_semigroup
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
/-- Positivity at sub-barrier records propagates to every positive record
height by the genuine uncapped killed-record semigroup. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hnbv : ¬ X.BoundedVariation)
    (a : ℝ) (ha : 0 < a) :
    ∀ h : ℝ, 0 < h →
      0 < (∫⁻ ω, if twoSidedExitUpTime X h ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal
          (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
      else 0 ∂P) := by
  let F : ℝ → ℝ≥0∞ := fun h =>
    ∫⁻ ω, if twoSidedExitUpTime X h ω < barrierRuinTime X a ω then
      ENNReal.ofReal
        (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
    else 0 ∂P
  have hsem (b c : ℝ) (hb : 0 < b) (hc : 0 < c) :
      F (b + c) = F b * F c := by
    simpa only [F] using
      (avram_wave3_01_uncapped_reflected_record_discount_semigroup
        X a b c q ha hb hc hq)
  have hsmall (h : ℝ) (hh : 0 < h) (hha : h < a) :
      0 < F h := by
    have hposL : 0 < W (a - h) :=
      scaleFunction_strict_pos_of_unbounded_variation X q W hW hnbv (a - h) (by linarith)
    have hposR : 0 < W a := scaleFunction_strict_pos_of_unbounded_variation X q W hW hnbv a ha
    have hbound :=
      (avram_wave3_01_unbounded_genuine_record_scale_sandwich
        X q hq W hW hnbv a h ha hh hha).1
    have hratio : 0 < ENNReal.ofReal (W (a - h) / W a) :=
      ENNReal.ofReal_pos.mpr (div_pos hposL hposR)
    exact lt_of_lt_of_le hratio (by simpa only [F] using hbound)
  have hpow (y : ℝ) (hy : 0 < y) :
      ∀ n : ℕ, F (((n : ℝ) + 1) * y) = (F y) ^ (n + 1) := by
    intro n
    induction n with
    | zero =>
        norm_num
    | succ n ih =>
        have hn0 : 0 < ((n : ℝ) + 1) * y :=
          mul_pos (by positivity) hy
        have hadd : (((n + 1 : ℕ) : ℝ) + 1) * y =
            ((n : ℝ) + 1) * y + y := by
          push_cast
          ring
        rw [hadd, hsem _ _ hn0 hy, ih]
        simp only [pow_succ]
  intro h hh
  obtain ⟨n, hn⟩ := exists_nat_gt (h / a)
  let y : ℝ := h / ((n : ℝ) + 1)
  have hn0 : 0 < (n : ℝ) + 1 := by positivity
  have hy : 0 < y := div_pos hh hn0
  have hylt : y < a := by
    have hna : h / a < (n : ℝ) + 1 := lt_trans hn (by linarith)
    have hmul : h < ((n : ℝ) + 1) * a :=
      (div_lt_iff₀ ha).mp hna
    exact (div_lt_iff₀ hn0).mpr (by nlinarith)
  have heq : ((n : ℝ) + 1) * y = h := by
    dsimp [y]
    field_simp
  change 0 < F h
  rw [← heq, hpow y hy n]
  exact ENNReal.pow_pos (hsmall y hy hylt) _
