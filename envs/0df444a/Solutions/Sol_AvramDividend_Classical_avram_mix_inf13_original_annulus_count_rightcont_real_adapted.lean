-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_inf13_original_annulus_count_rightcont_real_adapted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T08:14:35.795792+00:00
-- url     : https://prove2.me/submissions/a3de5ea7-c918-4048-8267-1f493c3a7324

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_run1640_original_cutoff_past_count_rightcont_real_adapted
import Theorems.Thm_AvramDividend_Classical_avram_mixed_source13_original_nested_cutoff_annulus_count_additive
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_count_eq_finite_marked_time_card
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin_source13_original_annulus_count_finite_every_path

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section

/-- The actual annulus count is a difference of two finite, adapted original cutoff counts. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (n m : ℕ) (hnm : n ≤ m) :
    StronglyMeasurable[𝓕.rightCont T] (fun ω : Ω =>
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Ioc (-(1 / ((n : ℝ) + 1)))
          (-(1 / ((m : ℝ) + 1))))).toReal) := by
  classical
  let J : ℕ → Ω → ℝ≥0∞ := fun j ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Iic (-(1 / ((j : ℝ) + 1))))
  let A : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Ioc (-(1 / ((n : ℝ) + 1)))
        (-(1 / ((m : ℝ) + 1))))
  have hCut (j : ℕ) :
      StronglyMeasurable[𝓕.rightCont T] (fun ω => (J j ω).toReal) := by
    simpa only [J] using
      (avram_p4_s3_run1640_original_cutoff_past_count_rightcont_real_adapted X T j)
  have hFiniteCut (j : ℕ) (ω : Ω) : J j ω ≠ ⊤ := by
    have h := avram_wave7_06_original_negative_band_count_eq_finite_marked_time_card
      X ω T j
    change J j ω = _ at h
    rw [h]
    simp
  have hFiniteA (ω : Ω) : A ω ≠ ⊤ := by
    simpa only [A] using
      (avram_mix_fin_source13_original_annulus_count_finite_every_path
        X T n m hnm ω)
  have hDifference (ω : Ω) :
      (A ω).toReal = (J m ω).toReal - (J n ω).toReal := by
    have hadd :=
      avram_mixed_source13_original_nested_cutoff_annulus_count_additive
        X T n m hnm ω
    change J m ω = J n ω + A ω at hadd
    have hr := congrArg ENNReal.toReal hadd
    rw [ENNReal.toReal_add (hFiniteCut n ω) (hFiniteA ω)] at hr
    linarith
  change StronglyMeasurable[𝓕.rightCont T] (fun ω => (A ω).toReal)
  have hEqFun : (fun ω => (A ω).toReal) =
      (fun ω => (J m ω).toReal) - (fun ω => (J n ω).toReal) := by
    funext ω
    exact hDifference ω
  rw [hEqFun]
  exact (hCut m).sub (hCut n)
