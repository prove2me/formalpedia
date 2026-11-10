-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_inf13_original_threecut_annulus_real_additivity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T12:57:32.217077+00:00
-- url     : https://prove2.me/submissions/9f307924-aa55-4d49-b73a-efd2cb9bde0b

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mixed_source13_original_nested_cutoff_annulus_count_additive
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_count_eq_finite_marked_time_card
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin_source13_original_annulus_count_finite_every_path
import Mathlib.Topology.Order.LeftRightLim

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section

/-- The original physical counts on adjacent negative annuli sum to the count on their union. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (n m p : ℕ) (hnm : n ≤ m) (hmp : m ≤ p) :
    let A : ℕ → ℕ → Ω → ℝ≥0∞ := fun a b ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Ioc (-(1 / ((a : ℝ) + 1)))
          (-(1 / ((b : ℝ) + 1))))
    ∀ ω, (A n p ω).toReal =
      (A n m ω).toReal + (A m p ω).toReal := by
  classical
  let K : ℕ → Ω → ℝ≥0∞ := fun j ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Iic (-(1 / ((j : ℝ) + 1))))
  let A : ℕ → ℕ → Ω → ℝ≥0∞ := fun a b ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Ioc (-(1 / ((a : ℝ) + 1)))
        (-(1 / ((b : ℝ) + 1))))
  change ∀ ω, (A n p ω).toReal =
    (A n m ω).toReal + (A m p ω).toReal
  have hFiniteK (j : ℕ) (ω : Ω) : K j ω ≠ ⊤ := by
    have h := avram_wave7_06_original_negative_band_count_eq_finite_marked_time_card
      X ω T j
    change K j ω = _ at h
    rw [h]
    simp
  have hFiniteA (a b : ℕ) (hab : a ≤ b) (ω : Ω) :
      A a b ω ≠ ⊤ := by
    simpa only [A] using
      (avram_mix_fin_source13_original_annulus_count_finite_every_path
        X T a b hab ω)
  have hDiff (a b : ℕ) (hab : a ≤ b) (ω : Ω) :
      (A a b ω).toReal = (K b ω).toReal - (K a ω).toReal := by
    have hadd :=
      avram_mixed_source13_original_nested_cutoff_annulus_count_additive
        X T a b hab ω
    change K b ω = K a ω + A a b ω at hadd
    have hr := congrArg ENNReal.toReal hadd
    rw [ENNReal.toReal_add (hFiniteK a ω) (hFiniteA a b hab ω)] at hr
    linarith
  intro ω
  have hnp := hDiff n p (le_trans hnm hmp) ω
  have hnm' := hDiff n m hnm ω
  have hmp' := hDiff m p hmp ω
  linarith
