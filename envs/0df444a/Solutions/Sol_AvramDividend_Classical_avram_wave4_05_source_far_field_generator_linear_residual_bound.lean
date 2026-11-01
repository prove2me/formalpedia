-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05_source_far_field_generator_linear_residual_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T15:45:12.085545+00:00
-- url     : https://prove2.me/submissions/5077a012-3f62-4eea-8ddd-d7d279da50e2

import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_far_field_generator_residual_le_drift_minus_discount
import Theorems.Thm_AvramDividend_Classical_barrierValue_nonnegative_for_nonnegative_capital
import Theorems.Thm_AvramDividend_Classical_vcstar_eq_linear_gt_cstar
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The true compensated source generator has at most affine-linear residual growth
with strictly negative discount slope above the barrier by one jump unit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (x : ℝ) (hfar : (cstar W).toReal + 1 ≤ x) :
    X.GeneratorIntegrable (vcstar W) x ∧
      X.generator (vcstar W) x ≤ X.c ∧
      X.generator (vcstar W) x - q * vcstar W x ≤
        X.c - q * (x - (cstar W).toReal) := by
  let a : ℝ := (cstar W).toReal
  have ha : 0 ≤ a := ENNReal.toReal_nonneg
  have hx : a < x := by dsimp [a] at *; linarith
  have hb : 0 ≤ barrierValue W a a :=
    barrierValue_nonnegative_for_nonnegative_capital
      X hX q hq W hW a a ha ha
  have hboundary : barrierValue W a a =
      divE (W a) (scaleDeriv W a) := by
    simp [barrierValue, not_lt.mpr ha]
  have hval : vcstar W x = x - a + barrierValue W a a := by
    calc
      vcstar W x = x - a + divE (W a) (scaleDeriv W a) :=
        vcstar_eq_linear_gt_cstar W x hx
      _ = x - a + barrierValue W a a := by rw [hboundary]
  have hle : x - a ≤ vcstar W x := by rw [hval]; linarith
  have hmul := mul_le_mul_of_nonneg_left hle hq.le
  obtain ⟨hdom, hres⟩ :=
    avram_wave4_05_source_far_field_generator_residual_le_drift_minus_discount
      X hX q hq W hW x hfar
  refine ⟨hdom, ?_, ?_⟩
  · linarith
  · dsimp [a] at *
    linarith
