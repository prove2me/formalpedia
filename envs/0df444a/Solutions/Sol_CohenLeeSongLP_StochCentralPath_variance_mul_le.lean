-- Prove2me | solution 1 for CohenLeeSongLP.StochCentralPath.variance_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T23:00:08.88272+00:00
-- url     : https://prove2.me/submissions/30fb1c49-218a-4bb8-b6cf-18b2bcf6bfb6

import Mathlib

open MeasureTheory ProbabilityTheory

namespace P37582f42

lemma sq_bound_integrable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Ω → ℝ) (C : ℝ) (hf : AEMeasurable f P) (hb : ∀ᵐ ω ∂P, |f ω| ≤ C) :
    Integrable (fun ω => f ω ^ 2) P := by
  refine Integrable.of_bound (hf.pow_const 2).aestronglyMeasurable (C ^ 2) ?_
  filter_upwards [hb] with ω h
  rw [Real.norm_eq_abs, abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) h 2

end P37582f42

open MeasureTheory ProbabilityTheory in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (cX cY : ℝ) (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (hXb : ∀ᵐ ω ∂P, |X ω| ≤ cX) (hYb : ∀ᵐ ω ∂P, |Y ω| ≤ cY) :
    variance (fun ω => X ω * Y ω) P ≤ 2 * cX ^ 2 * variance Y P + 2 * cY ^ 2 * variance X P := by
  set mX := P[X] with hmX
  set mY := P[Y] with hmY
  have hmXb : |mX| ≤ cX := by
    have := norm_integral_le_of_norm_le_const (μ := P) (C := cX) (f := X)
      (by filter_upwards [hXb] with ω h; simpa [Real.norm_eq_abs] using h)
    simpa [Real.norm_eq_abs] using this
  have hmYb : |mY| ≤ cY := by
    have := norm_integral_le_of_norm_le_const (μ := P) (C := cY) (f := Y)
      (by filter_upwards [hYb] with ω h; simpa [Real.norm_eq_abs] using h)
    simpa [Real.norm_eq_abs] using this
  have hXY : AEMeasurable (fun ω => X ω * Y ω) P := hX.mul hY
  have hZ : AEMeasurable (fun ω => X ω * Y ω - mX * mY) P := hXY.sub_const _
  rw [← variance_sub_const hXY.aestronglyMeasurable (mX * mY)]
  refine (variance_le_expectation_sq hZ.aestronglyMeasurable).trans ?_
  rw [variance_eq_integral hX, variance_eq_integral hY]
  have hI1 : Integrable (fun ω => (X ω * Y ω - mX * mY) ^ 2) P := by
    refine P37582f42.sq_bound_integrable P _ (cX * cY + |mX * mY|) hZ ?_
    filter_upwards [hXb, hYb] with ω h1 h2
    have hx0 : 0 ≤ |X ω| := abs_nonneg _
    have hy0 : 0 ≤ |Y ω| := abs_nonneg _
    calc |X ω * Y ω - mX * mY| ≤ |X ω * Y ω| + |mX * mY| := abs_sub _ _
      _ ≤ cX * cY + |mX * mY| := by
        rw [abs_mul]; gcongr; linarith
  have hI2 : Integrable (fun ω => (Y ω - mY) ^ 2) P := by
    refine P37582f42.sq_bound_integrable P _ (cY + |mY|) (hY.sub_const _) ?_
    filter_upwards [hYb] with ω h
    exact (abs_sub _ _).trans (by linarith)
  have hI3 : Integrable (fun ω => (X ω - mX) ^ 2) P := by
    refine P37582f42.sq_bound_integrable P _ (cX + |mX|) (hX.sub_const _) ?_
    filter_upwards [hXb] with ω h
    exact (abs_sub _ _).trans (by linarith)
  have hpow : P[(fun ω => X ω * Y ω - mX * mY) ^ 2] = ∫ ω, (X ω * Y ω - mX * mY) ^ 2 ∂P := by
    rfl
  have hR : ∫ ω, (2 * cX ^ 2 * (Y ω - mY) ^ 2 + 2 * cY ^ 2 * (X ω - mX) ^ 2) ∂P =
      2 * cX ^ 2 * ∫ ω, (Y ω - mY) ^ 2 ∂P + 2 * cY ^ 2 * ∫ ω, (X ω - mX) ^ 2 ∂P := by
    rw [integral_add (hI2.const_mul _) (hI3.const_mul _), integral_const_mul, integral_const_mul]
  rw [hpow, ← hR]
  refine integral_mono_ae hI1 ((hI2.const_mul _).add (hI3.const_mul _)) ?_
  filter_upwards [hXb, hYb] with ω h1 h2
  have e : X ω * Y ω - mX * mY = X ω * (Y ω - mY) + mY * (X ω - mX) := by ring
  have hx2 : X ω ^ 2 ≤ cX ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hm2 : mY ^ 2 ≤ cY ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hmYb 2
  have ha : 0 ≤ (Y ω - mY) ^ 2 := sq_nonneg _
  have hb : 0 ≤ (X ω - mX) ^ 2 := sq_nonneg _
  show (X ω * Y ω - mX * mY) ^ 2 ≤ 2 * cX ^ 2 * (Y ω - mY) ^ 2 + 2 * cY ^ 2 * (X ω - mX) ^ 2
  rw [e]
  have key : (X ω * (Y ω - mY) + mY * (X ω - mX)) ^ 2 ≤
      2 * (X ω ^ 2 * (Y ω - mY) ^ 2) + 2 * (mY ^ 2 * (X ω - mX) ^ 2) := by
    nlinarith [sq_nonneg (X ω * (Y ω - mY) - mY * (X ω - mX))]
  nlinarith [mul_le_mul_of_nonneg_right hx2 ha, mul_le_mul_of_nonneg_right hm2 hb]
