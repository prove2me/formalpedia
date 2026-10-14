-- Prove2me | solution 1 for DbarRegularity.lintegral_sq_lintegral_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T14:59:41.629492+00:00
-- url     : https://prove2.me/submissions/919edfc5-bb2c-4578-8f81-e5457220aa36

import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.PiL2



namespace DbarRegularity

open MeasureTheory
open scoped ENNReal

/-- `L² × L¹ → L²` Young inequality for the convolution of absolute values, in squared
lower-integral form. -/
theorem lintegral_sq_lintegral_mul_le {d : ℕ} (h f : EuclideanSpace ℝ (Fin d) → ℂ)
    (hh : AEStronglyMeasurable h volume) (hf : AEStronglyMeasurable f volume) :
    ∫⁻ x, (∫⁻ y, ‖h (x - y)‖ₑ * ‖f y‖ₑ) ^ 2
      ≤ (∫⁻ x, ‖h x‖ₑ ^ 2) * (∫⁻ y, ‖f y‖ₑ) ^ 2 := by
  have hH : AEMeasurable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => ‖h (p.1 - p.2)‖ₑ) (volume.prod volume) :=
    hh.enorm.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub volume volume)
  have hF : AEMeasurable (fun y : EuclideanSpace ℝ (Fin d) => ‖f y‖ₑ) volume := hf.enorm
  have hHx : ∀ x : EuclideanSpace ℝ (Fin d), AEMeasurable (fun y : EuclideanSpace ℝ (Fin d) => ‖h (x - y)‖ₑ) volume := fun x =>
    hh.enorm.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_left volume x)
  -- pointwise weighted Cauchy–Schwarz
  have hCS : ∀ x : EuclideanSpace ℝ (Fin d), (∫⁻ y, ‖h (x - y)‖ₑ * ‖f y‖ₑ) ^ 2 ≤
      (∫⁻ y, ‖h (x - y)‖ₑ ^ 2 * ‖f y‖ₑ) * ∫⁻ y, ‖f y‖ₑ := by
    intro x
    have := ENNReal.lintegral_mul_norm_pow_le (μ := volume)
      (f := fun y => ‖h (x - y)‖ₑ ^ 2 * ‖f y‖ₑ) (g := fun y => ‖f y‖ₑ)
      (((hHx x).pow_const 2).mul hF) hF (p := 1 / 2) (q := 1 / 2) (by norm_num) (by norm_num)
      (by norm_num)
    have hsq : ∀ a b : ℝ≥0∞, (a ^ 2 * b) ^ (1 / 2 : ℝ) * b ^ (1 / 2 : ℝ) = a * b := by
      intro a b
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), mul_assoc,
        ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
      norm_num
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
    simp_rw [hsq] at this
    calc (∫⁻ y, ‖h (x - y)‖ₑ * ‖f y‖ₑ) ^ 2
        ≤ ((∫⁻ y, ‖h (x - y)‖ₑ ^ 2 * ‖f y‖ₑ) ^ (1 / 2 : ℝ) *
            (∫⁻ y, ‖f y‖ₑ) ^ (1 / 2 : ℝ)) ^ 2 := by gcongr
      _ = _ := by
        rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, ← ENNReal.rpow_natCast,
          ← ENNReal.rpow_mul]; norm_num
  have hP : AEMeasurable (Function.uncurry fun (x y : EuclideanSpace ℝ (Fin d)) =>
      ‖h (x - y)‖ₑ ^ 2 * ‖f y‖ₑ) (volume.prod volume) :=
    (hH.pow_const 2).mul hF.comp_snd
  have hPx : AEMeasurable (fun x : EuclideanSpace ℝ (Fin d) =>
      ∫⁻ y, ‖h (x - y)‖ₑ ^ 2 * ‖f y‖ₑ) volume := hP.lintegral_prod_right'
  calc ∫⁻ x, (∫⁻ y, ‖h (x - y)‖ₑ * ‖f y‖ₑ) ^ 2
      ≤ ∫⁻ x, (∫⁻ y, ‖h (x - y)‖ₑ ^ 2 * ‖f y‖ₑ) * ∫⁻ y, ‖f y‖ₑ := lintegral_mono hCS
    _ = (∫⁻ x, ∫⁻ y, ‖h (x - y)‖ₑ ^ 2 * ‖f y‖ₑ) * ∫⁻ y, ‖f y‖ₑ := lintegral_mul_const'' _ hPx
    _ = (∫⁻ y, ∫⁻ x, ‖h (x - y)‖ₑ ^ 2 * ‖f y‖ₑ) * ∫⁻ y, ‖f y‖ₑ := by
        rw [lintegral_lintegral_swap hP]
    _ = (∫⁻ y, (∫⁻ x, ‖h x‖ₑ ^ 2) * ‖f y‖ₑ) * ∫⁻ y, ‖f y‖ₑ := by
        congr 1; refine lintegral_congr fun y => ?_
        have hm : AEMeasurable (fun x : EuclideanSpace ℝ (Fin d) => ‖h (x - y)‖ₑ ^ 2) volume :=
          (hh.enorm.pow_const 2).comp_quasiMeasurePreserving
            (measurePreserving_sub_right volume y).quasiMeasurePreserving
        rw [lintegral_mul_const'' _ hm, lintegral_sub_right_eq_self (fun x => ‖h x‖ₑ ^ 2) y]
    _ = _ := by rw [lintegral_const_mul'' _ hF]; ring

end DbarRegularity

open DbarRegularity

open MeasureTheory
open scoped ENNReal

theorem solution {d : ℕ} (h f : EuclideanSpace ℝ (Fin d) → ℂ)
    (hh : AEStronglyMeasurable h volume) (hf : AEStronglyMeasurable f volume) :
    ∫⁻ x, (∫⁻ y, ‖h (x - y)‖ₑ * ‖f y‖ₑ) ^ 2
      ≤ (∫⁻ x, ‖h x‖ₑ ^ 2) * (∫⁻ y, ‖f y‖ₑ) ^ 2 :=
  lintegral_sq_lintegral_mul_le h f hh hf
