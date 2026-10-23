-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_double_tail_real_kernel_weighted_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T14:18:25.718838+00:00
-- url     : https://prove2.me/submissions/c9ff3562-224a-4cb8-b0d4-bdd77593dfc0

import Mathlib
import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_real_kernel_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal

theorem solution
    (μ : Measure ℝ) [SFinite μ] (φ θ : ℝ)
    (hφ : 0 < φ) (hθ : 0 ≤ θ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    IntegrableOn
      (fun t : ℝ => Real.exp (-(θ * t)) *
        (∫⁻ z : ℝ,
          (if 0 < t ∧ t < z then
            ENNReal.ofReal (z - t) *
              ENNReal.ofReal (Real.exp (-(φ * z)))
           else 0) ∂μ).toReal)
      (Ioi (0 : ℝ)) volume := by
  let K : ℝ → ℝ := fun t =>
    (∫⁻ z : ℝ,
      (if 0 < t ∧ t < z then
        ENNReal.ofReal (z - t) *
          ENNReal.ofReal (Real.exp (-(φ * z)))
       else 0) ∂μ).toReal
  have hK : Integrable K volume :=
    gaussian_double_tail_real_kernel_integrable μ φ hφ hlevy
  have hKon : Integrable K (volume.restrict (Ioi (0 : ℝ))) :=
    hK.integrableOn
  have hcont : Continuous (fun t : ℝ => Real.exp (-(θ * t))) := by fun_prop
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => Real.exp (-(θ * t)) * K t)
      (volume.restrict (Ioi (0 : ℝ))) :=
    hcont.measurable.aestronglyMeasurable.mul hKon.aestronglyMeasurable
  apply hKon.mono hmeas
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with t ht
  have hnonneg : 0 ≤ θ * t := mul_nonneg hθ ht.le
  have he : Real.exp (-(θ * t)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr hnonneg)
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact (mul_le_mul_of_nonneg_right he (norm_nonneg (K t))).trans_eq (one_mul _)
