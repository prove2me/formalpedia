-- Prove2me | solution 2 for BanditAlgorithm.le_cam_cauchy_affinity
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T02:17:11.8788+00:00
-- url     : https://prove2.me/submissions/e2536598-0c81-400a-acd0-8a33d23b11ca

import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

open MeasureTheory InformationTheory
open scoped ENNReal

theorem solution {Ω : Type} {mΩ : MeasurableSpace Ω}
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    (2 : ℝ≥0∞)⁻¹ *
        (∫⁻ ω, (P.rnDeriv (P + Q) ω * Q.rnDeriv (P + Q) ω) ^ (2⁻¹ : ℝ)
          ∂(P + Q)) ^ 2 ≤
      ∫⁻ ω, min (P.rnDeriv (P + Q) ω) (Q.rnDeriv (P + Q) ω) ∂(P + Q) := by
  have hpm : Measurable (P.rnDeriv (P + Q)) := Measure.measurable_rnDeriv P (P + Q)
  have hqm : Measurable (Q.rnDeriv (P + Q)) := Measure.measurable_rnDeriv Q (P + Q)
  -- the densities integrate to the total masses `P Ω = 1` and `Q Ω = 1`
  have hP : ∫⁻ ω, P.rnDeriv (P + Q) ω ∂(P + Q) = 1 := by
    rw [Measure.lintegral_rnDeriv
      (Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl))]
    exact measure_univ
  have hQ : ∫⁻ ω, Q.rnDeriv (P + Q) ω ∂(P + Q) = 1 := by
    rw [Measure.lintegral_rnDeriv
      (Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl))]
    exact measure_univ
  set p := P.rnDeriv (P + Q) with hp
  set q := Q.rnDeriv (P + Q) with hq
  set μ := P + Q with hμ
  -- `(x ^ (1/2)) ^ 2 = x`
  have hsq : ∀ x : ℝ≥0∞, (x ^ (2⁻¹ : ℝ)) ^ (2 : ℝ) = x := by
    intro x
    rw [← ENNReal.rpow_mul]
    norm_num
  -- Step 1: `∫ max(p,q) ≤ ∫ (p + q) = 2`
  have hmax : ∫⁻ ω, max (p ω) (q ω) ∂μ ≤ 2 := by
    calc ∫⁻ ω, max (p ω) (q ω) ∂μ ≤ ∫⁻ ω, p ω + q ω ∂μ :=
          lintegral_mono fun ω => max_le le_self_add le_add_self
      _ = 1 + 1 := by rw [lintegral_add_left hpm, hP, hQ]
      _ = 2 := one_add_one_eq_two
  -- Step 2: Cauchy–Schwarz with `√(pq) = √(min(p,q)) · √(max(p,q))`
  have hCS : ∫⁻ ω, (p ω * q ω) ^ (2⁻¹ : ℝ) ∂μ ≤
      (∫⁻ ω, min (p ω) (q ω) ∂μ) ^ (2⁻¹ : ℝ) *
        (∫⁻ ω, max (p ω) (q ω) ∂μ) ^ (2⁻¹ : ℝ) := by
    have hf : AEMeasurable (fun ω => (min (p ω) (q ω)) ^ (2⁻¹ : ℝ)) μ :=
      ((hpm.min hqm).pow_const _).aemeasurable
    have hg : AEMeasurable (fun ω => (max (p ω) (q ω)) ^ (2⁻¹ : ℝ)) μ :=
      ((hpm.max hqm).pow_const _).aemeasurable
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hf hg
    have hpt : ∀ ω, ((fun ω => (min (p ω) (q ω)) ^ (2⁻¹ : ℝ)) *
        (fun ω => (max (p ω) (q ω)) ^ (2⁻¹ : ℝ))) ω = (p ω * q ω) ^ (2⁻¹ : ℝ) := by
      intro ω
      simp only [Pi.mul_apply]
      rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2⁻¹), min_mul_max]
    simp only [hpt, hsq, one_div] at h
    exact h
  -- Step 3: square the Cauchy–Schwarz bound
  have hsq2 : (∫⁻ ω, (p ω * q ω) ^ (2⁻¹ : ℝ) ∂μ) ^ 2 ≤
      (∫⁻ ω, min (p ω) (q ω) ∂μ) * (∫⁻ ω, max (p ω) (q ω) ∂μ) := by
    calc (∫⁻ ω, (p ω * q ω) ^ (2⁻¹ : ℝ) ∂μ) ^ 2
        ≤ ((∫⁻ ω, min (p ω) (q ω) ∂μ) ^ (2⁻¹ : ℝ) *
            (∫⁻ ω, max (p ω) (q ω) ∂μ) ^ (2⁻¹ : ℝ)) ^ 2 :=
          pow_le_pow_left' hCS 2
      _ = (∫⁻ ω, min (p ω) (q ω) ∂μ) * (∫⁻ ω, max (p ω) (q ω) ∂μ) := by
          rw [mul_pow, ← ENNReal.rpow_two, ← ENNReal.rpow_two, hsq, hsq]
  -- Step 4: conclude
  rw [ENNReal.inv_mul_le_iff (by norm_num) ENNReal.ofNat_ne_top]
  calc (∫⁻ ω, (p ω * q ω) ^ (2⁻¹ : ℝ) ∂μ) ^ 2
      ≤ (∫⁻ ω, min (p ω) (q ω) ∂μ) * (∫⁻ ω, max (p ω) (q ω) ∂μ) := hsq2
    _ ≤ (∫⁻ ω, min (p ω) (q ω) ∂μ) * 2 := mul_le_mul_right hmax _
    _ = 2 * ∫⁻ ω, min (p ω) (q ω) ∂μ := mul_comm _ _
