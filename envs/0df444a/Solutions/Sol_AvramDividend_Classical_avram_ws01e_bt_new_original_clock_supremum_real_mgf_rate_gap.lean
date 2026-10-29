-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_bt_new_original_clock_supremum_real_mgf_rate_gap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T01:04:32.267425+00:00
-- url     : https://prove2.me/submissions/872b7dbb-dc1c-4323-8a13-24464d244782

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_original_clock_supremum_lintegral_rate_gap
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- The genuine original exponential-clock running maximum has a
finite real MGF throughout its complete strict positive-root gap. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (p : ℝ) (hp : 0 < p)
    (lam : ℝ) (hlam : 0 < lam) (hroot : X.ψ lam = p)
    (β : ℝ) (hβlam : β < lam) :
    mgf (fun z : Ω × ℝ =>
      runningSup X (Real.toNNReal z.2) z.1)
      (P.prod (expMeasure p)) β =
    lam / (lam - β) := by
  let μ : Measure (Ω × ℝ) := P.prod (expMeasure p)
  let S : Ω × ℝ → ℝ :=
    fun z => runningSup X (Real.toNNReal z.2) z.1
  have hLamPos : 0 < lam - β := sub_pos.mpr hβlam
  have hLamNe : lam - β ≠ 0 := ne_of_gt hLamPos
  have hSMeas : Measurable S :=
    (levy_exponential_real_clock_extrema_drawdown_measurable X).fst.fst
  have hExpMeas : Measurable (fun z : Ω × ℝ => Real.exp (β * S z)) :=
    (measurable_const.mul hSMeas).exp
  have hENN :
      ENNReal.ofReal (lam - β) *
        (∫⁻ z : Ω × ℝ, ENNReal.ofReal (Real.exp (β * S z)) ∂μ) =
      ENNReal.ofReal lam := by
    simpa only [S, μ] using
      (avram_ws01e_bt_new_original_clock_supremum_lintegral_rate_gap
        X p hp lam hlam hroot β hβlam)
  have hFinite :
      (∫⁻ z : Ω × ℝ, ENNReal.ofReal (Real.exp (β * S z)) ∂μ) ≠ ⊤ := by
    intro htop
    have hc : ENNReal.ofReal (lam - β) ≠ 0 :=
      ne_of_gt (ENNReal.ofReal_pos.mpr hLamPos)
    rw [htop, ENNReal.mul_top hc] at hENN
    have hLamFinite : ENNReal.ofReal lam ≠ ⊤ := ENNReal.ofReal_ne_top
    exact hLamFinite hENN.symm
  have hInt : Integrable (fun z : Ω × ℝ => Real.exp (β * S z)) μ :=
    (lintegral_ofReal_ne_top_iff_integrable
      hExpMeas.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z => Real.exp_nonneg (β * S z)))).mp hFinite
  have hConvert :
      ENNReal.ofReal (∫ z : Ω × ℝ, Real.exp (β * S z) ∂μ) =
      (∫⁻ z : Ω × ℝ, ENNReal.ofReal (Real.exp (β * S z)) ∂μ) := by
    apply ofReal_integral_eq_lintegral_ofReal hInt
    filter_upwards [] with z
    exact (Real.exp_pos _).le
  have hMGFNonneg : 0 ≤ mgf S μ β := by
    change 0 ≤ ∫ z : Ω × ℝ, Real.exp (β * S z) ∂μ
    exact integral_nonneg (fun z => Real.exp_nonneg _)
  have hReal : (lam - β) * mgf S μ β = lam := by
    apply (ENNReal.ofReal_eq_ofReal_iff
      (mul_nonneg hLamPos.le hMGFNonneg) hlam.le).mp
    rw [ENNReal.ofReal_mul hLamPos.le]
    change ENNReal.ofReal (lam - β) *
      ENNReal.ofReal (∫ z : Ω × ℝ, Real.exp (β * S z) ∂μ) =
      ENNReal.ofReal lam
    rw [hConvert]
    exact hENN
  change mgf S μ β = lam / (lam - β)
  apply (eq_div_iff hLamNe).2
  simpa only [mul_comm] using hReal
