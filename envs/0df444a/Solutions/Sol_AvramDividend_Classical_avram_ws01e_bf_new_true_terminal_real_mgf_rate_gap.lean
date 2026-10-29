-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_bf_new_true_terminal_real_mgf_rate_gap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T21:57:25.700089+00:00
-- url     : https://prove2.me/submissions/5160e87d-bdd2-4041-bd84-b794d03e2de5

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_true_Qp_terminal_exp_moment_rate_gap
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (φ q p β : ℝ) (hφ : 0 < φ) (hq : 0 < q)
    (hroot : X.ψ φ = q) (hp : 0 < p)
    (hβ : 0 ≤ β) (hgap : X.ψ (φ + β) - q < p)
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (φ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ φ)))) :
    mgf (fun z : Ω × ℝ => X.X (Real.toNNReal z.2) z.1)
      ((P.prod (expMeasure p)).withDensity
        (fun z : Ω × ℝ => ENNReal.ofReal
          (Real.exp (φ * X.X (Real.toNNReal z.2) z.1 -
            (Real.toNNReal z.2 : ℝ) * X.ψ φ)))) β =
    p / (p - (X.ψ (φ + β) - q)) := by
  let μ : Measure (Ω × ℝ) :=
    ((P.prod (expMeasure p)).withDensity
      (fun z : Ω × ℝ => ENNReal.ofReal
        (Real.exp (φ * X.X (Real.toNNReal z.2) z.1 -
          (Real.toNNReal z.2 : ℝ) * X.ψ φ))))
  let V : Ω × ℝ → ℝ :=
    fun z => X.X (Real.toNNReal z.2) z.1
  let a : ℝ := X.ψ (φ + β) - q
  have hGapPos : 0 < p - a := sub_pos.mpr hgap
  have hGapNe : p - a ≠ 0 := ne_of_gt hGapPos
  have hClock : Measurable (fun z : Ω × ℝ => (Real.toNNReal z.2, z.1)) :=
    (measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst
  have hV : Measurable V :=
    (chat04_levy_joint_time_state_measurable X).comp hClock
  have hExpMeas : Measurable (fun z : Ω × ℝ => Real.exp (β * V z)) :=
    (measurable_const.mul hV).exp
  have hENN :
      ENNReal.ofReal (p - a) *
        (∫⁻ z : Ω × ℝ, ENNReal.ofReal (Real.exp (β * V z)) ∂μ) =
      ENNReal.ofReal p := by
    simpa only [a, V, μ] using
      (avram_ws01e_b_true_Qp_terminal_exp_moment_rate_gap
        X φ q p β hφ hq hroot hp hβ hgap hJoint)
  have hFinite :
      (∫⁻ z : Ω × ℝ, ENNReal.ofReal (Real.exp (β * V z)) ∂μ) ≠ ⊤ := by
    intro htop
    have hcoef : ENNReal.ofReal (p - a) ≠ 0 :=
      ne_of_gt (ENNReal.ofReal_pos.mpr hGapPos)
    rw [htop, ENNReal.mul_top hcoef] at hENN
    have hPFinite : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
    exact hPFinite hENN.symm
  have hInt : Integrable (fun z : Ω × ℝ => Real.exp (β * V z)) μ :=
    (lintegral_ofReal_ne_top_iff_integrable
      hExpMeas.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z => (Real.exp_nonneg (β * V z))))).mp hFinite
  have hConvert :
      ENNReal.ofReal (∫ z : Ω × ℝ, Real.exp (β * V z) ∂μ) =
      (∫⁻ z : Ω × ℝ, ENNReal.ofReal (Real.exp (β * V z)) ∂μ) := by
    apply ofReal_integral_eq_lintegral_ofReal hInt
    filter_upwards [] with z
    exact (Real.exp_pos _).le
  have hMGFNonneg : 0 ≤ mgf V μ β := by
    change 0 ≤ ∫ z : Ω × ℝ, Real.exp (β * V z) ∂μ
    exact integral_nonneg (fun z => Real.exp_nonneg _)
  have hReal : (p - a) * mgf V μ β = p := by
    apply (ENNReal.ofReal_eq_ofReal_iff
      (mul_nonneg hGapPos.le hMGFNonneg) hp.le).mp
    rw [ENNReal.ofReal_mul hGapPos.le]
    change ENNReal.ofReal (p - a) *
      ENNReal.ofReal (∫ z : Ω × ℝ, Real.exp (β * V z) ∂μ) =
      ENNReal.ofReal p
    rw [hConvert]
    exact hENN
  change mgf V μ β = p / (p - a)
  apply (eq_div_iff hGapNe).2
  simpa only [mul_comm] using hReal
