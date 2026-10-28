-- Prove2me | solution 1 for AvramDividend.Classical.chat04_actual_killed_scale_exp_clock_exponential_domination_ws01a
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T10:29:36.356547+00:00
-- url     : https://prove2.me/submissions/359f86dc-b736-4df7-a38a-ab5844d60d1f

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat03_scale_global_weighted_exponential_bound
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (r : ℝ) (hr : 0 < r)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ : ℝ) (hθ : 0 ≤ θ) (hψ : q < X.ψ θ) (x : ℝ) :
    (∫⁻ z : Ω × ℝ,
      if ∀ s : ℝ≥0, s ≤ Real.toNNReal z.2 → 0 ≤ x + X.X s z.1
      then ENNReal.ofReal (W (x + X.X (Real.toNNReal z.2) z.1))
      else (0 : ℝ≥0∞) ∂(P.prod (ProbabilityTheory.expMeasure r))) ≤
    ENNReal.ofReal (Real.exp θ * (X.ψ θ - q)⁻¹) *
      (∫⁻ z : Ω × ℝ,
        ENNReal.ofReal (Real.exp
          (θ * (x + X.X (Real.toNNReal z.2) z.1)))
        ∂(P.prod (ProbabilityTheory.expMeasure r))) := by
  let C : ℝ := Real.exp θ * (X.ψ θ - q)⁻¹
  have hC : 0 ≤ C := mul_nonneg (Real.exp_nonneg _)
    (inv_nonneg.mpr (le_of_lt (sub_pos.mpr hψ)))
  have hEnvelope (y : ℝ) : W y ≤ C * Real.exp (θ * y) := by
    have h := chat03_scale_global_weighted_exponential_bound
      X q W hW θ y hθ hψ
    calc
      W y = Real.exp (θ * (y + 1)) *
          (Real.exp (-(θ * (y + 1))) * W y) := by
            rw [← mul_assoc, ← Real.exp_add]
            simp
      _ ≤ Real.exp (θ * (y + 1)) * (X.ψ θ - q)⁻¹ :=
        mul_le_mul_of_nonneg_left h (Real.exp_nonneg _)
      _ = C * Real.exp (θ * y) := by
        dsimp [C]
        rw [show θ * (y + 1) = θ * y + θ by ring, Real.exp_add]
        ring
  have hClock : Measurable (fun z : Ω × ℝ =>
      (Real.toNNReal z.2, z.1)) :=
    (measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst
  have hXt : Measurable (fun z : Ω × ℝ =>
      X.X (Real.toNNReal z.2) z.1) :=
    (chat04_levy_joint_time_state_measurable X).comp hClock
  have hExpMeas : Measurable (fun z : Ω × ℝ =>
      ENNReal.ofReal (Real.exp
        (θ * (x + X.X (Real.toNNReal z.2) z.1)))) :=
    ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.measurable.comp
        (measurable_const.mul (measurable_const.add hXt)))
  have hPoint (z : Ω × ℝ) :
      (if ∀ s : ℝ≥0, s ≤ Real.toNNReal z.2 →
           0 ≤ x + X.X s z.1
       then ENNReal.ofReal (W (x + X.X (Real.toNNReal z.2) z.1))
       else (0 : ℝ≥0∞)) ≤ ENNReal.ofReal C *
         ENNReal.ofReal (Real.exp
           (θ * (x + X.X (Real.toNNReal z.2) z.1))) := by
    split_ifs with hs
    · exact (ENNReal.ofReal_le_ofReal (hEnvelope _)).trans
        (le_of_eq (ENNReal.ofReal_mul hC))
    · exact zero_le
  calc
    _ ≤ (∫⁻ z : Ω × ℝ, ENNReal.ofReal C *
        ENNReal.ofReal (Real.exp
          (θ * (x + X.X (Real.toNNReal z.2) z.1)))
        ∂(P.prod (ProbabilityTheory.expMeasure r))) :=
          lintegral_mono hPoint
    _ = _ := by
      rw [lintegral_const_mul]
      exact hExpMeas
