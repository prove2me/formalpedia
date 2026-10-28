-- Prove2me | solution 1 for AvramDividend.Classical.causal_gaussian_signed_damped_kernel_data
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T19:52:38.589989+00:00
-- url     : https://prove2.me/submissions/1ddc07d0-f3b4-402c-a8bc-4fc9bc9800f1

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Theorems.Thm_AvramDividend_Classical_causal_weighted_kernel_continuous_positive
import Theorems.Thm_AvramDividend_Classical_causal_continuous_kernel_measurable
import Theorems.Thm_AvramDividend_Classical_causal_signed_weighted_kernel_abs_le_envelope

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- The signed damped Gaussian Volterra kernel is causal and envelope-dominated. -/
theorem solution
    (K : ℝ → ℝ) (a β w : ℝ) (ha : 0 < a)
    (hKcont : ContinuousOn K (Ioi (0 : ℝ)))
    (hKnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ K t)
    (hEnvelope : IntegrableOn
      (fun t : ℝ => a⁻¹ * Real.exp (-w * t) * (|β| + K t))
      (Ioi (0 : ℝ)) volume) :
    ∃ k : ℝ → ℝ,
      k = (fun t : ℝ =>
        if 0 < t then -(a⁻¹ * Real.exp (-w * t) * (β + K t)) else 0) ∧
      IntegrableOn k (Ioi (0 : ℝ)) volume ∧
      Measurable k ∧
      ContinuousOn k (Ioi (0 : ℝ)) ∧
      (∀ t : ℝ, t ≤ 0 → k t = 0) ∧
      (∀ t : ℝ, 0 ≤ t →
        |k t| ≤ a⁻¹ * Real.exp (-w * t) * (|β| + K t)) := by
  let k : ℝ → ℝ := fun t =>
    if 0 < t then -(a⁻¹ * Real.exp (-w * t) * (β + K t)) else 0
  let κ : ℝ → ℝ := fun t => a⁻¹ * Real.exp (-w * t) * (|β| + K t)
  have hkzero : ∀ t : ℝ, t ≤ 0 → k t = 0 := by
    intro t ht
    simp [k, not_lt.mpr ht]
  have hkcont : ContinuousOn k (Ioi (0 : ℝ)) := by
    have hraw : ContinuousOn
        (fun t : ℝ => -(a⁻¹) *
          (Real.exp (-w * t) * (β + K t))) (Ioi (0 : ℝ)) :=
      continuousOn_const.mul
        (causal_weighted_kernel_continuous_positive K w β hKcont)
    refine hraw.congr ?_
    intro t ht
    simp [k, (mem_Ioi.mp ht), mul_assoc]
  have hkmeas : Measurable k :=
    causal_continuous_kernel_measurable k hkcont hkzero
  have hkdom : ∀ t : ℝ, 0 ≤ t → |k t| ≤ κ t := by
    intro t ht
    rcases eq_or_lt_of_le ht with hzero | hpos
    · subst t
      have hκ0 : 0 ≤ κ 0 := by
        dsimp [κ]
        exact mul_nonneg
          (mul_nonneg (inv_nonneg.mpr ha.le) (Real.exp_nonneg _))
          (add_nonneg (abs_nonneg _) (hKnonneg 0 le_rfl))
      simpa [k] using hκ0
    · have hbound :=
        causal_signed_weighted_kernel_abs_le_envelope
          K w β a t ha (hKnonneg t hpos.le)
      simpa only [k, κ, if_pos hpos, abs_neg, mul_assoc] using hbound
  have hkint : IntegrableOn k (Ioi (0 : ℝ)) volume := by
    have hAE : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
        ‖k t‖ ≤ κ t := by
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with t ht
      simpa only [Real.norm_eq_abs] using hkdom t ht.le
    exact hEnvelope.mono' hkmeas.aestronglyMeasurable hAE
  exact ⟨k, rfl, hkint, hkmeas, hkcont, hkzero, hkdom⟩
