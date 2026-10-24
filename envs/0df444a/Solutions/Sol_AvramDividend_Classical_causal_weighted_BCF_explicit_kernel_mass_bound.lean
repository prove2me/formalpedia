-- Prove2me | solution 1 for AvramDividend.Classical.causal_weighted_BCF_explicit_kernel_mass_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T07:22:23.826055+00:00
-- url     : https://prove2.me/submissions/e4b5815b-2f67-4ad0-b6dc-55f744f1e0f2

import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Theorems.Thm_AvramDividend_Classical_causal_weighted_volterra_operator_bound
import Theorems.Thm_AvramDividend_Classical_positive_weighted_full_kernel_norm_small
import Theorems.Thm_AvramDividend_Classical_causal_l1_exponential_damping_integrable
import Theorems.Thm_AvramDividend_Classical_causal_weighted_BCF_extension_continuous
import Theorems.Thm_AvramDividend_Classical_causal_weighted_BCF_local_bound
import Theorems.Thm_AvramDividend_Classical_causal_weighted_BCF_pointwise_norm_bound
import Mathlib.Analysis.Complex.Exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The same explicit strict kernel mass controls every weighted BCF input. -/
theorem solution
    (K : ℝ → ℝ) (a β w : ℝ) (ha : 0 < a) (hw : 0 < w)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hsmall : |β| / w +
      (∫ t in Ioi (0 : ℝ), |K t| * Real.exp (-w * t) ∂volume) < a) :
    let m := ∫ t in Ioi (0 : ℝ),
      Real.exp (-w * t) * |β + K t| ∂volume
    0 ≤ m ∧ m < a ∧
      ∀ (f : BoundedContinuousFunction ℝ≥0 ℝ)
        (R x : ℝ) (hR : 0 < R) (hx : x ∈ Ioc (0 : ℝ) R),
        Real.exp (-(w * x)) *
          |∫ s in Ioc (0 : ℝ) x, (β + K (x - s)) *
            (Real.exp (w * s) * f ⟨max s 0, le_max_right s 0⟩) ∂volume| ≤
          ‖f‖ * m := by
  dsimp
  obtain ⟨hLi, hma⟩ := positive_weighted_full_kernel_norm_small
    K a β w hw (causal_l1_exponential_damping_integrable K w hw hK) hsmall
  have hm0 : 0 ≤ ∫ t in Ioi (0 : ℝ),
      Real.exp (-w * t) * |β + K t| ∂volume := by
    apply integral_nonneg
    intro t
    exact mul_nonneg (Real.exp_pos _).le (abs_nonneg _)
  refine ⟨hm0, hma, ?_⟩
  intro f R x hR hx
  let V : ℝ → ℝ := fun s => Real.exp (w * s) *
    f ⟨max s 0, le_max_right s 0⟩
  have hVc : ContinuousOn V (Ioi (0 : ℝ)) :=
    (causal_weighted_BCF_extension_continuous f w).continuousOn
  have hVb : ∀ R : ℝ, 0 < R →
      ∃ C : ℝ, ∀ s : ℝ, s ∈ Ioc (0 : ℝ) R → |V s| ≤ C := by
    intro r hr
    exact causal_weighted_BCF_local_bound f w r hr
  have hbase := causal_weighted_volterra_operator_bound
    K V β w hw.le hK hVc hVb hLi R x hR hx
  have hSup : sSup ((fun t : ℝ =>
      Real.exp (-(w * t)) * |V t|) '' Ioc (0 : ℝ) R) ≤ ‖f‖ := by
    apply csSup_le
    · refine ⟨Real.exp (-(w * R)) * |V R|, ?_⟩
      exact ⟨R, ⟨hR, le_refl R⟩, rfl⟩
    · intro y hy
      rcases hy with ⟨t, ht, rfl⟩
      exact causal_weighted_BCF_pointwise_norm_bound f w t
  calc
    _ ≤ sSup ((fun t : ℝ =>
          Real.exp (-(w * t)) * |V t|) '' Ioc (0 : ℝ) R) *
          (∫ t in Ioi (0 : ℝ), Real.exp (-w * t) * |β + K t| ∂volume) :=
      hbase
    _ ≤ ‖f‖ *
          (∫ t in Ioi (0 : ℝ), Real.exp (-w * t) * |β + K t| ∂volume) :=
      mul_le_mul_of_nonneg_right hSup hm0
