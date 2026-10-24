-- Prove2me | solution 1 for AvramDividend.Classical.causal_weighted_volterra_strict_operator_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T06:53:09.043565+00:00
-- url     : https://prove2.me/submissions/6d6e50d4-5340-4edd-9e77-1ca70e14240b

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_AvramDividend_Classical_causal_l1_exponential_damping_integrable
import Theorems.Thm_AvramDividend_Classical_positive_weighted_full_kernel_norm_small
import Theorems.Thm_AvramDividend_Classical_causal_weighted_volterra_operator_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- A strict weighted full-kernel mass uniformly controls the causal operator. -/
theorem solution
    (K V : ℝ → ℝ) (a β w : ℝ)
    (ha : 0 < a) (hw : 0 < w)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hsmall : |β| / w + (∫ t in Ioi (0 : ℝ), |K t| * Real.exp (-w * t) ∂volume) < a)
    (hVc : ContinuousOn V (Ioi (0 : ℝ)))
    (hVb : ∀ R : ℝ, 0 < R → ∃ C : ℝ, ∀ s : ℝ, s ∈ Ioc (0 : ℝ) R → |V s| ≤ C) :
    ∃ m : ℝ, 0 ≤ m ∧ m < a ∧
      ∀ (R x : ℝ) (hR : 0 < R) (hx : x ∈ Ioc (0 : ℝ) R),
        Real.exp (-(w * x)) *
          |∫ s in Ioc (0 : ℝ) x, (β + K (x - s)) * V s ∂volume| ≤
        sSup ((fun t : ℝ => Real.exp (-(w * t)) * |V t|) '' Ioc (0 : ℝ) R) * m := by
  have hKi :=
    AvramDividend.Classical.causal_l1_exponential_damping_integrable K w hw hK
  obtain ⟨hLi, hm⟩ :=
    AvramDividend.Classical.positive_weighted_full_kernel_norm_small
      K a β w hw hKi hsmall
  let m : ℝ := ∫ t in Ioi (0 : ℝ),
    Real.exp (-w * t) * |β + K t| ∂volume
  refine ⟨m, ?_, hm, ?_⟩
  · dsimp [m]
    apply MeasureTheory.integral_nonneg
    intro t
    exact mul_nonneg (Real.exp_nonneg _) (abs_nonneg _)
  · intro R x hR hx
    exact AvramDividend.Classical.causal_weighted_volterra_operator_bound
      K V β w hw.le hK hVc hVb hLi R x hR hx
