-- Prove2me | solution 1 for AvramDividend.Classical.causal_weighted_BCF_operator_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T10:14:28.610779+00:00
-- url     : https://prove2.me/submissions/277e3d2c-d09a-4b30-b129-edc679a6c129

import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Theorems.Thm_AvramDividend_Classical_causal_weighted_volterra_strict_operator_bound
import Theorems.Thm_AvramDividend_Classical_causal_weighted_BCF_extension_continuous
import Theorems.Thm_AvramDividend_Classical_causal_weighted_BCF_local_bound
import Theorems.Thm_AvramDividend_Classical_causal_weighted_BCF_pointwise_norm_bound
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The weighted causal operator has BCF operator norm strictly below a. -/
theorem solution
    (K : ℝ → ℝ) (f : BoundedContinuousFunction ℝ≥0 ℝ)
    (a β w : ℝ) (ha : 0 < a) (hw : 0 < w)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hsmall : |β| / w +
      (∫ t in Ioi (0 : ℝ), |K t| * Real.exp (-w * t) ∂volume) < a) :
    ∃ m : ℝ, 0 ≤ m ∧ m < a ∧
      ∀ (R x : ℝ) (hR : 0 < R) (hx : x ∈ Ioc (0 : ℝ) R),
        Real.exp (-(w * x)) *
          |∫ s in Ioc (0 : ℝ) x, (β + K (x - s)) *
            (Real.exp (w * s) * f ⟨max s 0, le_max_right s 0⟩) ∂volume| ≤
          ‖f‖ * m := by
  let V : ℝ → ℝ := fun s => Real.exp (w * s) *
    f ⟨max s 0, le_max_right s 0⟩
  have hVc : ContinuousOn V (Ioi (0 : ℝ)) :=
    (causal_weighted_BCF_extension_continuous f w).continuousOn
  have hVb : ∀ R : ℝ, 0 < R →
      ∃ C : ℝ, ∀ s : ℝ, s ∈ Ioc (0 : ℝ) R → |V s| ≤ C := by
    intro R hR
    exact causal_weighted_BCF_local_bound f w R hR
  obtain ⟨m, hm0, hma, hBound⟩ :=
    causal_weighted_volterra_strict_operator_bound
      K V a β w ha hw hK hsmall hVc hVb
  refine ⟨m, hm0, hma, ?_⟩
  intro R x hR hx
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
          Real.exp (-(w * t)) * |V t|) '' Ioc (0 : ℝ) R) * m :=
      hBound R x hR hx
    _ ≤ ‖f‖ * m := mul_le_mul_of_nonneg_right hSup hm0
