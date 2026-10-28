-- Prove2me | solution 1 for FunctionalInequalities.Probability.Posterior.integrable_exp_norm_mul_of_compact_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:03:38.813321+00:00
-- url     : https://prove2.me/submissions/58dfc8ee-fe8d-436d-a9b0-5b45fb2e4263

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_Generator

noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff
section Smooth
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- Under a compact prior, `e^{s‖x‖} ‖e^{E_{0,Q}} f‖` is integrable for every `s` (bounded `f` on the support). -/
theorem solution (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) {f : E → ℝ} (hf : Measurable f)
    {C : ℝ} (_hC : 0 ≤ C) (hfb : ∀ x ∈ (μ : Measure E).support, ‖f x‖ ≤ C)
    (Q : E →L[ℝ] E) (s : ℝ) :
    Integrable (fun x => Real.exp (s * ‖x‖) * ‖Real.exp (FunctionalInequalities.Probability.Posterior.quadraticExponent 0 Q x) * f x‖) (μ : Measure E) := by
  have hφ : Continuous (FunctionalInequalities.Probability.Posterior.quadraticExponent (0 : E) Q) := by unfold FunctionalInequalities.Probability.Posterior.quadraticExponent; fun_prop
  obtain ⟨P, _hP, hp⟩ := FunctionalInequalities.Probability.Posterior.exists_bound_on_support_of_compact μ hc hφ
  obtain ⟨R, _hR, hR⟩ := FunctionalInequalities.Probability.Posterior.exists_bound_on_support_of_compact μ hc
    (continuous_norm : Continuous (fun x : E => ‖x‖))
  have hmeas : Measurable (fun x => Real.exp (s * ‖x‖) * ‖Real.exp (FunctionalInequalities.Probability.Posterior.quadraticExponent 0 Q x) * f x‖) :=
    ((Real.continuous_exp.comp (continuous_norm.const_mul s)).measurable).mul (((Real.continuous_exp.comp hφ).measurable.mul hf).norm)
  apply FunctionalInequalities.Probability.Posterior.integrable_of_bound_on_support μ hmeas (Real.exp (|s| * R + P) * C)
  intro x hx
  have hnorm : ‖x‖ ≤ R := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x)] using hR x hx
  have hleft : s * ‖x‖ ≤ |s| * R :=
    (mul_le_mul_of_nonneg_right (le_abs_self s) (norm_nonneg x)).trans
      (mul_le_mul_of_nonneg_left hnorm (abs_nonneg s))
  have hright : FunctionalInequalities.Probability.Posterior.quadraticExponent 0 Q x ≤ P :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hp x hx)
  change ‖Real.exp (s * ‖x‖) * ‖Real.exp (FunctionalInequalities.Probability.Posterior.quadraticExponent 0 Q x) * f x‖‖ ≤ Real.exp (|s| * R + P) * C
  rw [norm_mul, norm_norm, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← mul_assoc, ← Real.exp_add]
  exact mul_le_mul (Real.exp_le_exp.mpr (add_le_add hleft hright)) (hfb x hx)
    (norm_nonneg _) (Real.exp_nonneg _)
