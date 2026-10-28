-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.Suspension.logLaplace_jointLaw_factorization_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:23:40.323781+00:00
-- url     : https://prove2.me/submissions/34cfa398-961a-4bd0-804d-5576af98f21e

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Suspension_Cumulant
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_joint_integrability_factorization_readable

noncomputable section
open MeasureTheory FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Analysis.Tensor
open FunctionalInequalities.Probability.Line
open scoped RealInnerProductSpace
/-- The real logarithmic Laplace factorization at any genuinely integrable joint parameter. -/
theorem solution {n N : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f)
    {β : ℝ} (hβ : 0 < β) (hN : 0 < N) (z : FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n)
    (hInt : Integrable (fun p => Real.exp ⟪z, p⟫) (FunctionalInequalities.KLS.LogConcave.Suspension.jointLaw μ f β (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) N)) :
    FunctionalInequalities.Analysis.BakryEmery.logLaplace (FunctionalInequalities.KLS.LogConcave.Suspension.jointLaw μ f β (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) N) z =
      Real.log (∫ s : ℝ, Real.exp (z none / FunctionalInequalities.KLS.LogConcave.Suspension.sigma β * s) ∂FunctionalInequalities.Probability.Line.laplaceMeasure β) +
        ∑ i : Fin N, Real.log (∫ x, Real.exp
          (z none / (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β * Real.sqrt N) * f x +
            ⟪(WithLp.toLp 2 fun j => z (some (i, j)) : EuclideanSpace ℝ (Fin n)), x⟫) ∂μ) := by
  let _ : IsProbabilityMeasure (FunctionalInequalities.Probability.Line.laplaceMeasure β) := FunctionalInequalities.Probability.Line.isProbabilityMeasure_laplaceMeasure hβ
  obtain ⟨hNoise, hCopy, hreal⟩ := FunctionalInequalities.KLS.LogConcave.Suspension.joint_integrability_factorization_readable μ hf hβ hN z hInt
  have hNoisepos : 0 < ∫ s : ℝ, Real.exp (z none / FunctionalInequalities.KLS.LogConcave.Suspension.sigma β * s) ∂FunctionalInequalities.Probability.Line.laplaceMeasure β :=
    integral_exp_pos hNoise
  have hCopypos (i : Fin N) : 0 < ∫ x, Real.exp
      (z none / (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β * Real.sqrt N) * f x +
        ⟪(WithLp.toLp 2 fun j => z (some (i, j)) : EuclideanSpace ℝ (Fin n)), x⟫) ∂μ :=
    integral_exp_pos (hCopy i)
  have hprod : (∏ i : Fin N, ∫ x, Real.exp
      (z none / (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β * Real.sqrt N) * f x +
        ⟪(WithLp.toLp 2 fun j => z (some (i, j)) : EuclideanSpace ℝ (Fin n)), x⟫) ∂μ) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => (hCopypos i).ne')
  rw [FunctionalInequalities.Analysis.BakryEmery.logLaplace, hreal,
    Real.log_mul hNoisepos.ne' hprod, Real.log_prod (fun i _ => (hCopypos i).ne')]
