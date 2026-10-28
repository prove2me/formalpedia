-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.Suspension.integral_scalar_mul_inner_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:22:06.882085+00:00
-- url     : https://prove2.me/submissions/fbf0223d-8280-4779-a40a-d098c147b1da

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Suspension_Moments
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_scalar_moments_readable
import Theorems.Thm_FunctionalInequalities_Probability_integral_normalizedSum_mul_comp_eval_pi_readable
import Theorems.Thm_FunctionalInequalities_Probability_integral_prod_add_mul_eq_zero_readable
import Theorems.Thm_FunctionalInequalities_Probability_pi_normalizedSum_moments_readable

noncomputable section
open MeasureTheory ProbabilityTheory FunctionalInequalities.Probability
open FunctionalInequalities.Probability.Line
open scoped RealInnerProductSpace
/-- The copy statistic `F_N = (Σ_i f(X_i))/√N` has mean `0` and second moment `1`. -/
theorem FunctionalInequalities.KLS.LogConcave.Suspension.copyStat_moments {n N : ℕ} (hN : 0 < N)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf2 : MemLp f 2 μ)
    (hf0 : ∫ x, f x ∂μ = 0) (hf1 : ∫ x, f x ^ 2 ∂μ = 1) :
    MemLp (copyStat f N) 2 (Measure.pi (fun _ : Fin N => μ)) ∧
      (∫ x, copyStat f N x ∂(Measure.pi (fun _ : Fin N => μ))) = 0 ∧
      (∫ x, (copyStat f N x) ^ 2 ∂(Measure.pi (fun _ : Fin N => μ))) = 1 := by
  exact pi_normalizedSum_moments_readable μ f hf2 hf0 hf1 N hN
/-- Linear functionals of a law with finite second moment are in `L²`. -/
private theorem FunctionalInequalities.KLS.LogConcave.Suspension.memLp_inner {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] (hμ2 : MemLp id 2 μ) (u : EuclideanSpace ℝ (Fin n)) :
    MemLp (fun x => ⟪u, x⟫) 2 μ := by
  simpa [Function.comp_def] using (innerSL ℝ u).comp_memLp' hμ2
/-- Linear functionals of a centered law are centered. -/
private theorem FunctionalInequalities.KLS.LogConcave.Suspension.integral_inner_eq_zero {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] (hμ2 : MemLp id 2 μ) (hμ0 : ∫ x, x ∂μ = 0)
    (u : EuclideanSpace ℝ (Fin n)) : (∫ x, ⟪u, x⟫ ∂μ) = 0 := by
  calc
    _ = ⟪u, ∫ x, x ∂μ⟫ :=
      (innerSL ℝ u).integral_comp_comm (hμ2.integrable one_le_two)
    _ = 0 := by rw [hμ0]; simp
/-- `E[F_N ⟪u, X_i⟫] = 0` when `f` is orthogonal to the linear functions. -/
theorem FunctionalInequalities.KLS.LogConcave.Suspension.integral_copyStat_mul_inner {n N : ℕ} (hN : 0 < N)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) (hμ0 : ∫ x, x ∂μ = 0)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf2 : MemLp f 2 μ)
    (hf0 : ∫ x, f x ∂μ = 0)
    (hfx : ∀ u, ∫ x, ⟪u, x⟫ * f x ∂μ = 0)
    (i : Fin N) (u : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun x : Fin N → EuclideanSpace ℝ (Fin n) => copyStat f N x * ⟪u, x i⟫)
      (Measure.pi (fun _ : Fin N => μ)) ∧
      (∫ x : Fin N → EuclideanSpace ℝ (Fin n), copyStat f N x * ⟪u, x i⟫
        ∂(Measure.pi (fun _ : Fin N => μ))) = 0 := by
  have hfg : (∫ x, f x * ⟪u, x⟫ ∂μ) = 0 := by
    calc
      _ = ∫ x, ⟪u, x⟫ * f x ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall fun _ => mul_comm _ _)
      _ = 0 := hfx u
  exact integral_normalizedSum_mul_comp_eval_pi_readable μ f (fun x => ⟪u, x⟫) hf2
    (memLp_inner μ hμ2 u) hf0 (integral_inner_eq_zero μ hμ2 hμ0 u) hfg N hN i
/-- `E[S ⟪u, X_i⟫] = 0`. -/
theorem solution {n N : ℕ} (hN : 0 < N)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) (hμ0 : ∫ x, x ∂μ = 0)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf2 : MemLp f 2 μ)
    (hf0 : ∫ x, f x ∂μ = 0) (hf1 : ∫ x, f x ^ 2 ∂μ = 1)
    (hfx : ∀ u, ∫ x, ⟪u, x⟫ * f x ∂μ = 0)
    {β : ℝ} (hβ : 0 < β) [IsProbabilityMeasure (FunctionalInequalities.Probability.Line.laplaceMeasure β)]
    (hη1 : Integrable (fun s : ℝ => s) (FunctionalInequalities.Probability.Line.laplaceMeasure β))
    (hη2 : Integrable (fun s : ℝ => s ^ 2) (FunctionalInequalities.Probability.Line.laplaceMeasure β))
    (hη0 : ∫ s, s ∂FunctionalInequalities.Probability.Line.laplaceMeasure β = 0) (hηv : ∫ s, s ^ 2 ∂FunctionalInequalities.Probability.Line.laplaceMeasure β = 2 / β ^ 2)
    (i : Fin N) (u : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun q : (Fin N → EuclideanSpace ℝ (Fin n)) × ℝ =>
      ((FunctionalInequalities.KLS.LogConcave.Suspension.copyStat f N q.1 + q.2) / FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) * ⟪u, q.1 i⟫)
      ((Measure.pi (fun _ : Fin N => μ)).prod (FunctionalInequalities.Probability.Line.laplaceMeasure β)) ∧
      (∫ q : (Fin N → EuclideanSpace ℝ (Fin n)) × ℝ,
        ((FunctionalInequalities.KLS.LogConcave.Suspension.copyStat f N q.1 + q.2) / FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) * ⟪u, q.1 i⟫
        ∂((Measure.pi (fun _ : Fin N => μ)).prod (FunctionalInequalities.Probability.Line.laplaceMeasure β))) = 0 := by
  have hF := FunctionalInequalities.KLS.LogConcave.Suspension.copyStat_moments hN μ f hf2 hf0 hf1
  have hS := FunctionalInequalities.KLS.LogConcave.Suspension.scalar_moments_readable hN μ f hf2 hf0 hf1 hβ hη1 hη2 hη0 hηv
  have hZμ2 : MemLp (fun x => ⟪u, x⟫) 2 μ := by
    simpa [Function.comp_def] using (innerSL ℝ u).comp_memLp' hμ2
  have hZ2 : MemLp (fun x : Fin N → EuclideanSpace ℝ (Fin n) => ⟪u, x i⟫) 2
      (Measure.pi (fun _ : Fin N => μ)) :=
    hZμ2.comp_measurePreserving (measurePreserving_eval (fun _ : Fin N => μ) i)
  have hZprod2 := hZ2.comp_fst (FunctionalInequalities.Probability.Line.laplaceMeasure β)
  have hprod : MemLp (fun q : (Fin N → EuclideanSpace ℝ (Fin n)) × ℝ =>
      ((FunctionalInequalities.KLS.LogConcave.Suspension.copyStat f N q.1 + q.2) / FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) * ⟪u, q.1 i⟫) 1
      ((Measure.pi (fun _ : Fin N => μ)).prod (FunctionalInequalities.Probability.Line.laplaceMeasure β)) :=
    hZprod2.mul' hS.1
  have hηL2 : MemLp (fun s : ℝ => s) 2 (FunctionalInequalities.Probability.Line.laplaceMeasure β) :=
    (memLp_two_iff_integrable_sq_norm hη1.aestronglyMeasurable).mpr
      (by simpa only [Real.norm_eq_abs, sq_abs] using hη2)
  have hCX := FunctionalInequalities.KLS.LogConcave.Suspension.integral_copyStat_mul_inner hN μ hμ2 hμ0 f hf2 hf0 hfx i u
  have hbase := FunctionalInequalities.Probability.integral_prod_add_mul_eq_zero_readable (Measure.pi (fun _ : Fin N => μ)) (FunctionalInequalities.Probability.Line.laplaceMeasure β)
    (FunctionalInequalities.KLS.LogConcave.Suspension.copyStat f N) (fun x => ⟪u, x i⟫) (fun s : ℝ => s) hF.1 hZ2 hηL2 hCX.2 hη0
  refine ⟨hprod.integrable le_rfl, ?_⟩
  have heq : (fun q : (Fin N → EuclideanSpace ℝ (Fin n)) × ℝ =>
      ((FunctionalInequalities.KLS.LogConcave.Suspension.copyStat f N q.1 + q.2) / FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) * ⟪u, q.1 i⟫) =
      (fun q => ((FunctionalInequalities.KLS.LogConcave.Suspension.copyStat f N q.1 + q.2) * ⟪u, q.1 i⟫) / FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) := by
    funext q
    ring
  rw [heq, integral_div, hbase.2]
  simp
