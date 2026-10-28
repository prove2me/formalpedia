-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.Suspension.scalar_moments_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:20:41.164468+00:00
-- url     : https://prove2.me/submissions/0ae8db4a-d2b2-4e03-b33f-682055822bf0

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Suspension_Moments
import Theorems.Thm_FunctionalInequalities_Probability_pi_normalizedSum_moments_readable
import Theorems.Thm_FunctionalInequalities_Probability_prod_add_moments_readable

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
/-- **The suspension coordinate** `S = (F_N + η)/σ_β` has mean `0` and second moment `1`. -/
theorem solution {n N : ℕ} (hN : 0 < N)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf2 : MemLp f 2 μ)
    (hf0 : ∫ x, f x ∂μ = 0) (hf1 : ∫ x, f x ^ 2 ∂μ = 1)
    {β : ℝ} (hβ : 0 < β) [IsProbabilityMeasure (FunctionalInequalities.Probability.Line.laplaceMeasure β)]
    (hη1 : Integrable (fun s : ℝ => s) (FunctionalInequalities.Probability.Line.laplaceMeasure β))
    (hη2 : Integrable (fun s : ℝ => s ^ 2) (FunctionalInequalities.Probability.Line.laplaceMeasure β))
    (hη0 : ∫ s, s ∂FunctionalInequalities.Probability.Line.laplaceMeasure β = 0) (hηv : ∫ s, s ^ 2 ∂FunctionalInequalities.Probability.Line.laplaceMeasure β = 2 / β ^ 2) :
    MemLp (fun q : (Fin N → EuclideanSpace ℝ (Fin n)) × ℝ =>
      (FunctionalInequalities.KLS.LogConcave.Suspension.copyStat f N q.1 + q.2) / FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) 2
      ((Measure.pi (fun _ : Fin N => μ)).prod (FunctionalInequalities.Probability.Line.laplaceMeasure β)) ∧
      (∫ q : (Fin N → EuclideanSpace ℝ (Fin n)) × ℝ,
        (FunctionalInequalities.KLS.LogConcave.Suspension.copyStat f N q.1 + q.2) / FunctionalInequalities.KLS.LogConcave.Suspension.sigma β
        ∂((Measure.pi (fun _ : Fin N => μ)).prod (FunctionalInequalities.Probability.Line.laplaceMeasure β))) = 0 ∧
      (∫ q : (Fin N → EuclideanSpace ℝ (Fin n)) × ℝ,
        ((FunctionalInequalities.KLS.LogConcave.Suspension.copyStat f N q.1 + q.2) / FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) ^ 2
        ∂((Measure.pi (fun _ : Fin N => μ)).prod (FunctionalInequalities.Probability.Line.laplaceMeasure β))) = 1 := by
  have hF := FunctionalInequalities.KLS.LogConcave.Suspension.copyStat_moments hN μ f hf2 hf0 hf1
  have hηL2 : MemLp (fun s : ℝ => s) 2 (FunctionalInequalities.Probability.Line.laplaceMeasure β) :=
    (memLp_two_iff_integrable_sq_norm hη1.aestronglyMeasurable).mpr
      (by simpa only [Real.norm_eq_abs, sq_abs] using hη2)
  have hsum := FunctionalInequalities.Probability.prod_add_moments_readable (Measure.pi (fun _ : Fin N => μ))
    (FunctionalInequalities.Probability.Line.laplaceMeasure β) (FunctionalInequalities.KLS.LogConcave.Suspension.copyStat f N) (fun s : ℝ => s) hF.1 hηL2 hF.2.1 hη0
  have hβsq : 0 < β ^ 2 := sq_pos_of_pos hβ
  have hsumpos : 0 < 1 + 2 / β ^ 2 := add_pos (by norm_num) (div_pos (by norm_num) hβsq)
  have hσsq : (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) ^ 2 = 1 + 2 / β ^ 2 := by
    exact Real.sq_sqrt hsumpos.le
  have hS2 : MemLp (fun q : (Fin N → EuclideanSpace ℝ (Fin n)) × ℝ =>
      (FunctionalInequalities.KLS.LogConcave.Suspension.copyStat f N q.1 + q.2) / FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) 2
      ((Measure.pi (fun _ : Fin N => μ)).prod (FunctionalInequalities.Probability.Line.laplaceMeasure β)) := by
    simpa [div_eq_mul_inv] using hsum.1.mul_const (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β)⁻¹
  refine ⟨hS2, ?_, ?_⟩
  · rw [integral_div, hsum.2.1]
    simp
  · simp_rw [div_pow]
    rw [integral_div, hsum.2.2, hF.2.2, hηv, hσsq]
    exact div_self hsumpos.ne'
