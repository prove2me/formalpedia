-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.Suspension.jointLaw_moments_of_laplace_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:23:22.333503+00:00
-- url     : https://prove2.me/submissions/b63e3358-e6a5-45dd-b115-5f785d4ab896

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Product
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Suspension_Moments
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_integral_scalar_mul_inner_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_scalar_moments_readable
import Theorems.Thm_FunctionalInequalities_Probability_integral_mul_comp_eval_pi_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_euclideanMomentsFromCoordinates_readable

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
section MeasurableSpace
variable {E : Type*}
variable [MeasurableSpace E]
/-- A coordinate of `μ^N` has law `μ`. -/
theorem FunctionalInequalities.Probability.integral_comp_eval_pi
    (μ : Measure E) [IsProbabilityMeasure μ] (a : E → ℝ)
    (ha : AEStronglyMeasurable a μ) (N : ℕ) (i : Fin N) :
    (∫ x : Fin N → E, a (x i) ∂(Measure.pi (fun _ : Fin N => μ))) = ∫ x, a x ∂μ := by
  have he := measurePreserving_eval (fun _ : Fin N => μ) i
  have hm : AEStronglyMeasurable a
      ((Measure.pi (fun _ : Fin N => μ)).map (Function.eval i)) := by
    rw [he.map_eq]
    exact ha
  calc
    _ = ∫ x, a x ∂((Measure.pi (fun _ : Fin N => μ)).map (Function.eval i)) :=
      (integral_map he.measurable.aemeasurable hm).symm
    _ = ∫ x, a x ∂μ := by rw [he.map_eq]
end MeasurableSpace
end
end

noncomputable section
open MeasureTheory ProbabilityTheory FunctionalInequalities.Probability
open FunctionalInequalities.Probability.Line
open scoped RealInnerProductSpace
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
/-- `E[⟪u, X_i⟫ ⟪v, X_j⟫] = δ_ij ⟪u, v⟫` for independent isotropic copies. -/
theorem FunctionalInequalities.KLS.LogConcave.Suspension.integral_inner_mul_inner_pi {n N : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) (hμ0 : ∫ x, x ∂μ = 0)
    (hμcov : ∀ u v : EuclideanSpace ℝ (Fin n),
      ∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂μ = ⟪u, v⟫)
    (i j : Fin N) (u v : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun x : Fin N → EuclideanSpace ℝ (Fin n) => ⟪u, x i⟫ * ⟪v, x j⟫)
      (Measure.pi (fun _ : Fin N => μ)) ∧
      (∫ x : Fin N → EuclideanSpace ℝ (Fin n), ⟪u, x i⟫ * ⟪v, x j⟫
        ∂(Measure.pi (fun _ : Fin N => μ))) = if i = j then ⟪u, v⟫ else 0 := by
  classical
  have h := integral_mul_comp_eval_pi_readable μ (fun x => ⟪u, x⟫) (fun x => ⟪v, x⟫)
    (memLp_inner μ hμ2 u) (memLp_inner μ hμ2 v) N i j
  refine ⟨h.1, ?_⟩
  rw [h.2, hμcov u v, integral_inner_eq_zero μ hμ2 hμ0 u, integral_inner_eq_zero μ hμ2 hμ0 v]
  simp
/-- **Second moments of the joint law** (BKL p. 28, isotropy from (108)): under the explicit Laplace
moment data, the joint law of `(S, X₁, …, X_N)` has finite second moment, mean `0` and identity
covariance.
-/
theorem solution {n N : ℕ} (hN : 0 < N)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) (hμ0 : ∫ x, x ∂μ = 0)
    (hμcov : ∀ u v : EuclideanSpace ℝ (Fin n), ∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂μ = ⟪u, v⟫)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f) (hf2 : MemLp f 2 μ)
    (hf0 : ∫ x, f x ∂μ = 0) (hf1 : ∫ x, f x ^ 2 ∂μ = 1) (hfx : ∀ u, ∫ x, ⟪u, x⟫ * f x ∂μ = 0)
    {β : ℝ} (hβ : 0 < β) [IsProbabilityMeasure (FunctionalInequalities.Probability.Line.laplaceMeasure β)]
    (hη1 : Integrable (fun s : ℝ => s) (FunctionalInequalities.Probability.Line.laplaceMeasure β))
    (hη2 : Integrable (fun s : ℝ => s ^ 2) (FunctionalInequalities.Probability.Line.laplaceMeasure β))
    (hη0 : ∫ s, s ∂FunctionalInequalities.Probability.Line.laplaceMeasure β = 0) (hηv : ∫ s, s ^ 2 ∂FunctionalInequalities.Probability.Line.laplaceMeasure β = 2 / β ^ 2) :
    MemLp id 2 (FunctionalInequalities.KLS.LogConcave.Suspension.jointLaw μ f β (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) N) ∧ ∫ p, p ∂(FunctionalInequalities.KLS.LogConcave.Suspension.jointLaw μ f β (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) N) = 0 ∧
      ∀ u v : FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n, ∫ p, ⟪u, p⟫ * ⟪v, p⟫ ∂(FunctionalInequalities.KLS.LogConcave.Suspension.jointLaw μ f β (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) N) = ⟪u, v⟫ := by
  classical
  let ν := Measure.pi (fun _ : Fin N => μ)
  let P := ν.prod (FunctionalInequalities.Probability.Line.laplaceMeasure β)
  let Y : ((Fin N → EuclideanSpace ℝ (Fin n)) × ℝ) → FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n :=
    FunctionalInequalities.KLS.LogConcave.Suspension.embed f (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) N
  have hYmeas : Measurable Y := by
    have hg : Measurable
        (fun q : (Fin N → EuclideanSpace ℝ (Fin n)) × ℝ =>
          fun o : Option (Fin N × Fin n) =>
            o.elim ((FunctionalInequalities.KLS.LogConcave.Suspension.copyStat f N q.1 + q.2) / FunctionalInequalities.KLS.LogConcave.Suspension.sigma β)
              (fun ij => (q.1 ij.1).ofLp ij.2)) := by
      rw [measurable_pi_iff]
      intro o
      cases o with
      | none => unfold FunctionalInequalities.KLS.LogConcave.Suspension.copyStat; measurability
      | some ij => measurability
    exact (WithLp.measurable_toLp 2 _).comp hg
  have hS := FunctionalInequalities.KLS.LogConcave.Suspension.scalar_moments_readable hN μ f hf2 hf0 hf1
    hβ hη1 hη2 hη0 hηv
  have hcoord2 (o : Option (Fin N × Fin n)) : MemLp (fun q => Y q o) 2 P := by
    cases o with
    | none => exact hS.1
    | some ij =>
        have hB2 : MemLp (fun x : EuclideanSpace ℝ (Fin n) => x ij.2) 2 μ := by
          exact (EuclideanSpace.proj ij.2 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).comp_memLp' hμ2
        have hXi2 : MemLp (fun x : Fin N → EuclideanSpace ℝ (Fin n) => x ij.1 ij.2) 2 ν :=
          hB2.comp_measurePreserving (measurePreserving_eval (fun _ : Fin N => μ) ij.1)
        exact hXi2.comp_fst (FunctionalInequalities.Probability.Line.laplaceMeasure β)
  have hcoord0 (o : Option (Fin N × Fin n)) : (∫ q, Y q o ∂P) = 0 := by
    cases o with
    | none => exact hS.2.1
    | some ij =>
        have hB2 : MemLp (fun x : EuclideanSpace ℝ (Fin n) => x ij.2) 2 μ :=
          (EuclideanSpace.proj ij.2 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).comp_memLp' hμ2
        have hB0 : (∫ x : EuclideanSpace ℝ (Fin n), x ij.2 ∂μ) = 0 := by
          have h := (EuclideanSpace.proj ij.2 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).integral_comp_comm
            (hμ2.integrable one_le_two)
          simpa [hμ0] using h
        have hXi0 : (∫ x : Fin N → EuclideanSpace ℝ (Fin n), x ij.1 ij.2 ∂ν) = 0 := by
          rw [FunctionalInequalities.Probability.integral_comp_eval_pi μ (fun x => x ij.2) hB2.aestronglyMeasurable N ij.1]
          exact hB0
        change (∫ q : (Fin N → EuclideanSpace ℝ (Fin n)) × ℝ, q.1 ij.1 ij.2 ∂P) = 0
        rw [integral_fun_fst (fun x : Fin N → EuclideanSpace ℝ (Fin n) => x ij.1 ij.2), hXi0]
        simp
  have hcoordcov (o r : Option (Fin N × Fin n)) :
      (∫ q, Y q o * Y q r ∂P) = if o = r then 1 else 0 := by
    cases o with
    | none =>
        cases r with
        | none =>
            change (∫ q : (Fin N → EuclideanSpace ℝ (Fin n)) × ℝ,
              ((FunctionalInequalities.KLS.LogConcave.Suspension.copyStat f N q.1 + q.2) / FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) *
                ((FunctionalInequalities.KLS.LogConcave.Suspension.copyStat f N q.1 + q.2) / FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) ∂P) = 1
            simpa only [pow_two] using hS.2.2
        | some ij =>
            have h := FunctionalInequalities.KLS.LogConcave.Suspension.integral_scalar_mul_inner_readable hN μ hμ2 hμ0 f hf2 hf0 hf1
              hfx hβ hη1 hη2 hη0 hηv ij.1 (EuclideanSpace.basisFun (Fin n) ℝ ij.2)
            change (∫ q : (Fin N → EuclideanSpace ℝ (Fin n)) × ℝ,
              ((FunctionalInequalities.KLS.LogConcave.Suspension.copyStat f N q.1 + q.2) / FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) * q.1 ij.1 ij.2 ∂P) = 0
            simpa only [EuclideanSpace.basisFun_inner] using h.2
    | some ij =>
        cases r with
        | none =>
            have h := FunctionalInequalities.KLS.LogConcave.Suspension.integral_scalar_mul_inner_readable hN μ hμ2 hμ0 f hf2 hf0 hf1
              hfx hβ hη1 hη2 hη0 hηv ij.1 (EuclideanSpace.basisFun (Fin n) ℝ ij.2)
            change (∫ q : (Fin N → EuclideanSpace ℝ (Fin n)) × ℝ,
              q.1 ij.1 ij.2 * ((FunctionalInequalities.KLS.LogConcave.Suspension.copyStat f N q.1 + q.2) / FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) ∂P) = 0
            calc
              _ = ∫ q : (Fin N → EuclideanSpace ℝ (Fin n)) × ℝ,
                  ((FunctionalInequalities.KLS.LogConcave.Suspension.copyStat f N q.1 + q.2) / FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) * q.1 ij.1 ij.2 ∂P :=
                    integral_congr_ae (Filter.Eventually.of_forall fun _ => mul_comm _ _)
              _ = 0 := by simpa only [EuclideanSpace.basisFun_inner] using h.2
        | some kl =>
            let b := EuclideanSpace.basisFun (Fin n) ℝ
            have h := FunctionalInequalities.KLS.LogConcave.Suspension.integral_inner_mul_inner_pi μ hμ2 hμ0 hμcov ij.1 kl.1 (b ij.2) (b kl.2)
            have hraw : (∫ x : Fin N → EuclideanSpace ℝ (Fin n), x ij.1 ij.2 * x kl.1 kl.2 ∂ν) =
                if ij.1 = kl.1 then ⟪b ij.2, b kl.2⟫ else 0 := by
              simpa only [b, EuclideanSpace.basisFun_inner] using h.2
            change (∫ q : (Fin N → EuclideanSpace ℝ (Fin n)) × ℝ,
              q.1 ij.1 ij.2 * q.1 kl.1 kl.2 ∂P) = if some ij = some kl then 1 else 0
            rw [integral_fun_fst (fun x : Fin N → EuclideanSpace ℝ (Fin n) =>
              x ij.1 ij.2 * x kl.1 kl.2), hraw]
            have hmass : (FunctionalInequalities.Probability.Line.laplaceMeasure β).real Set.univ = 1 := by simp
            rw [hmass, one_smul]
            rw [b.inner_eq_ite]
            by_cases hik : ij.1 = kl.1 <;> by_cases hjl : ij.2 = kl.2 <;>
              simp [Prod.ext_iff, hik, hjl]
  have hbase := FunctionalInequalities.KLS.LogConcave.Suspension.euclideanMomentsFromCoordinates_readable P Y hYmeas hcoord2 hcoord0 hcoordcov
  have hmap2 : MemLp id 2 (P.map Y) := by
    apply (memLp_map_measure_iff (continuous_id.aestronglyMeasurable)
      hYmeas.aemeasurable).mpr
    exact hbase.1
  refine ⟨hmap2, ?_, ?_⟩
  · change (∫ p : FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n, p ∂P.map Y) = 0
    have hm : AEStronglyMeasurable (fun p : FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n => p) (P.map Y) :=
      continuous_id.aestronglyMeasurable
    exact (integral_map hYmeas.aemeasurable hm).trans hbase.2.1
  · intro u v
    change (∫ p : FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n, ⟪u, p⟫ * ⟪v, p⟫ ∂P.map Y) = ⟪u, v⟫
    have hm : AEStronglyMeasurable (fun p : FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n => ⟪u, p⟫ * ⟪v, p⟫) (P.map Y) := by
      exact (show Continuous (fun p : FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n => ⟪u, p⟫ * ⟪v, p⟫) by fun_prop).aestronglyMeasurable
    rw [integral_map hYmeas.aemeasurable hm]
    exact hbase.2.2 u v
