-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.Suspension.lintegral_exp_inner_jointLaw_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:20:50.883001+00:00
-- url     : https://prove2.me/submissions/9100c011-fa03-45ff-8f56-8cff291d7e1c

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Suspension_Cumulant
import Theorems.Thm_FunctionalInequalities_Probability_lintegral_pi_prod_fin_readable

noncomputable section
open MeasureTheory FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Analysis.Tensor
open FunctionalInequalities.Probability.Line
open scoped RealInnerProductSpace
/-- **Factorization of the joint Laplace transform** (BKL p. 28), in extended nonnegative form:
`∫⁻ e^{⟪z, p⟫} dν = (∫⁻ e^{(z₀/σ) s} dη_β) · Π_i ∫⁻ e^{(z₀/(σ√N)) f + ⟪z_i, x⟫} dμ`. -/
theorem solution {n N : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [SigmaFinite μ] {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f) (β σ : ℝ)
    [SigmaFinite (FunctionalInequalities.Probability.Line.laplaceMeasure β)] (z : FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n) :
    ∫⁻ p, ENNReal.ofReal (Real.exp ⟪z, p⟫) ∂(FunctionalInequalities.KLS.LogConcave.Suspension.jointLaw μ f β σ N) =
      (∫⁻ s, ENNReal.ofReal (Real.exp (z none / σ * s)) ∂FunctionalInequalities.Probability.Line.laplaceMeasure β) *
        ∏ i : Fin N, ∫⁻ x, ENNReal.ofReal (Real.exp (z none / (σ * Real.sqrt N) * f x +
          ⟪(WithLp.toLp 2 fun j => z (some (i, j)) : EuclideanSpace ℝ (Fin n)), x⟫)) ∂μ := by
    classical
    have hinner :
        ∀ (x : Fin N → EuclideanSpace ℝ (Fin n)) (s : ℝ),
          ⟪z, FunctionalInequalities.KLS.LogConcave.Suspension.embed f σ N (x, s)⟫ =
            z none / σ * s +
              ∑ i : Fin N,
                (z none / (σ * Real.sqrt N) * f (x i) +
                  ⟪(WithLp.toLp 2 fun j => z (some (i, j)) :
                      EuclideanSpace ℝ (Fin n)), x i⟫) := by
      intro x s
      simp only [FunctionalInequalities.KLS.LogConcave.Suspension.embed, FunctionalInequalities.KLS.LogConcave.Suspension.copyStat, PiLp.inner_apply, Fintype.sum_option,
        Fintype.sum_prod_type, Option.elim_none, Option.elim_some,
        Real.inner_apply, div_eq_mul_inv, mul_inv_rev]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      ring

    have hintegrand :
        ∀ (x : Fin N → EuclideanSpace ℝ (Fin n)) (s : ℝ),
          ENNReal.ofReal (Real.exp ⟪z, FunctionalInequalities.KLS.LogConcave.Suspension.embed f σ N (x, s)⟫) =
            ENNReal.ofReal (Real.exp (z none / σ * s)) *
              ∏ i : Fin N, ENNReal.ofReal (Real.exp
                (z none / (σ * Real.sqrt N) * f (x i) +
                  ⟪(WithLp.toLp 2 fun j => z (some (i, j)) :
                      EuclideanSpace ℝ (Fin n)), x i⟫)) := by
      intro x s
      rw [hinner, Real.exp_add, Real.exp_sum,
        ENNReal.ofReal_mul (Real.exp_pos _).le]
      have hfin :
          ENNReal.ofReal
              (∏ i : Fin N, Real.exp
                (z none / (σ * Real.sqrt N) * f (x i) +
                  ⟪(WithLp.toLp 2 fun j => z (some (i, j)) :
                      EuclideanSpace ℝ (Fin n)), x i⟫)) =
            ∏ i : Fin N, ENNReal.ofReal (Real.exp
                (z none / (σ * Real.sqrt N) * f (x i) +
                  ⟪(WithLp.toLp 2 fun j => z (some (i, j)) :
                      EuclideanSpace ℝ (Fin n)), x i⟫)) := by
        simpa using
          (ENNReal.ofReal_prod_of_nonneg
            (s := (Finset.univ : Finset (Fin N)))
            (fun i _ => (Real.exp_pos
              (z none / (σ * Real.sqrt N) * f (x i) +
                ⟪(WithLp.toLp 2 fun j => z (some (i, j)) :
                    EuclideanSpace ℝ (Fin n)), x i⟫)).le))
      rw [hfin]

    have hmeas :
        Measurable (FunctionalInequalities.KLS.LogConcave.Suspension.embed f σ N) := by
      have hg :
          Measurable (fun q : (Fin N → EuclideanSpace ℝ (Fin n)) × ℝ =>
            fun o : Option (Fin N × Fin n) =>
              o.elim ((FunctionalInequalities.KLS.LogConcave.Suspension.copyStat f N q.1 + q.2) / σ)
                (fun ij => (q.1 ij.1).ofLp ij.2)) := by
        rw [measurable_pi_iff]
        intro o
        cases o with
        | none =>
            unfold FunctionalInequalities.KLS.LogConcave.Suspension.copyStat
            measurability
        | some ij =>
            measurability
      unfold FunctionalInequalities.KLS.LogConcave.Suspension.embed
      exact (WithLp.measurable_toLp 2 _).comp hg

    rw [FunctionalInequalities.KLS.LogConcave.Suspension.jointLaw, lintegral_map (by fun_prop) hmeas]
    simp_rw [hintegrand]

    let gi : Fin N → EuclideanSpace ℝ (Fin n) → ENNReal := fun i x =>
      ENNReal.ofReal (Real.exp
        (z none / (σ * Real.sqrt N) * f x +
          ⟪(WithLp.toLp 2 fun j => z (some (i, j)) :
              EuclideanSpace ℝ (Fin n)), x⟫))
    let G : (Fin N → EuclideanSpace ℝ (Fin n)) → ENNReal := fun x =>
      ∏ i : Fin N, gi i (x i)
    let H : ℝ → ENNReal := fun s =>
      ENNReal.ofReal (Real.exp (z none / σ * s))

    have hG : Measurable G := by
      dsimp [G, gi]
      measurability
    have hH : Measurable H := by
      dsimp [H]
      fun_prop

    have hpi :
        (∫⁻ x, G x ∂(Measure.pi fun _ : Fin N => μ)) =
          ∏ i : Fin N, ∫⁻ x, gi i x ∂μ := by
      simpa [G] using
        (FunctionalInequalities.Probability.lintegral_pi_prod_fin_readable μ N gi (by
          intro i
          dsimp [gi]
          measurability))

    have hmain :
        (∫⁻ a, H a.2 * G a.1
            ∂((Measure.pi fun _ : Fin N => μ).prod (FunctionalInequalities.Probability.Line.laplaceMeasure β))) =
          (∫⁻ s, H s ∂FunctionalInequalities.Probability.Line.laplaceMeasure β) *
            ∏ i : Fin N, ∫⁻ x, gi i x ∂μ := by
      calc
        (∫⁻ a, H a.2 * G a.1
            ∂((Measure.pi fun _ : Fin N => μ).prod (FunctionalInequalities.Probability.Line.laplaceMeasure β))) =
            ∫⁻ a, G a.1 * H a.2
              ∂((Measure.pi fun _ : Fin N => μ).prod (FunctionalInequalities.Probability.Line.laplaceMeasure β)) :=
          lintegral_congr fun a => mul_comm _ _
        _ = (∫⁻ x, G x ∂(Measure.pi fun _ : Fin N => μ)) *
            (∫⁻ s, H s ∂FunctionalInequalities.Probability.Line.laplaceMeasure β) :=
          lintegral_prod_mul hG.aemeasurable hH.aemeasurable
        _ = (∫⁻ s, H s ∂FunctionalInequalities.Probability.Line.laplaceMeasure β) *
            ∏ i : Fin N, ∫⁻ x, gi i x ∂μ := by
          rw [hpi, mul_comm]

    simpa [G, H, gi] using hmain
