-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.Suspension.joint_integrability_factorization_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:22:28.291032+00:00
-- url     : https://prove2.me/submissions/ed17395d-b866-4468-9d77-97db0a8c91ec

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Suspension_Cumulant
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_lintegral_exp_inner_jointLaw_readable

noncomputable section
open MeasureTheory FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Analysis.Tensor
open FunctionalInequalities.Probability.Line
open scoped RealInnerProductSpace
private theorem FunctionalInequalities.KLS.LogConcave.Suspension.lintegral_exp_pos_probability {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (g : X → ℝ) (hg : Measurable g) :
    0 < ∫⁻ x, ENNReal.ofReal (Real.exp (g x)) ∂μ := by
  have hs : Function.support (fun x => ENNReal.ofReal (Real.exp (g x))) = Set.univ := by
    ext x
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (ENNReal.ofReal_pos.mpr (Real.exp_pos (g x))).ne'
  rw [lintegral_pos_iff_support (hg.exp.ennreal_ofReal), hs, measure_univ]
  norm_num
private theorem FunctionalInequalities.KLS.LogConcave.Suspension.fin_prod_factor_ne_top {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ι → ENNReal) (hb : ∀ i, b i ≠ 0) (hprod : (∏ i, b i) ≠ ⊤) (i : ι) :
    b i ≠ ⊤ := by
  have hrest : (∏ j ∈ (Finset.univ : Finset ι).erase i, b j) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => hb j)
  have hmul : (∏ j ∈ (Finset.univ : Finset ι).erase i, b j) * b i ≠ ⊤ := by
    rw [Finset.prod_erase_mul _ _ (by simp)]
    exact hprod
  exact (ENNReal.lt_top_of_mul_ne_top_right hmul hrest).ne
/-- Joint integrability forces every strictly positive Laplace product factor to be finite. -/
theorem solution {n N : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f)
    {β : ℝ} (hβ : 0 < β) (_hN : 0 < N) (z : FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n)
    (hInt : Integrable (fun p => Real.exp ⟪z, p⟫) (FunctionalInequalities.KLS.LogConcave.Suspension.jointLaw μ f β (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) N)) :
    Integrable (fun s : ℝ => Real.exp (z none / FunctionalInequalities.KLS.LogConcave.Suspension.sigma β * s)) (FunctionalInequalities.Probability.Line.laplaceMeasure β) ∧
      (∀ i : Fin N, Integrable (fun x => Real.exp
        (z none / (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β * Real.sqrt N) * f x +
          ⟪(WithLp.toLp 2 fun j => z (some (i, j)) : EuclideanSpace ℝ (Fin n)), x⟫)) μ) ∧
      (∫ p, Real.exp ⟪z, p⟫ ∂FunctionalInequalities.KLS.LogConcave.Suspension.jointLaw μ f β (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) N) =
        (∫ s : ℝ, Real.exp (z none / FunctionalInequalities.KLS.LogConcave.Suspension.sigma β * s) ∂FunctionalInequalities.Probability.Line.laplaceMeasure β) *
          ∏ i : Fin N, ∫ x, Real.exp
            (z none / (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β * Real.sqrt N) * f x +
              ⟪(WithLp.toLp 2 fun j => z (some (i, j)) : EuclideanSpace ℝ (Fin n)), x⟫) ∂μ := by
  classical
  let _ : IsProbabilityMeasure (FunctionalInequalities.Probability.Line.laplaceMeasure β) := FunctionalInequalities.Probability.Line.isProbabilityMeasure_laplaceMeasure hβ
  let noise : ℝ → ℝ := fun s => z none / FunctionalInequalities.KLS.LogConcave.Suspension.sigma β * s
  let copy : Fin N → EuclideanSpace ℝ (Fin n) → ℝ := fun i x =>
    z none / (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β * Real.sqrt N) * f x +
      ⟪(WithLp.toLp 2 fun j => z (some (i, j)) : EuclideanSpace ℝ (Fin n)), x⟫
  let A : ENNReal := ∫⁻ s, ENNReal.ofReal (Real.exp (noise s)) ∂FunctionalInequalities.Probability.Line.laplaceMeasure β
  let B : Fin N → ENNReal := fun i => ∫⁻ x, ENNReal.ofReal (Real.exp (copy i x)) ∂μ
  let J : ENNReal := ∫⁻ p, ENNReal.ofReal (Real.exp ⟪z, p⟫) ∂FunctionalInequalities.KLS.LogConcave.Suspension.jointLaw μ f β (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) N
  have hmNoise : Measurable noise := by dsimp [noise]; fun_prop
  have hmCopy (i : Fin N) : Measurable (copy i) := by dsimp [copy]; measurability
  have hApos : 0 < A := FunctionalInequalities.KLS.LogConcave.Suspension.lintegral_exp_pos_probability (FunctionalInequalities.Probability.Line.laplaceMeasure β) noise hmNoise
  have hBpos (i : Fin N) : 0 < B i := FunctionalInequalities.KLS.LogConcave.Suspension.lintegral_exp_pos_probability μ (copy i) (hmCopy i)
  have hJfinite : J ≠ ⊤ :=
    (lintegral_ofReal_ne_top_iff_integrable hInt.aestronglyMeasurable
      (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)).mpr hInt
  have hfactor : J = A * ∏ i, B i := by
    exact FunctionalInequalities.KLS.LogConcave.Suspension.lintegral_exp_inner_jointLaw_readable μ hf β (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) z
  have htotal : A * ∏ i, B i ≠ ⊤ := hfactor.symm ▸ hJfinite
  have hprodNonzero : (∏ i, B i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => (hBpos i).ne')
  have hAfinite : A ≠ ⊤ := (ENNReal.lt_top_of_mul_ne_top_left htotal hprodNonzero).ne
  have hprodFinite : (∏ i, B i) ≠ ⊤ :=
    (ENNReal.lt_top_of_mul_ne_top_right htotal hApos.ne').ne
  have hBfinite (i : Fin N) : B i ≠ ⊤ :=
    FunctionalInequalities.KLS.LogConcave.Suspension.fin_prod_factor_ne_top B (fun i => (hBpos i).ne') hprodFinite i
  have hNoise : Integrable (fun s => Real.exp (noise s)) (FunctionalInequalities.Probability.Line.laplaceMeasure β) :=
    (lintegral_ofReal_ne_top_iff_integrable hmNoise.exp.aestronglyMeasurable
      (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)).mp hAfinite
  have hCopy (i : Fin N) : Integrable (fun x => Real.exp (copy i x)) μ :=
    (lintegral_ofReal_ne_top_iff_integrable (hmCopy i).exp.aestronglyMeasurable
      (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)).mp (hBfinite i)
  have hJreal : J.toReal = ∫ p, Real.exp ⟪z, p⟫ ∂FunctionalInequalities.KLS.LogConcave.Suspension.jointLaw μ f β (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) N :=
    (integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le) hInt.aestronglyMeasurable).symm
  have hAreal : A.toReal = ∫ s, Real.exp (noise s) ∂FunctionalInequalities.Probability.Line.laplaceMeasure β :=
    (integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le) hNoise.aestronglyMeasurable).symm
  have hBreal (i : Fin N) : (B i).toReal = ∫ x, Real.exp (copy i x) ∂μ :=
    (integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le) (hCopy i).aestronglyMeasurable).symm
  have hreal := congrArg ENNReal.toReal hfactor
  rw [ENNReal.toReal_mul, ENNReal.toReal_prod, hJreal, hAreal] at hreal
  simp_rw [hBreal] at hreal
  exact ⟨hNoise, hCopy, hreal⟩
