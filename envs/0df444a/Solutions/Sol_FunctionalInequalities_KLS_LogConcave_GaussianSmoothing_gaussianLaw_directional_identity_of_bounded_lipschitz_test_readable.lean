-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_directional_identity_of_bounded_lipschitz_test_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:37:12.49809+00:00
-- url     : https://prove2.me/submissions/4e9dcdd1-e30c-4291-b71c-b850c4f7fb5c

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Moments
import Theorems.Thm_FunctionalInequalities_Analysis_hasWeakDerivAlong_of_contDiff_readable
import Theorems.Thm_FunctionalInequalities_Analysis_integral_eq_zero_of_integrable_weak_derivative_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_gaussianLaw_exp_norm_integrable_readable

section
open MeasureTheory ProbabilityTheory Filter Topology
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [CompleteSpace E] in
/-- The Gaussian noise law `γ_s` is the tilt of Lebesgue measure by `e^{-s‖y‖²}`. -/
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_eq_tilted {s : ℝ} (hs : 0 < s) :
    gaussianLaw (V := E) s = (volume : Measure E).tilted (fun y => -s * ‖y‖ ^ 2) := by
  have hmass : (∫ y : E, Real.exp (-s * ‖y‖ ^ 2)) = mass (V := E) s := integral_kernel hs
  unfold gaussianLaw Measure.tilted normalizedKernel kernel
  rw [hmass]
omit [CompleteSpace E] in
/-- `γ_s` has a finite second moment. -/
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_memLp_two {s : ℝ} (hs : 0 < s) : MemLp id 2 (gaussianLaw (V := E) s) := by
  let _ : IsProbabilityMeasure (gaussianLaw (V := E) s) := gaussianLaw_probability hs
  have he : Integrable (fun y : E => Real.exp ((1 : ℝ) * ‖y‖)) (gaussianLaw s) := by
    simpa only [one_mul] using gaussianLaw_exp_norm_integrable_readable (E := E) hs
  exact (memLp_two_iff_integrable_sq_norm continuous_id.aestronglyMeasurable).2
    (Probability.integrable_norm_pow_of_integrable_exp_norm (by norm_num : (0 : ℝ) < 1) he 2)
end
section GaussianDirectionalIdentity
open MeasureTheory Filter
open FunctionalInequalities.Analysis
open scoped ContDiff Topology RealInnerProductSpace
set_option maxHeartbeats 800000 in
/-- Gaussian integration by parts for C1 bounded globally Lipschitz tests: under `gaussianLaw s` (`s > 0`, all dimensions),
`∫ ⟪x, v⟫ f = (2 s)⁻¹ ∫ D_v f`, with both integrands integrable. -/
theorem solution {n : ℕ}
    {s : ℝ} (hs : 0 < s) {f : EuclideanSpace ℝ (Fin n) → ℝ} {L : NNReal}
    (hf : ContDiff ℝ 1 f) (hLip : LipschitzWith L f) (C : ℝ) (hbound : ∀ x, ‖f x‖ ≤ C)
    (v : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun x => ⟪x, v⟫ * f x) (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw s) ∧
    Integrable (fun x => fderiv ℝ f x v) (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw s) ∧
    (∫ x, ⟪x, v⟫ * f x ∂(FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw s)) =
      (2 * s)⁻¹ * ∫ x, fderiv ℝ f x v ∂(FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw s) := by
  let E := EuclideanSpace ℝ (Fin n)
  let w : E → ℝ := fun x => Real.exp (-s * ‖x‖ ^ 2)
  let mu : Measure E := FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw s
  let : IsProbabilityMeasure mu := FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_probability hs
  have hexp : Integrable (fun x : E => Real.exp (-s * ‖x‖ ^ 2)) volume := FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.integrable_kernel hs
  have hF : Integrable f mu :=
    (integrable_const C).mono' hf.continuous.aestronglyMeasurable (ae_of_all _ hbound)
  have hX : Integrable (fun x : E => ⟪x, v⟫) mu :=
    ((FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_memLp_two hs).inner_const (𝕜 := ℝ) v).integrable one_le_two
  have hXF : Integrable (fun x : E => ⟪x, v⟫ * f x) mu :=
    hX.mul_bdd hf.continuous.aestronglyMeasurable (ae_of_all _ hbound)
  have hdfmeas : Measurable (fun x : E => fderiv ℝ f x v) :=
    (continuous_id.clm_apply continuous_const).measurable.comp (measurable_fderiv ℝ f)
  have hDF : Integrable (fun x : E => fderiv ℝ f x v) mu := by
    apply (integrable_const ((L : ℝ) * ‖v‖)).mono' hdfmeas.aestronglyMeasurable
    exact ae_of_all _ fun x => ((fderiv ℝ f x).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hLip) (norm_nonneg v))
  have raw (k : E → ℝ) (hk : Integrable k mu) : Integrable (fun x => w x * k x) volume := by
    have hkt : Integrable k ((volume : Measure E).tilted (fun x => -s * ‖x‖ ^ 2)) := by
      rwa [← FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_eq_tilted hs]
    simpa only [w, smul_eq_mul] using (integrable_tilted_iff hexp k).mp hkt
  have hRawF := raw f hF
  have hRawXF := raw (fun x => ⟪x, v⟫ * f x) hXF
  have hRawDF := raw (fun x => fderiv ℝ f x v) hDF
  have hw : ContDiff ℝ 1 w := by
    have hn : ContDiff ℝ 1 (fun x : E => ‖x‖ ^ 2) := contDiff_norm_sq ℝ
    exact ((contDiff_const : ContDiff ℝ 1 (fun _ : E => -s)).mul hn).exp
  have hd (x : E) : fderiv ℝ (fun y => w y * f y) x v =
      w x * fderiv ℝ f x v - (2 * s) * (w x * (⟪x, v⟫ * f x)) := by
    have hwx : HasFDerivAt w (w x • ((-s) • (2 • innerSL ℝ x))) x :=
      ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (-s)).exp
    change fderiv ℝ (w * f) x v = _
    rw [(hwx.mul ((hf.differentiable one_ne_zero x).hasFDerivAt)).fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul, innerSL_apply_apply]
    ring
  have hRawD : Integrable (fun x => fderiv ℝ (fun y => w y * f y) x v) volume := by
    apply (hRawDF.sub (hRawXF.const_mul (2 * s))).congr
    filter_upwards [] with x
    exact (hd x).symm
  have hz := FunctionalInequalities.Analysis.integral_eq_zero_of_integrable_weak_derivative_readable
    (FunctionalInequalities.Analysis.hasWeakDerivAlong_of_contDiff_readable (hw.mul hf) v) hRawF hRawD
  have hRawEq : (∫ x, w x * fderiv ℝ f x v ∂volume) =
      (2 * s) * ∫ x, w x * (⟪x, v⟫ * f x) ∂volume := by
    have heq : (∫ x, fderiv ℝ (fun y => w y * f y) x v ∂volume) =
        (∫ x, w x * fderiv ℝ f x v ∂volume) -
        (2 * s) * ∫ x, w x * (⟪x, v⟫ * f x) ∂volume := by
      calc
        _ = ∫ x, w x * fderiv ℝ f x v - (2 * s) * (w x * (⟪x, v⟫ * f x)) ∂volume :=
          integral_congr_ae (ae_of_all _ hd)
        _ = _ := by rw [integral_sub hRawDF (hRawXF.const_mul (2 * s)), integral_const_mul]
    linarith
  have htilt (k : E → ℝ) : (∫ x, k x ∂mu) =
      (∫ x, w x * k x ∂volume) / (∫ x, w x ∂volume) := by
    dsimp only [mu]
    rw [FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_eq_tilted hs, integral_tilted]
    change (∫ x, (w x / (∫ y, w y ∂volume)) * k x ∂volume) = _
    simp_rw [div_mul_eq_mul_div]
    exact integral_div _ _
  refine ⟨hXF, hDF, ?_⟩
  change (∫ x, ⟪x, v⟫ * f x ∂mu) = (2 * s)⁻¹ * ∫ x, fderiv ℝ f x v ∂mu
  rw [htilt, htilt, hRawEq, mul_div_assoc, ← mul_assoc,
    inv_mul_cancel₀ (ne_of_gt (mul_pos (by norm_num : (0 : ℝ) < 2) hs)), one_mul]
