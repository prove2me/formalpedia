-- Prove2me | solution 1 for GaussianMatrix.gordon_minimax
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T08:23:04.860986+00:00
-- url     : https://prove2.me/submissions/ec9fb2fb-ada2-4da0-80e1-de38b4f6ac65

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

/-!
# Gordon's minimax comparison inequality (expectation form, no equal-variance assumption)

Proof by Gaussian interpolation (Kahane, Gordon; Vershynin HDP Exercise 7.2.14):

* `gmm_gaussian_ibp` — Gaussian integration by parts (adapted from the Sudakov–Fernique file);
* `gmm_interp` — for a C² test function `F` with bounded gradient `g` and Hessian `H`, and
  independent centered Gaussian vectors `X, Y`, `𝔼F(X) ≤ 𝔼F(Y)` whenever
  `∑ᵢⱼ (Σʸᵢⱼ - Σˣᵢⱼ) Hᵢⱼ(x) ≥ 0` for all `x`;
* `gmmF β x = -β⁻¹ log ∑ᵤ (∑ₜ exp(β x₍ᵤ,ₜ₎))⁻¹` — the smooth min-max, with gradient `gmmg`
  (`= p_u q_{t|u}`) and Hessian `gmmH`; `min max x - log|U|/β ≤ gmmF β x ≤ min max x + log|T|/β`;
* `gmm_hess_nonneg` — the Hessian is symmetric with zero row sums, `≤ 0` off the diagonal within a
  block and `≥ 0` across blocks, hence pairs nonnegatively with the covariance difference;
* `gmm_main` — the theorem, after realising `X, Y` independently on the product of their laws and
  letting `β → ∞`.
-/

namespace GaussianMatrix

open Real in
lemma gmm_hasDerivAt_pdf (v : NNReal) (hv : v ≠ 0) (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 v) (-(x / v) * gaussianPDFReal 0 v x) x := by
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  have h1 : HasDerivAt (fun x : ℝ => -(x - 0) ^ 2 / (2 * v)) (-(2 * (x - 0)) / (2 * v)) x := by
    have := ((hasDerivAt_id x).sub_const 0).pow 2
    simpa using (this.neg).div_const (2 * (v : ℝ))
  have h2 := (h1.exp).const_mul (√(2 * π * v))⁻¹
  rw [gaussianPDFReal_def]
  refine h2.congr_deriv ?_
  simp only [sub_zero]
  field_simp

lemma gmm_ibp_real (v : NNReal) (h h' : ℝ → ℝ) (hh : ∀ x, HasDerivAt h (h' x) x)
    (hc : Continuous h') (M M' : ℝ) (hb : ∀ x, |h x| ≤ M) (hb' : ∀ x, |h' x| ≤ M') :
    ∫ x, x * h x ∂(gaussianReal 0 v) = v * ∫ x, h' x ∂(gaussianReal 0 v) := by
  by_cases hv : v = 0
  · subst hv; simp [gaussianReal_zero_var]
  have hv' : (0 : ℝ) < v := by positivity
  have hhc : Continuous h := continuous_iff_continuousAt.2 fun x => (hh x).continuousAt
  rw [integral_gaussianReal_eq_integral_smul hv, integral_gaussianReal_eq_integral_smul hv]
  have hφ : Integrable (gaussianPDFReal 0 v) := integrable_gaussianPDFReal 0 v
  have hxφ : Integrable (fun x => x * gaussianPDFReal 0 v x) := by
    have := (integrable_mul_exp_neg_mul_sq (b := 1 / (2 * v)) (by positivity)).const_mul
      (Real.sqrt (2 * Real.pi * v))⁻¹
    refine this.congr (ae_of_all _ fun x => ?_)
    simp only [gaussianPDFReal_def, sub_zero]
    ring_nf
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable (u := h) (u' := h')
    (v := gaussianPDFReal 0 v) (v' := fun x => -(x / v) * gaussianPDFReal 0 v x)
    (fun x _ => hh x) (fun x _ => gmm_hasDerivAt_pdf v hv x) ?_ ?_ ?_
  · simp only [smul_eq_mul]
    have e1 : ∫ x, h x * (-(x / v) * gaussianPDFReal 0 v x)
        = -(1 / v) * ∫ x, gaussianPDFReal 0 v x * (x * h x) := by
      rw [← integral_const_mul]; congr 1; ext x; ring
    have e2 : ∫ x, h' x * gaussianPDFReal 0 v x = ∫ x, gaussianPDFReal 0 v x * h' x := by
      congr 1; ext x; ring
    rw [e1, e2] at key
    have k2 : (1 / (v:ℝ)) * ∫ x, gaussianPDFReal 0 v x * (x * h x)
        = ∫ x, gaussianPDFReal 0 v x * h' x := by linarith
    rw [← k2]; field_simp
  · -- h * v'
    have : Integrable (fun x => -(1 / (v : ℝ)) * (x * gaussianPDFReal 0 v x)) := hxφ.const_mul _
    refine Integrable.mono' (this.norm.const_mul M) ?_ (ae_of_all _ fun x => ?_)
    · exact (hhc.mul (by
        have : Continuous (gaussianPDFReal 0 v) := by
          rw [gaussianPDFReal_def]; fun_prop
        fun_prop)).aestronglyMeasurable
    · simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
      have := hb x
      rw [abs_neg, abs_neg, abs_div, abs_div, abs_one]
      have e : |x| / |(v:ℝ)| * |gaussianPDFReal 0 v x| = 1 / |(v:ℝ)| * (|x| * |gaussianPDFReal 0 v x|) := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_right this (by positivity)
  · refine Integrable.mono' (hφ.norm.const_mul M') ?_ (ae_of_all _ fun x => ?_)
    · exact (hc.mul (by rw [gaussianPDFReal_def]; fun_prop)).aestronglyMeasurable
    · simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hb' x) (abs_nonneg _)
  · refine Integrable.mono' (hφ.norm.const_mul M) ?_ (ae_of_all _ fun x => ?_)
    · exact (hhc.mul (by rw [gaussianPDFReal_def]; fun_prop)).aestronglyMeasurable
    · simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hb x) (abs_nonneg _)


lemma gmm_indep_regress {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω] {P : Measure Ω}
    (U : Ω → ℝ) (W : ι → Ω → ℝ)
    (hUW : HasGaussianLaw (fun ω => (U ω, fun j => W j ω)) P)
    (hcov : ∀ j, cov[U, W j; P] = 0) :
    IndepFun U (fun ω j => W j ω) P := by
  set L : ℝ × (ι → ℝ) →L[ℝ] (Unit → ℝ) × (ι → ℝ) :=
    (ContinuousLinearMap.pi fun _ : Unit => ContinuousLinearMap.fst ℝ ℝ (ι → ℝ)).prod
      (ContinuousLinearMap.snd ℝ ℝ (ι → ℝ)) with hL
  have h1 : HasGaussianLaw (fun ω => (fun _ : Unit => U ω, fun j => W j ω)) P := by
    have := hUW.map_fun L
    simpa [hL] using this
  have h2 := h1.indepFun_of_covariance_eval (X := fun _ : Unit => U) (fun _ j => hcov j)
  exact h2.comp (measurable_pi_apply ()) measurable_id


theorem gmm_gaussian_ibp {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    {P : Measure Ω} (U : Ω → ℝ) (V : ι → Ω → ℝ)
    (hUV : HasGaussianLaw (fun ω => (U ω, fun j => V j ω)) P) (hU0 : ∫ ω, U ω ∂P = 0)
    (G : (ι → ℝ) → ℝ) (G' : ι → (ι → ℝ) → ℝ)
    (hG : ∀ x, HasFDerivAt G
      (∑ j, G' j x • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) j) x)
    (hG'c : ∀ j, Continuous (G' j)) (C : ℝ) (hGb : ∀ x, |G x| ≤ C)
    (hG'b : ∀ j x, |G' j x| ≤ C) :
    ∫ ω, U ω * G (fun j => V j ω) ∂P = ∑ j, cov[U, V j; P] * ∫ ω, G' j (fun j => V j ω) ∂P := by
  have hP := hUV.isProbabilityMeasure
  have hUm : MemLp U 2 P := hUV.fst.memLp_two
  have hVm : ∀ j, MemLp (V j) 2 P := fun j => (hUV.snd.eval j).memLp_two
  have hGc : Continuous G := continuous_iff_continuousAt.2 fun x => (hG x).continuousAt
  have hUae : AEMeasurable U P := hUV.fst.aemeasurable
  have hVae : AEMeasurable (fun ω j => V j ω) P := hUV.snd.aemeasurable
  set σ2 := Var[U; P] with hσ2
  by_cases hσ : σ2 = 0
  · have hU : ∀ᵐ ω ∂P, U ω = 0 := by
      filter_upwards [ae_eq_integral_of_variance_eq_zero hUm hσ] with ω hω
      rw [hω, hU0]
    have hL : ∫ ω, U ω * G (fun j => V j ω) ∂P = 0 := by
      rw [integral_eq_zero_of_ae]
      filter_upwards [hU] with ω hω; simp [hω]
    have hc : ∀ j, cov[U, V j; P] = 0 := by
      intro j
      rw [covariance, integral_eq_zero_of_ae]
      filter_upwards [hU] with ω hω; simp [hω, hU0]
    simp [hL, hc]
  have hσpos : 0 < σ2 := lt_of_le_of_ne (variance_nonneg U P) (Ne.symm hσ)
  set c : ι → ℝ := fun j => cov[U, V j; P] / σ2 with hc
  set W : ι → Ω → ℝ := fun j ω => V j ω - U ω * c j with hW
  -- joint law of (U, W)
  set L : ℝ × (ι → ℝ) →L[ℝ] ℝ × (ι → ℝ) :=
    (ContinuousLinearMap.fst ℝ ℝ (ι → ℝ)).prod
      (ContinuousLinearMap.snd ℝ ℝ (ι → ℝ) - (ContinuousLinearMap.fst ℝ ℝ (ι → ℝ)).smulRight c)
    with hLdef
  have hUW : HasGaussianLaw (fun ω => (U ω, fun j => W j ω)) P := by
    have := hUV.map_fun L
    have heq : (fun ω => (U ω, fun j => W j ω)) = fun ω => L (U ω, fun j => V j ω) := by
      funext ω
      simp only [hLdef, hW]
      simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst',
        sub_apply, ContinuousLinearMap.coe_snd',
        ContinuousLinearMap.smulRight_apply]
      ext j <;> simp
    rw [heq]; exact this
  have hcovW : ∀ j, cov[U, W j; P] = 0 := by
    intro j
    rw [hW]
    simp only
    rw [covariance_fun_sub_right hUm (hVm j) (hUm.mul_const _), covariance_mul_const_right,
      covariance_self hUae, ← hσ2, hc]
    field_simp
    ring
  have hind := gmm_indep_regress U W hUW hcovW
  set Wv : Ω → (ι → ℝ) := fun ω j => W j ω with hWv
  have hWae : AEMeasurable Wv P := hUW.snd.aemeasurable
  have hprod := (indepFun_iff_map_prod_eq_prod_map_map hUae hWae).1 hind
  have hmapU : P.map U = gaussianReal 0 σ2.toNNReal := by
    rw [hUV.fst.map_eq_gaussianReal, hU0]
  have hVeq : ∀ ω, (fun j => V j ω) = U ω • c + Wv ω := by
    intro ω; ext j; simp [hWv, hW]
  -- generic transfer
  have hpm : AEMeasurable (fun ω => (U ω, Wv ω)) P := hUae.prodMk hWae
  have htrans : ∀ F : ℝ × (ι → ℝ) → ℝ, Continuous F →
      Integrable (fun ω => F (U ω, Wv ω)) P →
      ∫ ω, F (U ω, Wv ω) ∂P = ∫ w, ∫ u, F (u, w) ∂(P.map U) ∂(P.map Wv) := by
    intro F hF hFi
    have h1 : ∫ ω, F (U ω, Wv ω) ∂P = ∫ p, F p ∂(P.map (fun ω => (U ω, Wv ω))) :=
      (integral_map hpm hF.aestronglyMeasurable).symm
    have hint : Integrable F (P.map (fun ω => (U ω, Wv ω))) :=
      (integrable_map_measure hF.aestronglyMeasurable hpm).2 hFi
    rw [h1, hprod]
    rw [hprod] at hint
    exact integral_prod_symm F hint
  set F1 : ℝ × (ι → ℝ) → ℝ := fun p => p.1 * G (p.1 • c + p.2) with hF1
  set F2 : ℝ × (ι → ℝ) → ℝ := fun p => ∑ j, G' j (p.1 • c + p.2) * c j with hF2
  have hF1c : Continuous F1 := by rw [hF1]; fun_prop
  have hF2c : Continuous F2 := by
    rw [hF2]
    exact continuous_finsetSum _ fun j _ => ((hG'c j).comp (by fun_prop)).mul continuous_const
  set K := C * ∑ j, |c j| with hK
  have hF2b : ∀ p, |F2 p| ≤ K := by
    intro p
    rw [hF2, hK, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hG'b j _) (abs_nonneg _)
  have hF1i : Integrable (fun ω => F1 (U ω, Wv ω)) P := by
    refine Integrable.mono' ((hUm.integrable one_le_two).norm.const_mul C)
      (hF1c.comp_aestronglyMeasurable hpm.aestronglyMeasurable) (ae_of_all _ fun ω => ?_)
    simp only [hF1, Real.norm_eq_abs, abs_mul]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (hGb _) (abs_nonneg _)
  have hF2i : Integrable (fun ω => F2 (U ω, Wv ω)) P := by
    refine Integrable.mono' (integrable_const K)
      (hF2c.comp_aestronglyMeasurable hpm.aestronglyMeasurable) (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs]; exact hF2b _
  have hσnn : ((σ2.toNNReal : NNReal) : ℝ) = σ2 := Real.coe_toNNReal _ hσpos.le
  have hinner : ∀ w : ι → ℝ, ∫ u, F1 (u, w) ∂(P.map U) = σ2 * ∫ u, F2 (u, w) ∂(P.map U) := by
    intro w
    rw [hmapU]
    have := gmm_ibp_real σ2.toNNReal (fun u => G (u • c + w)) (fun u => F2 (u, w)) ?_
      (hF2c.comp (by fun_prop)) C K (fun u => hGb _) (fun u => hF2b _)
    · rw [hσnn] at this
      simpa [hF1] using this
    · intro u
      have hd : HasDerivAt (fun u : ℝ => u • c + w) ((1 : ℝ) • c) u :=
        ((hasDerivAt_id u).smul_const c).add_const w
      have := (hG (u • c + w)).comp_hasDerivAt u hd
      have e : F2 (u, w) = (∑ j, G' j (u • c + w) •
          ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) j) ((1 : ℝ) • c) := by
        simp [hF2]
      rw [e]; exact this
  have hLHS : ∫ ω, U ω * G (fun j => V j ω) ∂P = ∫ ω, F1 (U ω, Wv ω) ∂P := by
    congr 1; ext ω; rw [hVeq ω]
  rw [hLHS, htrans F1 hF1c hF1i]
  simp_rw [hinner]
  rw [integral_const_mul, ← htrans F2 hF2c hF2i]
  simp only [hF2, ← hVeq]
  rw [integral_finsetSum _ (fun j _ => ?_), Finset.mul_sum]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_mul_const, hc]
    field_simp
  · refine Integrable.mono' (integrable_const (C * |c j|))
      ((((hG'c j).comp_aestronglyMeasurable hVae.aestronglyMeasurable)).mul_const _)
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hG'b j _) (abs_nonneg _)

section Interp

variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω] {P : Measure Ω}

/-- covariance of the derivative process with the interpolated process -/
lemma gmm_cov_DZ (X Y : ι → Ω → ℝ)
    (hXY : HasGaussianLaw (fun ω => (fun t => X t ω, fun t => Y t ω)) P)
    (hX0 : ∀ t, ∫ ω, X t ω ∂P = 0) (hY0 : ∀ t, ∫ ω, Y t ω ∂P = 0)
    (hcross : ∀ s t, ∫ ω, X s ω * Y t ω ∂P = 0) (θ : ℝ) (i j : ι) :
    cov[fun ω => -Real.sin θ * X i ω + Real.cos θ * Y i ω,
      fun ω => Real.cos θ * X j ω + Real.sin θ * Y j ω; P]
      = Real.sin θ * Real.cos θ *
        (∫ ω, Y i ω * Y j ω ∂P - ∫ ω, X i ω * X j ω ∂P) := by
  have hP := hXY.isProbabilityMeasure
  have hXm : ∀ t, MemLp (X t) 2 P := fun t => (hXY.fst.eval t).memLp_two
  have hYm : ∀ t, MemLp (Y t) 2 P := fun t => (hXY.snd.eval t).memLp_two
  set s := Real.sin θ
  set c := Real.cos θ
  have hD : MemLp (fun ω => -s * X i ω + c * Y i ω) 2 P :=
    ((hXm i).const_mul _).add ((hYm i).const_mul _)
  have hZ : MemLp (fun ω => c * X j ω + s * Y j ω) 2 P :=
    ((hXm j).const_mul _).add ((hYm j).const_mul _)
  rw [covariance_eq_sub hD hZ]
  have hint : ∀ t, Integrable (X t) P := fun t => (hXm t).integrable one_le_two
  have hintY : ∀ t, Integrable (Y t) P := fun t => (hYm t).integrable one_le_two
  have hD0 : ∫ ω, -s * X i ω + c * Y i ω ∂P = 0 := by
    rw [integral_add ((hint i).const_mul _) ((hintY i).const_mul _), integral_const_mul,
      integral_const_mul, hX0, hY0]; ring
  rw [hD0, zero_mul, sub_zero]
  simp only [Pi.mul_apply]
  have e : (fun ω => (-s * X i ω + c * Y i ω) * (c * X j ω + s * Y j ω))
      = fun ω => (-s * c) * (X i ω * X j ω) + (-s ^ 2) * (X i ω * Y j ω)
        + c ^ 2 * (X j ω * Y i ω) + (c * s) * (Y i ω * Y j ω) := by
    funext ω; ring
  have i1 : Integrable (fun ω => X i ω * X j ω) P := (hXm i).integrable_mul (hXm j)
  have i2 : Integrable (fun ω => X i ω * Y j ω) P := (hXm i).integrable_mul (hYm j)
  have i3 : Integrable (fun ω => X j ω * Y i ω) P := (hXm j).integrable_mul (hYm i)
  have i4 : Integrable (fun ω => Y i ω * Y j ω) P := (hYm i).integrable_mul (hYm j)
  rw [e, integral_add (((i1.const_mul _).fun_add (i2.const_mul _)).fun_add (i3.const_mul _))
    (i4.const_mul _), integral_add ((i1.const_mul _).fun_add (i2.const_mul _)) (i3.const_mul _),
    integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul, hcross, hcross]
  ring

omit [Fintype ι] in
lemma gmm_sq_sub (X : ι → Ω → ℝ) (hXm : ∀ t, MemLp (X t) 2 P) (i j : ι) :
    ∫ ω, (X i ω - X j ω) ^ 2 ∂P = ∫ ω, X i ω * X i ω ∂P + ∫ ω, X j ω * X j ω ∂P
      - ∫ ω, X i ω * X j ω ∂P - ∫ ω, X j ω * X i ω ∂P := by
  have i1 : Integrable (fun ω => X i ω * X i ω) P := (hXm i).integrable_mul (hXm i)
  have i2 : Integrable (fun ω => X j ω * X j ω) P := (hXm j).integrable_mul (hXm j)
  have i3 : Integrable (fun ω => X i ω * X j ω) P := (hXm i).integrable_mul (hXm j)
  have i4 : Integrable (fun ω => X j ω * X i ω) P := (hXm j).integrable_mul (hXm i)
  have e : (fun ω => (X i ω - X j ω) ^ 2) = fun ω => X i ω * X i ω + X j ω * X j ω
      - X i ω * X j ω - X j ω * X i ω := by funext ω; ring
  rw [e, integral_sub ((i1.fun_add i2).sub' i3) i4, integral_sub (i1.fun_add i2) i3,
    integral_add i1 i2]

end Interp

section GenInterp

/-- Gaussian interpolation for a general smooth test function with bounded gradient and Hessian. -/
theorem gmm_interp {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω] {P : Measure Ω}
    (X Y : ι → Ω → ℝ)
    (hXY : HasGaussianLaw (fun ω => (fun t => X t ω, fun t => Y t ω)) P)
    (hX0 : ∀ t, ∫ ω, X t ω ∂P = 0) (hY0 : ∀ t, ∫ ω, Y t ω ∂P = 0)
    (hcross : ∀ s t, ∫ ω, X s ω * Y t ω ∂P = 0)
    (F : (ι → ℝ) → ℝ) (g : ι → (ι → ℝ) → ℝ) (H : ι → ι → (ι → ℝ) → ℝ)
    (hF : ∀ x, HasFDerivAt F
      (∑ i, g i x • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i) x)
    (hg : ∀ i x, HasFDerivAt (g i)
      (∑ j, H i j x • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) j) x)
    (hHc : ∀ i j, Continuous (H i j))
    (C : ℝ) (hgb : ∀ i x, |g i x| ≤ C) (hHb : ∀ i j x, |H i j x| ≤ C)
    (K : ℝ) (hFb : ∀ x, |F x| ≤ ∑ t, |x t| + K)
    (hpos : ∀ x, 0 ≤ ∑ i, ∑ j,
      (∫ ω, Y i ω * Y j ω ∂P - ∫ ω, X i ω * X j ω ∂P) * H i j x) :
    ∫ ω, F (fun t => X t ω) ∂P ≤ ∫ ω, F (fun t => Y t ω) ∂P := by
  have hP := hXY.isProbabilityMeasure
  have hXm : ∀ t, MemLp (X t) 2 P := fun t => (hXY.fst.eval t).memLp_two
  have hYm : ∀ t, MemLp (Y t) 2 P := fun t => (hXY.snd.eval t).memLp_two
  have hXi : ∀ t, Integrable (X t) P := fun t => (hXm t).integrable one_le_two
  have hYi : ∀ t, Integrable (Y t) P := fun t => (hYm t).integrable one_le_two
  have hXae : ∀ t, AEMeasurable (X t) P := fun t => (hXm t).aestronglyMeasurable.aemeasurable
  have hYae : ∀ t, AEMeasurable (Y t) P := fun t => (hYm t).aestronglyMeasurable.aemeasurable
  have hFc : Continuous F := continuous_iff_continuousAt.2 fun x => (hF x).continuousAt
  have hgc : ∀ i, Continuous (g i) := fun i =>
    continuous_iff_continuousAt.2 fun x => (hg i x).continuousAt
  set Z : ℝ → Ω → ι → ℝ := fun θ ω t => Real.cos θ * X t ω + Real.sin θ * Y t ω with hZ
  set D : ℝ → Ω → ι → ℝ := fun θ ω t => -Real.sin θ * X t ω + Real.cos θ * Y t ω with hD
  set B : Ω → ℝ := fun ω => ∑ t, (|X t ω| + |Y t ω|) with hBdef
  have hB : Integrable B P :=
    integrable_finsetSum _ fun t _ => (hXi t).abs.add (hYi t).abs
  have hZb : ∀ θ ω t, |Z θ ω t| ≤ |X t ω| + |Y t ω| := by
    intro θ ω t
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    gcongr
    · exact (mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one θ))
    · exact (mul_le_of_le_one_left (abs_nonneg _) (Real.abs_sin_le_one θ))
  have hDb : ∀ θ ω t, |D θ ω t| ≤ |X t ω| + |Y t ω| := by
    intro θ ω t
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_neg]
    gcongr
    · exact (mul_le_of_le_one_left (abs_nonneg _) (Real.abs_sin_le_one θ))
    · exact (mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one θ))
  have hZae : ∀ θ, AEMeasurable (Z θ) P := fun θ =>
    aemeasurable_pi_lambda _ fun t => ((hXae t).const_mul _).add ((hYae t).const_mul _)
  have hDae : ∀ θ t, AEMeasurable (fun ω => D θ ω t) P := fun θ t =>
    ((hXae t).const_mul _).add ((hYae t).const_mul _)
  set Φ : ℝ → ℝ := fun θ => ∫ ω, F (Z θ ω) ∂P with hΦ
  set F' : ℝ → Ω → ℝ := fun θ ω => ∑ i, g i (Z θ ω) * D θ ω i with hF'
  have hgD : ∀ θ ω i, |g i (Z θ ω) * D θ ω i| ≤ C * (|X i ω| + |Y i ω|) := by
    intro θ ω i
    rw [abs_mul]
    have hC : 0 ≤ C := (abs_nonneg _).trans (hgb i (Z θ ω))
    exact mul_le_mul (hgb i _) (hDb θ ω i) (abs_nonneg _) hC
  have hderiv : ∀ θ0, HasDerivAt Φ (∫ ω, F' θ0 ω ∂P) θ0 := by
    intro θ0
    have hFm : ∀ θ, AEStronglyMeasurable (fun ω => F (Z θ ω)) P := fun θ =>
      (hFc.measurable.comp_aemeasurable (hZae θ)).aestronglyMeasurable
    have hFint : Integrable (fun ω => F (Z θ0 ω)) P := by
      refine Integrable.mono' (hB.add (integrable_const K)) (hFm θ0)
        (ae_of_all _ fun ω => ?_)
      rw [Real.norm_eq_abs]
      refine (hFb _).trans ?_
      simp only [Pi.add_apply, hBdef]
      gcongr with t
      exact hZb θ0 ω t
    have hF'm : AEStronglyMeasurable (F' θ0) P := by
      refine (Finset.aemeasurable_fun_sum _ fun i _ => ?_).aestronglyMeasurable
      exact ((hgc i).measurable.comp_aemeasurable (hZae θ0)).mul (hDae θ0 i)
    have hbound : ∀ θ ω, ‖F' θ ω‖ ≤ C * B ω := by
      intro θ ω
      rw [Real.norm_eq_abs, hF', hBdef, Finset.mul_sum]
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hgD θ ω i)
    have hdiff : ∀ ω θ, HasDerivAt (fun θ => F (Z θ ω)) (F' θ ω) θ := by
      intro ω θ
      have hZd : HasDerivAt (fun θ => Z θ ω) (D θ ω) θ := by
        rw [hasDerivAt_pi]
        intro t
        exact ((Real.hasDerivAt_cos θ).mul_const (X t ω)).add
          ((Real.hasDerivAt_sin θ).mul_const (Y t ω))
      have := (hF (Z θ ω)).comp_hasDerivAt θ hZd
      refine this.congr_deriv ?_
      simp [hF']
    exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := P)
      (F := fun θ ω => F (Z θ ω)) (F' := F') (x₀ := θ0) (bound := fun ω => C * B ω)
      (s := Set.univ)
      Filter.univ_mem (Filter.Eventually.of_forall hFm) hFint hF'm
      (ae_of_all _ fun ω θ _ => hbound θ ω) (hB.const_mul C)
      (ae_of_all _ fun ω θ _ => hdiff ω θ)).2
  set Δ : ι → ι → ℝ := fun i j => ∫ ω, Y i ω * Y j ω ∂P - ∫ ω, X i ω * X j ω ∂P with hΔdef
  have hHi : ∀ θ i j, Integrable (fun ω => H i j (Z θ ω)) P := fun θ i j =>
    Integrable.mono' (integrable_const C)
      ((hHc i j).measurable.comp_aemeasurable (hZae θ)).aestronglyMeasurable
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hHb i j _)
  have hnonneg : ∀ θ, 0 ≤ Real.sin θ * Real.cos θ → 0 ≤ ∫ ω, F' θ ω ∂P := by
    intro θ hsc
    have hUV : ∀ i, HasGaussianLaw (fun ω => (D θ ω i, fun j => Z θ ω j)) P := by
      intro i
      set L : (ι → ℝ) × (ι → ℝ) →L[ℝ] ℝ × (ι → ℝ) :=
        ((-Real.sin θ) • ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i).comp
            (ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ))) +
          Real.cos θ • ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i).comp
            (ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ)))).prod
        (Real.cos θ • ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ) +
          Real.sin θ • ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ)) with hL
      have := hXY.map_fun L
      have heq : (fun ω => (D θ ω i, fun j => Z θ ω j))
          = fun ω => L (fun t => X t ω, fun t => Y t ω) := by
        funext ω
        simp only [hL, hD, hZ]
        ext j <;> simp
      rw [heq]; exact this
    have hU0 : ∀ i, ∫ ω, D θ ω i ∂P = 0 := by
      intro i
      simp only [hD]
      rw [integral_add ((hXi i).const_mul _) ((hYi i).const_mul _), integral_const_mul,
        integral_const_mul, hX0, hY0]; ring
    have hIBP : ∀ i, ∫ ω, D θ ω i * g i (Z θ ω) ∂P
        = ∑ j, (Real.sin θ * Real.cos θ * Δ i j) * ∫ ω, H i j (Z θ ω) ∂P := by
      intro i
      have h := gmm_gaussian_ibp (fun ω => D θ ω i) (fun j ω => Z θ ω j) (hUV i)
        (hU0 i) (g i) (H i) (fun x => hg i x) (fun j => hHc i j) C (hgb i) (hHb i)
      refine h.trans (Finset.sum_congr rfl fun j _ => ?_)
      congr 1
      exact gmm_cov_DZ X Y hXY hX0 hY0 hcross θ i j
    have hDp : ∀ i, Integrable (fun ω => D θ ω i * g i (Z θ ω)) P := by
      intro i
      refine Integrable.mono' (((hXi i).abs.add (hYi i).abs).const_mul C) (((hDae θ i).mul
        ((hgc i).measurable.comp_aemeasurable (hZae θ))).aestronglyMeasurable)
        (ae_of_all _ fun ω => ?_)
      rw [Real.norm_eq_abs, mul_comm]
      exact hgD θ ω i
    have e1 : ∫ ω, F' θ ω ∂P = ∑ i, ∫ ω, D θ ω i * g i (Z θ ω) ∂P := by
      simp only [hF']
      rw [integral_finsetSum _ (fun i _ => by simpa only [mul_comm] using hDp i)]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1; ext ω; ring
    have e2 : ∑ i, ∑ j, (Real.sin θ * Real.cos θ * Δ i j) * ∫ ω, H i j (Z θ ω) ∂P
        = ∫ ω, ∑ i, ∑ j, (Real.sin θ * Real.cos θ * Δ i j) * H i j (Z θ ω) ∂P := by
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ =>
        (hHi θ i j).const_mul _)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum _ (fun j _ => (hHi θ i j).const_mul _)]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_const_mul]
    rw [e1]
    simp_rw [hIBP]
    rw [e2]
    refine integral_nonneg fun ω => ?_
    have e3 : ∑ i, ∑ j, (Real.sin θ * Real.cos θ * Δ i j) * H i j (Z θ ω)
        = (Real.sin θ * Real.cos θ) * ∑ i, ∑ j, Δ i j * H i j (Z θ ω) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [e3]
    exact mul_nonneg hsc (hpos _)
  have hcont : Continuous Φ := continuous_iff_continuousAt.2 fun θ => (hderiv θ).continuousAt
  have hmono : MonotoneOn Φ (Set.Icc 0 (Real.pi / 2)) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 (Real.pi / 2))
      hcont.continuousOn (fun θ _ => (hderiv θ).hasDerivWithinAt) (fun θ hθ => ?_)
    rw [interior_Icc] at hθ
    refine hnonneg θ (mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1.le (by linarith [hθ.2,
      Real.pi_pos])) (Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2.le⟩))
  have hpi : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have h := hmono ⟨le_refl 0, hpi⟩ ⟨hpi, le_refl _⟩ hpi
  have h0 : Φ 0 = ∫ ω, F (fun t => X t ω) ∂P := by simp [hΦ, hZ]
  have h1 : Φ (Real.pi / 2) = ∫ ω, F (fun t => Y t ω) ∂P := by simp [hΦ, hZ]
  rw [← h0, ← h1]; exact h

end GenInterp

set_option linter.unusedSectionVars false

section Coeff

variable {ι : Type*} [Fintype ι]

local notation "PR" j => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) j

lemma gmm_coeff_mul {f h : (ι → ℝ) → ℝ} {x : ι → ℝ} {c d : ι → ℝ}
    (hf : HasFDerivAt f (∑ b, c b • PR b) x) (hh : HasFDerivAt h (∑ b, d b • PR b) x) :
    HasFDerivAt (fun y => f y * h y) (∑ b, (f x * d b + h x * c b) • PR b) x := by
  refine (hf.fun_mul hh).congr_fderiv ?_
  simp only [Finset.smul_sum, smul_smul, ← Finset.sum_add_distrib, add_smul]

lemma gmm_coeff_inv {f : (ι → ℝ) → ℝ} {x : ι → ℝ} {c : ι → ℝ}
    (hf : HasFDerivAt f (∑ b, c b • PR b) x) (hx : f x ≠ 0) :
    HasFDerivAt (fun y => (f y)⁻¹) (∑ b, (-(f x ^ 2)⁻¹ * c b) • PR b) x := by
  refine ((hasDerivAt_inv hx).comp_hasFDerivAt x hf).congr_fderiv ?_
  simp only [Finset.smul_sum, smul_smul]

lemma gmm_coeff_log {f : (ι → ℝ) → ℝ} {x : ι → ℝ} {c : ι → ℝ}
    (hf : HasFDerivAt f (∑ b, c b • PR b) x) (hx : f x ≠ 0) :
    HasFDerivAt (fun y => Real.log (f y)) (∑ b, ((f x)⁻¹ * c b) • PR b) x := by
  refine (hf.log hx).congr_fderiv ?_
  simp only [Finset.smul_sum, smul_smul]

lemma gmm_coeff_const_mul {f : (ι → ℝ) → ℝ} {x : ι → ℝ} {c : ι → ℝ}
    (hf : HasFDerivAt f (∑ b, c b • PR b) x) (r : ℝ) :
    HasFDerivAt (fun y => r * f y) (∑ b, (r * c b) • PR b) x := by
  refine (hf.const_mul r).congr_fderiv ?_
  simp only [Finset.smul_sum, smul_smul]

lemma gmm_coeff_sum {κ : Type*} [Fintype κ] {f : κ → (ι → ℝ) → ℝ} {x : ι → ℝ}
    {c : κ → ι → ℝ} (hf : ∀ k, HasFDerivAt (f k) (∑ b, c k b • PR b) x) :
    HasFDerivAt (fun y => ∑ k, f k y) (∑ b, (∑ k, c k b) • PR b) x := by
  have h := HasFDerivAt.sum (u := Finset.univ) (fun k _ => hf k)
  have e : (fun y => ∑ k, f k y) = ∑ k, f k := by funext y; simp
  rw [e]
  refine h.congr_fderiv ?_
  rw [Finset.sum_comm]
  simp only [Finset.sum_smul]

lemma gmm_coeff_exp [DecidableEq ι] (β : ℝ) (a : ι) (x : ι → ℝ) :
    HasFDerivAt (fun y : ι → ℝ => Real.exp (β * y a))
      (∑ b, (if b = a then β * Real.exp (β * x a) else 0) • PR b) x := by
  have h := (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) a).hasFDerivAt
    (x := x)).const_mul β).exp
  refine h.congr_fderiv ?_
  simp only [ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true, smul_smul]
  rw [mul_comm]
  rfl

end Coeff

section SmoothMinMax

variable {U T : Type*} [Fintype U] [Fintype T]

local notation "PR" j => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : U × T => ℝ) j

/-- block partition function `S_u(x) = ∑_t exp(β x_{ut})` -/
noncomputable def gmmS (β : ℝ) (u : U) (x : U × T → ℝ) : ℝ := ∑ t, Real.exp (β * x (u, t))
/-- `W(x) = ∑_u S_u(x)⁻¹` -/
noncomputable def gmmW (β : ℝ) (x : U × T → ℝ) : ℝ := ∑ u, (gmmS β u x)⁻¹
/-- the smooth min-max `F_β(x) = -β⁻¹ log ∑_u (∑_t e^{β x_{ut}})⁻¹` -/
noncomputable def gmmF (β : ℝ) (x : U × T → ℝ) : ℝ := -β⁻¹ * Real.log (gmmW β x)
/-- gradient `∂F/∂x_a = p_u q_{t|u}`, `a = (u,t)` -/
noncomputable def gmmg (β : ℝ) (a : U × T) (x : U × T → ℝ) : ℝ :=
  Real.exp (β * x a) * ((gmmS β a.1 x) ^ 2)⁻¹ * (gmmW β x)⁻¹
/-- within-block weight `q_{s|u} = e^{β x_b}/S_u`, `u = a.1`, `b = (·, s)` -/
noncomputable def gmmq (β : ℝ) (a b : U × T) (x : U × T → ℝ) : ℝ :=
  Real.exp (β * x b) / gmmS β a.1 x
/-- the Hessian of the smooth min-max -/
noncomputable def gmmH [DecidableEq U] [DecidableEq T] (β : ℝ) (a b : U × T)
    (x : U × T → ℝ) : ℝ :=
  β * ((if a = b then gmmg β a x else 0)
    - 2 * (if a.1 = b.1 then gmmg β a x * gmmq β a b x else 0) + gmmg β a x * gmmg β b x)

lemma gmmS_pos [Nonempty T] (β : ℝ) (u : U) (x : U × T → ℝ) : 0 < gmmS β u x :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

lemma gmmW_pos [Nonempty U] [Nonempty T] (β : ℝ) (x : U × T → ℝ) : 0 < gmmW β x :=
  Finset.sum_pos (fun u _ => inv_pos.2 (gmmS_pos β u x)) Finset.univ_nonempty

lemma gmm_exp_le_S (β : ℝ) (u : U) (t : T) (x : U × T → ℝ) :
    Real.exp (β * x (u, t)) ≤ gmmS β u x :=
  Finset.single_le_sum (f := fun t => Real.exp (β * x (u, t))) (fun _ _ => (Real.exp_pos _).le)
    (Finset.mem_univ t)

lemma gmm_Sinv_le_W [Nonempty T] (β : ℝ) (u : U) (x : U × T → ℝ) :
    (gmmS β u x)⁻¹ ≤ gmmW β x :=
  Finset.single_le_sum (f := fun u => (gmmS β u x)⁻¹)
    (fun v _ => (inv_pos.2 (gmmS_pos β v x)).le) (Finset.mem_univ u)

lemma gmmg_nonneg [Nonempty U] [Nonempty T] (β : ℝ) (a : U × T) (x : U × T → ℝ) :
    0 ≤ gmmg β a x := by
  unfold gmmg
  have := gmmS_pos β a.1 x
  have := gmmW_pos β x
  positivity

lemma gmmg_sum [Nonempty U] [Nonempty T] (β : ℝ) (x : U × T → ℝ) :
    ∑ a, gmmg β a x = 1 := by
  rw [Fintype.sum_prod_type]
  have hW := (gmmW_pos β x).ne'
  have h : ∀ u, ∑ t, gmmg β (u, t) x = (gmmS β u x)⁻¹ * (gmmW β x)⁻¹ := by
    intro u
    have hS := (gmmS_pos β u x).ne'
    simp only [gmmg]
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    change gmmS β u x * _ * _ = _
    field_simp
  simp_rw [h]
  rw [← Finset.sum_mul]
  change gmmW β x * _ = _
  field_simp

lemma gmmg_le_one [Nonempty U] [Nonempty T] (β : ℝ) (a : U × T) (x : U × T → ℝ) :
    gmmg β a x ≤ 1 := by
  rw [← gmmg_sum β x]
  exact Finset.single_le_sum (fun b _ => gmmg_nonneg β b x) (Finset.mem_univ a)

lemma gmmq_nonneg [Nonempty T] (β : ℝ) (a b : U × T) (x : U × T → ℝ) : 0 ≤ gmmq β a b x :=
  div_nonneg (Real.exp_pos _).le (gmmS_pos β a.1 x).le

lemma gmmq_le_one [Nonempty T] (β : ℝ) (a b : U × T) (h : a.1 = b.1) (x : U × T → ℝ) :
    gmmq β a b x ≤ 1 := by
  unfold gmmq
  rw [div_le_one (gmmS_pos β a.1 x), h]
  exact gmm_exp_le_S β b.1 b.2 x

lemma gmmg_le_q [Nonempty U] [Nonempty T] (β : ℝ) (a b : U × T) (h : a.1 = b.1)
    (x : U × T → ℝ) : gmmg β b x ≤ gmmq β a b x := by
  unfold gmmg gmmq
  rw [h]
  have hS := gmmS_pos β b.1 x
  have hW := gmmW_pos β x
  have h1 := gmm_Sinv_le_W β b.1 x
  have he := Real.exp_pos (β * x b)
  rw [div_eq_mul_inv, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ he.le
  rw [show ((gmmS β b.1 x) ^ 2)⁻¹ * (gmmW β x)⁻¹
      = (gmmS β b.1 x)⁻¹ * ((gmmS β b.1 x) * gmmW β x)⁻¹ by field_simp]
  refine mul_le_of_le_one_right (inv_pos.2 hS).le ?_
  rw [inv_le_one₀ (by positivity)]
  calc (1 : ℝ) = gmmS β b.1 x * (gmmS β b.1 x)⁻¹ := by field_simp
    _ ≤ gmmS β b.1 x * gmmW β x := mul_le_mul_of_nonneg_left h1 hS.le

section Hess
variable [DecidableEq U] [DecidableEq T]

lemma gmmH_symm [Nonempty T] (β : ℝ) (a b : U × T) (x : U × T → ℝ) :
    gmmH β a b x = gmmH β b a x := by
  unfold gmmH
  by_cases hab : a = b
  · subst hab; rfl
  rw [if_neg hab, if_neg (Ne.symm hab)]
  by_cases h1 : a.1 = b.1
  · rw [if_pos h1, if_pos h1.symm]
    obtain ⟨u, t⟩ := a
    obtain ⟨v, s⟩ := b
    simp only at h1
    subst h1
    simp only [gmmg, gmmq]
    ring
  · rw [if_neg h1, if_neg (Ne.symm h1)]
    ring

lemma gmmH_rowsum [Nonempty U] [Nonempty T] (β : ℝ) (a : U × T) (x : U × T → ℝ) :
    ∑ b, gmmH β a b x = 0 := by
  unfold gmmH
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq,
    ← Finset.mul_sum, ← Finset.mul_sum, gmmg_sum, if_pos (Finset.mem_univ a)]
  have h : ∑ b : U × T, (if a.1 = b.1 then gmmg β a x * gmmq β a b x else 0) = gmmg β a x := by
    rw [Fintype.sum_prod_type, Finset.sum_eq_single a.1]
    · simp only [if_true]
      rw [← Finset.mul_sum]
      have hS := (gmmS_pos β a.1 x).ne'
      have : ∑ s, gmmq β a (a.1, s) x = 1 := by
        simp only [gmmq]
        rw [← Finset.sum_div]
        exact div_self hS
      rw [this, mul_one]
    · intro v _ hv
      exact Finset.sum_eq_zero fun s _ => if_neg (Ne.symm hv)
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [h]
  ring

lemma gmmH_abs_le [Nonempty U] [Nonempty T] {β : ℝ} (hβ : 0 < β) (a b : U × T)
    (x : U × T → ℝ) : |gmmH β a b x| ≤ 4 * β := by
  unfold gmmH
  have g0 := gmmg_nonneg β a x
  have g1 := gmmg_le_one β a x
  have g0' := gmmg_nonneg β b x
  have g1' := gmmg_le_one β b x
  have hA : |(if a = b then gmmg β a x else 0)| ≤ 1 := by
    split_ifs
    · rw [abs_of_nonneg g0]; exact g1
    · simp
  have hB : |(if a.1 = b.1 then gmmg β a x * gmmq β a b x else 0)| ≤ 1 := by
    split_ifs with h
    · have q0 := gmmq_nonneg β a b x
      have q1 := gmmq_le_one β a b h x
      rw [abs_of_nonneg (mul_nonneg g0 q0)]
      exact mul_le_one₀ g1 q0 q1
    · simp
  have hC : |gmmg β a x * gmmg β b x| ≤ 1 := by
    rw [abs_of_nonneg (mul_nonneg g0 g0')]
    exact mul_le_one₀ g1 g0' g1'
  rw [abs_mul, abs_of_pos hβ]
  have : |(if a = b then gmmg β a x else 0)
      - 2 * (if a.1 = b.1 then gmmg β a x * gmmq β a b x else 0) + gmmg β a x * gmmg β b x|
      ≤ 4 := by
    set A := (if a = b then gmmg β a x else 0)
    set B := (if a.1 = b.1 then gmmg β a x * gmmq β a b x else 0)
    set D := gmmg β a x * gmmg β b x
    have e1 := abs_add_le (A - 2 * B) D
    have e2 := abs_sub A (2 * B)
    rw [abs_mul, abs_two] at e2
    linarith
  nlinarith

end Hess

end SmoothMinMax

section Coeff2
variable {ι : Type*} [Fintype ι]
local notation "PR" j => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) j

lemma gmm_coeff_sq {f : (ι → ℝ) → ℝ} {x : ι → ℝ} {c : ι → ℝ}
    (hf : HasFDerivAt f (∑ b, c b • PR b) x) :
    HasFDerivAt (fun y => f y ^ 2) (∑ b, (2 * f x * c b) • PR b) x := by
  have h := gmm_coeff_mul hf hf
  have e : (fun y => f y ^ 2) = fun y => f y * f y := by funext y; ring
  rw [e]
  refine h.congr_fderiv (Finset.sum_congr rfl fun b _ => ?_)
  congr 1; ring

end Coeff2

section SmoothMinMax2

variable {U T : Type*} [Fintype U] [Fintype T] [DecidableEq U] [DecidableEq T]

local notation "PR" j => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : U × T => ℝ) j

lemma gmmS_hasFDerivAt (β : ℝ) (u : U) (x : U × T → ℝ) :
    HasFDerivAt (gmmS β u)
      (∑ b, (if b.1 = u then β * Real.exp (β * x b) else 0) • PR b) x := by
  have h := gmm_coeff_sum (ι := U × T) (κ := T) (fun t => gmm_coeff_exp β (u, t) x)
  refine h.congr_fderiv (Finset.sum_congr rfl fun b _ => ?_)
  congr 1
  obtain ⟨v, s⟩ := b
  by_cases hv : v = u
  · subst hv; simp [Prod.ext_iff]
  · simp [Prod.ext_iff, hv]

lemma gmmW_hasFDerivAt [Nonempty U] [Nonempty T] (β : ℝ) (x : U × T → ℝ) :
    HasFDerivAt (gmmW β) (∑ b, (-(β * gmmW β x * gmmg β b x)) • PR b) x := by
  have h := gmm_coeff_sum (κ := U)
    (fun u => gmm_coeff_inv (gmmS_hasFDerivAt β u x) (gmmS_pos β u x).ne')
  refine h.congr_fderiv (Finset.sum_congr rfl fun b _ => ?_)
  congr 1
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hS := (gmmS_pos β b.1 x).ne'
  have hW := (gmmW_pos β x).ne'
  unfold gmmg
  generalize gmmW β x = W at hW ⊢
  field_simp

lemma gmmF_hasFDerivAt [Nonempty U] [Nonempty T] {β : ℝ} (hβ : β ≠ 0) (x : U × T → ℝ) :
    HasFDerivAt (gmmF β) (∑ b, gmmg β b x • PR b) x := by
  have h := gmm_coeff_const_mul
    (gmm_coeff_log (gmmW_hasFDerivAt β x) (gmmW_pos β x).ne') (-β⁻¹)
  refine h.congr_fderiv (Finset.sum_congr rfl fun b _ => ?_)
  congr 1
  have hW := (gmmW_pos β x).ne'
  field_simp

lemma gmmg_hasFDerivAt [Nonempty U] [Nonempty T] (β : ℝ) (a : U × T) (x : U × T → ℝ) :
    HasFDerivAt (gmmg β a) (∑ b, gmmH β a b x • PR b) x := by
  have hS := (gmmS_pos β a.1 x).ne'
  have hW := (gmmW_pos β x).ne'
  have h := gmm_coeff_mul (gmm_coeff_mul (gmm_coeff_exp β a x)
    (gmm_coeff_inv (gmm_coeff_sq (gmmS_hasFDerivAt β a.1 x)) (pow_ne_zero 2 hS)))
    (gmm_coeff_inv (gmmW_hasFDerivAt β x) hW)
  have e : gmmg β a = fun y : U × T → ℝ =>
      Real.exp (β * y a) * ((gmmS β a.1 y) ^ 2)⁻¹ * (gmmW β y)⁻¹ := by funext y; rfl
  rw [e]
  refine h.congr_fderiv (Finset.sum_congr rfl fun b _ => ?_)
  congr 1
  unfold gmmH
  by_cases hab : a = b
  · subst hab
    simp only [if_true]
    unfold gmmg gmmq
    field_simp
    ring
  · rw [if_neg hab, if_neg (Ne.symm hab)]
    by_cases h1 : a.1 = b.1
    · rw [if_pos h1, if_pos h1.symm]
      obtain ⟨u, t⟩ := a
      obtain ⟨v, s⟩ := b
      simp only at h1
      subst h1
      simp only [gmmg, gmmq]
      field_simp
      ring
    · rw [if_neg h1, if_neg (Ne.symm h1)]
      simp only [gmmg]
      field_simp
      ring

lemma gmmg_continuous [Nonempty U] [Nonempty T] (β : ℝ) (a : U × T) :
    Continuous (gmmg (T := T) β a) :=
  continuous_iff_continuousAt.2 fun x => (gmmg_hasFDerivAt β a x).continuousAt

lemma gmmF_continuous [Nonempty U] [Nonempty T] {β : ℝ} (hβ : β ≠ 0) :
    Continuous (gmmF (U := U) (T := T) β) :=
  continuous_iff_continuousAt.2 fun x => (gmmF_hasFDerivAt hβ x).continuousAt

lemma gmmS_continuous (β : ℝ) (u : U) : Continuous (gmmS (T := T) β u) :=
  continuous_iff_continuousAt.2 fun x => (gmmS_hasFDerivAt β u x).continuousAt

lemma gmmH_continuous [Nonempty U] [Nonempty T] (β : ℝ) (a b : U × T) :
    Continuous (gmmH β a b) := by
  have hq : Continuous (gmmq (T := T) β a b) := by
    unfold gmmq
    exact Continuous.div (by fun_prop) (gmmS_continuous β a.1)
      (fun x => (gmmS_pos β a.1 x).ne')
  have hg := gmmg_continuous (T := T) β a
  have hg' := gmmg_continuous (T := T) β b
  unfold gmmH
  split_ifs
  · exact continuous_const.mul ((hg.sub (continuous_const.mul (hg.mul hq))).add (hg.mul hg'))
  · exact continuous_const.mul ((hg.sub (continuous_const.mul continuous_const)).add
      (hg.mul hg'))
  · exact continuous_const.mul ((continuous_const.sub (continuous_const.mul (hg.mul hq))).add
      (hg.mul hg'))
  · exact continuous_const.mul ((continuous_const.sub (continuous_const.mul
      continuous_const)).add (hg.mul hg'))

end SmoothMinMax2

section Quad

lemma gmm_quad_of_rowsum {ι : Type*} [Fintype ι] (H Δ : ι → ι → ℝ)
    (hsym : ∀ i j, H i j = H j i) (hrow : ∀ i, ∑ j, H i j = 0) :
    ∑ i, ∑ j, Δ i j * H i j
      = -(1 / 2) * ∑ i, ∑ j, H i j * (Δ i i + Δ j j - Δ i j - Δ j i) := by
  have e1 : ∑ i, ∑ j, H i j * (Δ i i + Δ j j - Δ i j - Δ j i)
      = ∑ i, ∑ j, H i j * Δ i i + ∑ i, ∑ j, H i j * Δ j j
        - ∑ i, ∑ j, H i j * Δ i j - ∑ i, ∑ j, H i j * Δ j i := by
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have e2 : ∑ i, ∑ j, H i j * Δ i i = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← Finset.sum_mul, hrow, zero_mul]
  have e3 : ∑ i, ∑ j, H i j * Δ j j = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← Finset.sum_mul, show ∑ i, H i j = ∑ i, H j i from
      Finset.sum_congr rfl fun i _ => hsym i j, hrow, zero_mul]
  have e4 : ∑ i, ∑ j, H i j * Δ j i = ∑ i, ∑ j, Δ i j * H i j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hsym]; ring
  have e5 : ∑ i, ∑ j, H i j * Δ i j = ∑ i, ∑ j, Δ i j * H i j :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [e1, e2, e3, e4, e5]
  ring

variable {U T : Type*} [Fintype U] [Fintype T] [DecidableEq U] [DecidableEq T]
  [Nonempty U] [Nonempty T]

/-- The key sign lemma: the Hessian of the smooth min-max pairs nonnegatively with any
covariance difference whose increments grow inside blocks and shrink across blocks. -/
theorem gmm_hess_nonneg {β : ℝ} (hβ : 0 < β) (x : U × T → ℝ) (Δ : U × T → U × T → ℝ)
    (hs : ∀ a b : U × T, a.1 = b.1 → 0 ≤ Δ a a + Δ b b - Δ a b - Δ b a)
    (hd : ∀ a b : U × T, a.1 ≠ b.1 → Δ a a + Δ b b - Δ a b - Δ b a ≤ 0) :
    0 ≤ ∑ a, ∑ b, Δ a b * gmmH β a b x := by
  rw [gmm_quad_of_rowsum (fun a b => gmmH β a b x) Δ (fun a b => gmmH_symm β a b x)
    (fun a => gmmH_rowsum β a x)]
  have : ∑ a, ∑ b, gmmH β a b x * (Δ a a + Δ b b - Δ a b - Δ b a) ≤ 0 := by
    refine Finset.sum_nonpos fun a _ => Finset.sum_nonpos fun b _ => ?_
    by_cases hab : a = b
    · subst hab
      have : Δ a a + Δ a a - Δ a a - Δ a a = 0 := by ring
      rw [this, mul_zero]
    by_cases h1 : a.1 = b.1
    · have hH : gmmH β a b x ≤ 0 := by
        unfold gmmH
        rw [if_neg hab, if_pos h1]
        have g0 := gmmg_nonneg β a x
        have hq := gmmg_le_q β a b h1 x
        have q0 := gmmq_nonneg β a b x
        have : gmmg β a x * gmmg β b x ≤ gmmg β a x * gmmq β a b x :=
          mul_le_mul_of_nonneg_left hq g0
        have : 0 ≤ gmmg β a x * gmmq β a b x := mul_nonneg g0 q0
        nlinarith
      exact mul_nonpos_of_nonpos_of_nonneg hH (hs a b h1)
    · have hH : 0 ≤ gmmH β a b x := by
        unfold gmmH
        rw [if_neg hab, if_neg h1]
        have := mul_nonneg (gmmg_nonneg β a x) (gmmg_nonneg β b x)
        nlinarith
      exact mul_nonpos_of_nonneg_of_nonpos hH (hd a b h1)
  nlinarith

end Quad

section Bounds

variable {U T : Type*} [Fintype U] [Fintype T] [Nonempty U] [Nonempty T]

lemma gmmS_le_card {β : ℝ} (hβ : 0 < β) (u : U) (x : U × T → ℝ) :
    gmmS β u x ≤ (Fintype.card T : ℝ) * Real.exp (β * ⨆ t, x (u, t)) := by
  have hb : BddAbove (Set.range fun t => x (u, t)) := (Set.finite_range _).bddAbove
  have : gmmS β u x ≤ ∑ _t : T, Real.exp (β * ⨆ t, x (u, t)) :=
    Finset.sum_le_sum fun t _ => Real.exp_le_exp.2
      (mul_le_mul_of_nonneg_left (le_ciSup hb t) hβ.le)
  simpa using this

lemma gmmS_ge_max (β : ℝ) (u : U) (x : U × T → ℝ) :
    Real.exp (β * ⨆ t, x (u, t)) ≤ gmmS β u x := by
  obtain ⟨t0, ht0⟩ := exists_eq_ciSup_of_finite (f := fun t => x (u, t))
  rw [← ht0]
  exact gmm_exp_le_S β u t0 x

lemma gmmF_ge {β : ℝ} (hβ : 0 < β) (x : U × T → ℝ) :
    (⨅ u, ⨆ t, x (u, t)) - Real.log (Fintype.card U) / β ≤ gmmF β x := by
  set m := ⨅ u, ⨆ t, x (u, t) with hm
  have hmu : ∀ u, m ≤ ⨆ t, x (u, t) := fun u => ciInf_le (Set.finite_range _).bddBelow u
  have hW : gmmW β x ≤ (Fintype.card U : ℝ) * Real.exp (-(β * m)) := by
    have : gmmW β x ≤ ∑ _u : U, Real.exp (-(β * m)) := by
      refine Finset.sum_le_sum fun u _ => ?_
      calc (gmmS β u x)⁻¹ ≤ (Real.exp (β * ⨆ t, x (u, t)))⁻¹ :=
            inv_anti₀ (Real.exp_pos _) (gmmS_ge_max β u x)
        _ = Real.exp (-(β * ⨆ t, x (u, t))) := (Real.exp_neg _).symm
        _ ≤ Real.exp (-(β * m)) := Real.exp_le_exp.2 (by nlinarith [hmu u])
    simpa using this
  have hc : (0 : ℝ) < Fintype.card U := by exact_mod_cast Fintype.card_pos
  have hl := Real.log_le_log (gmmW_pos β x) hW
  rw [Real.log_mul hc.ne' (Real.exp_pos _).ne', Real.log_exp] at hl
  have h2 : β⁻¹ * Real.log (gmmW β x) ≤ β⁻¹ * (Real.log (Fintype.card U) + -(β * m)) :=
    mul_le_mul_of_nonneg_left hl (inv_nonneg.2 hβ.le)
  have e : β⁻¹ * (Real.log (Fintype.card U) + -(β * m)) = Real.log (Fintype.card U) / β - m := by
    field_simp
    ring
  unfold gmmF
  linarith

lemma gmmF_le {β : ℝ} (hβ : 0 < β) (x : U × T → ℝ) :
    gmmF β x ≤ (⨅ u, ⨆ t, x (u, t)) + Real.log (Fintype.card T) / β := by
  set m := ⨅ u, ⨆ t, x (u, t) with hm
  obtain ⟨u0, hu0⟩ := exists_eq_ciInf_of_finite (f := fun u => ⨆ t, x (u, t))
  have hc : (0 : ℝ) < Fintype.card T := by exact_mod_cast Fintype.card_pos
  have hW : ((Fintype.card T : ℝ) * Real.exp (β * m))⁻¹ ≤ gmmW β x := by
    refine le_trans ?_ (gmm_Sinv_le_W β u0 x)
    refine inv_anti₀ (gmmS_pos β u0 x) ?_
    rw [hm, ← hu0]
    exact gmmS_le_card hβ u0 x
  have hl := Real.log_le_log (by positivity) hW
  rw [Real.log_inv, Real.log_mul hc.ne' (Real.exp_pos _).ne', Real.log_exp] at hl
  have h2 : β⁻¹ * (-(Real.log (Fintype.card T) + β * m)) ≤ β⁻¹ * Real.log (gmmW β x) :=
    mul_le_mul_of_nonneg_left hl (inv_nonneg.2 hβ.le)
  have e : β⁻¹ * (-(Real.log (Fintype.card T) + β * m)) = -(Real.log (Fintype.card T) / β + m) := by
    field_simp
  unfold gmmF
  linarith

lemma gmm_abs_minmax_le (x : U × T → ℝ) : |⨅ u, ⨆ t, x (u, t)| ≤ ∑ a, |x a| := by
  obtain ⟨u0, hu0⟩ := exists_eq_ciInf_of_finite (f := fun u => ⨆ t, x (u, t))
  obtain ⟨t0, ht0⟩ := exists_eq_ciSup_of_finite (f := fun t => x (u0, t))
  rw [← hu0, ← ht0]
  exact Finset.single_le_sum (f := fun a => |x a|) (fun a _ => abs_nonneg _)
    (Finset.mem_univ (u0, t0))

lemma gmmF_abs_le {β : ℝ} (hβ : 0 < β) (x : U × T → ℝ) :
    |gmmF β x| ≤ ∑ a, |x a| + (Real.log (Fintype.card U) + Real.log (Fintype.card T)) / β := by
  have h1 := gmmF_ge hβ x
  have h2 := gmmF_le hβ x
  have h3 := gmm_abs_minmax_le x
  have hU : 0 ≤ Real.log (Fintype.card U) / β :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast Fintype.card_pos)) hβ.le
  have hT : 0 ≤ Real.log (Fintype.card T) / β :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast Fintype.card_pos)) hβ.le
  rw [add_div]
  rw [abs_le] at h3 ⊢
  constructor <;> linarith [h3.1, h3.2]

end Bounds

section Main

lemma gmm_integrable_of_abs_le {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] (X : ι → Ω → ℝ) (hXi : ∀ t, Integrable (X t) P) (g : (ι → ℝ) → ℝ)
    (hg : Measurable g) (hXae : AEMeasurable (fun ω t => X t ω) P) (K : ℝ)
    (hb : ∀ x, |g x| ≤ ∑ t, |x t| + K) :
    Integrable (fun ω => g (fun t => X t ω)) P := by
  refine Integrable.mono' ((integrable_finsetSum Finset.univ fun t _ => (hXi t).abs).add
    (integrable_const K)) (hg.comp_aemeasurable hXae).aestronglyMeasurable
    (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs]
  simpa using hb (fun t => X t ω)

theorem gmm_main {U T Ω Ω' : Type*} [Fintype U] [Fintype T] [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {P : Measure Ω} {Q : Measure Ω'}
    (X : U → T → Ω → ℝ) (Y : U → T → Ω' → ℝ)
    (hX : HasGaussianLaw (fun ω (p : U × T) => X p.1 p.2 ω) P)
    (hY : HasGaussianLaw (fun ω (p : U × T) => Y p.1 p.2 ω) Q)
    (hX0 : ∀ u t, ∫ ω, X u t ω ∂P = 0) (hY0 : ∀ u t, ∫ ω, Y u t ω ∂Q = 0)
    (hsame : ∀ u t s,
      ∫ ω, (X u t ω - X u s ω) ^ 2 ∂P ≤ ∫ ω, (Y u t ω - Y u s ω) ^ 2 ∂Q)
    (hdiff : ∀ u v t s, u ≠ v →
      ∫ ω, (Y u t ω - Y v s ω) ^ 2 ∂Q ≤ ∫ ω, (X u t ω - X v s ω) ^ 2 ∂P) :
    ∫ ω, (⨅ u, ⨆ t, X u t ω) ∂P ≤ ∫ ω, (⨅ u, ⨆ t, Y u t ω) ∂Q := by
  rcases isEmpty_or_nonempty U with hU | hU
  · simp
  rcases isEmpty_or_nonempty T with hT | hT
  · simp
  classical
  have hP := hX.isProbabilityMeasure
  have hQ := hY.isProbabilityMeasure
  set μX := P.map (fun ω (p : U × T) => X p.1 p.2 ω) with hμX
  set μY := Q.map (fun ω (p : U × T) => Y p.1 p.2 ω) with hμY
  have : IsGaussian μX := hX.isGaussian_map
  have : IsGaussian μY := hY.isGaussian_map
  set μ := μX.prod μY with hμ
  have hlaw : HasGaussianLaw
      (fun p : (U × T → ℝ) × (U × T → ℝ) => (fun a => p.1 a, fun a => p.2 a)) μ :=
    IsGaussian.hasGaussianLaw_id
  have hfst : ∀ f : (U × T → ℝ) → ℝ, Measurable f →
      ∫ p, f p.1 ∂μ = ∫ ω, f (fun a => X a.1 a.2 ω) ∂P := by
    intro f hf
    have h1 : ∫ p, f p.1 ∂μ = ∫ x, f x ∂(μ.map Prod.fst) :=
      (integral_map measurable_fst.aemeasurable hf.aestronglyMeasurable).symm
    rw [h1, hμ, Measure.map_fst_prod, measure_univ, one_smul, hμX,
      integral_map hX.aemeasurable hf.aestronglyMeasurable]
  have hsnd : ∀ f : (U × T → ℝ) → ℝ, Measurable f →
      ∫ p, f p.2 ∂μ = ∫ ω, f (fun a => Y a.1 a.2 ω) ∂Q := by
    intro f hf
    have h1 : ∫ p, f p.2 ∂μ = ∫ x, f x ∂(μ.map Prod.snd) :=
      (integral_map measurable_snd.aemeasurable hf.aestronglyMeasurable).symm
    rw [h1, hμ, Measure.map_snd_prod, measure_univ, one_smul, hμY,
      integral_map hY.aemeasurable hf.aestronglyMeasurable]
  have hX0' : ∀ a : U × T, ∫ p, p.1 a ∂μ = 0 := fun a => by
    rw [hfst (fun x => x a) (measurable_pi_apply a)]; exact hX0 a.1 a.2
  have hY0' : ∀ a : U × T, ∫ p, p.2 a ∂μ = 0 := fun a => by
    rw [hsnd (fun x => x a) (measurable_pi_apply a)]; exact hY0 a.1 a.2
  have hcross : ∀ a b : U × T, ∫ p, p.1 a * p.2 b ∂μ = 0 := by
    intro a b
    rw [hμ, integral_prod_mul (fun x : U × T → ℝ => x a) (fun y : U × T → ℝ => y b)]
    have : ∫ x, x a ∂μX = 0 := by
      rw [hμX, integral_map hX.aemeasurable (measurable_pi_apply a).aestronglyMeasurable]
      exact hX0 a.1 a.2
    rw [this, zero_mul]
  have hXm : ∀ a : U × T, MemLp (fun p : (U × T → ℝ) × (U × T → ℝ) => p.1 a) 2 μ :=
    fun a => (hlaw.fst.eval a).memLp_two
  have hYm : ∀ a : U × T, MemLp (fun p : (U × T → ℝ) × (U × T → ℝ) => p.2 a) 2 μ :=
    fun a => (hlaw.snd.eval a).memLp_two
  set Δ : U × T → U × T → ℝ := fun a b =>
    ∫ p, p.2 a * p.2 b ∂μ - ∫ p, p.1 a * p.1 b ∂μ with hΔ
  have he : ∀ a b : U × T, Δ a a + Δ b b - Δ a b - Δ b a
      = ∫ ω, (Y a.1 a.2 ω - Y b.1 b.2 ω) ^ 2 ∂Q - ∫ ω, (X a.1 a.2 ω - X b.1 b.2 ω) ^ 2 ∂P := by
    intro a b
    have h1 := gmm_sq_sub (fun (a : U × T) (p : (U × T → ℝ) × (U × T → ℝ)) => p.1 a) hXm a b
    have h2 := gmm_sq_sub (fun (a : U × T) (p : (U × T → ℝ) × (U × T → ℝ)) => p.2 a) hYm a b
    rw [hfst (fun x => (x a - x b) ^ 2) (by fun_prop)] at h1
    rw [hsnd (fun x => (x a - x b) ^ 2) (by fun_prop)] at h2
    simp only at h1 h2
    rw [h1, h2, hΔ]
    ring
  have hs : ∀ a b : U × T, a.1 = b.1 → 0 ≤ Δ a a + Δ b b - Δ a b - Δ b a := by
    intro a b hab
    rw [he]
    obtain ⟨u, t⟩ := a
    obtain ⟨v, s⟩ := b
    simp only at hab ⊢
    subst hab
    linarith [hsame u t s]
  have hd : ∀ a b : U × T, a.1 ≠ b.1 → Δ a a + Δ b b - Δ a b - Δ b a ≤ 0 := by
    intro a b hab
    rw [he]
    linarith [hdiff a.1 b.1 a.2 b.2 hab]
  have hXi : ∀ a : U × T, Integrable (fun ω => X a.1 a.2 ω) P := fun a => (hX.eval a).integrable
  have hYi : ∀ a : U × T, Integrable (fun ω => Y a.1 a.2 ω) Q := fun a => (hY.eval a).integrable
  obtain ⟨mm, hmm⟩ : ∃ f : (U × T → ℝ) → ℝ, f = fun x => ⨅ u, ⨆ t, x (u, t) := ⟨_, rfl⟩
  have hmmm : Measurable mm := by
    rw [hmm]
    exact Measurable.iInf fun u => Measurable.iSup fun t => measurable_pi_apply (u, t)
  have hmmb : ∀ x, |mm x| ≤ ∑ a, |x a| := fun x => by rw [hmm]; exact gmm_abs_minmax_le x
  have hIX : Integrable (fun ω => mm (fun a => X a.1 a.2 ω)) P :=
    gmm_integrable_of_abs_le (fun a ω => X a.1 a.2 ω) hXi mm hmmm hX.aemeasurable 0
      (fun x => by rw [add_zero]; exact hmmb x)
  have hIY : Integrable (fun ω => mm (fun a => Y a.1 a.2 ω)) Q :=
    gmm_integrable_of_abs_le (fun a ω => Y a.1 a.2 ω) hYi mm hmmm hY.aemeasurable 0
      (fun x => by rw [add_zero]; exact hmmb x)
  set Lg := Real.log (Fintype.card U) + Real.log (Fintype.card T) with hLg
  have key : ∀ β : ℝ, 0 < β → ∫ ω, mm (fun a => X a.1 a.2 ω) ∂P
      ≤ ∫ ω, mm (fun a => Y a.1 a.2 ω) ∂Q + Lg / β := by
    intro β hβ
    have hgb : ∀ (a : U × T) (x : U × T → ℝ), |gmmg β a x| ≤ 1 + 4 * β := fun a x => by
      rw [abs_of_nonneg (gmmg_nonneg β a x)]
      linarith [gmmg_le_one β a x]
    have hHb : ∀ (a b : U × T) (x : U × T → ℝ), |gmmH β a b x| ≤ 1 + 4 * β := fun a b x => by
      linarith [gmmH_abs_le hβ a b x]
    have hc := gmm_interp (P := μ) (fun (a : U × T) (p : (U × T → ℝ) × (U × T → ℝ)) => p.1 a)
      (fun (a : U × T) (p : (U × T → ℝ) × (U × T → ℝ)) => p.2 a) hlaw hX0' hY0'
      hcross (gmmF β) (gmmg β) (gmmH β) (gmmF_hasFDerivAt hβ.ne') (gmmg_hasFDerivAt β)
      (gmmH_continuous β) (1 + 4 * β) hgb hHb _ (gmmF_abs_le hβ)
      (fun x => gmm_hess_nonneg hβ x Δ hs hd)
    rw [hfst (gmmF β) (gmmF_continuous hβ.ne').measurable,
      hsnd (gmmF β) (gmmF_continuous hβ.ne').measurable] at hc
    have hFX : Integrable (fun ω => gmmF β (fun a => X a.1 a.2 ω)) P :=
      gmm_integrable_of_abs_le (fun (a : U × T) ω => X a.1 a.2 ω) hXi (gmmF β)
        (gmmF_continuous hβ.ne').measurable hX.aemeasurable _ (gmmF_abs_le hβ)
    have hFY : Integrable (fun ω => gmmF β (fun a => Y a.1 a.2 ω)) Q :=
      gmm_integrable_of_abs_le (fun (a : U × T) ω => Y a.1 a.2 ω) hYi (gmmF β)
        (gmmF_continuous hβ.ne').measurable hY.aemeasurable _ (gmmF_abs_le hβ)
    have h1 : ∫ ω, mm (fun a => X a.1 a.2 ω) ∂P
        ≤ ∫ ω, (gmmF β (fun a => X a.1 a.2 ω) + Real.log (Fintype.card U) / β) ∂P :=
      integral_mono hIX (hFX.add (integrable_const _)) fun ω => by
        have := gmmF_ge hβ (fun a => X a.1 a.2 ω)
        rw [hmm]
        linarith
    have h2 : ∫ ω, gmmF β (fun a => Y a.1 a.2 ω) ∂Q
        ≤ ∫ ω, (mm (fun a => Y a.1 a.2 ω) + Real.log (Fintype.card T) / β) ∂Q :=
      integral_mono hFY (hIY.add (integrable_const _)) fun ω => by
        have := gmmF_le hβ (fun a => Y a.1 a.2 ω)
        rw [hmm]
        linarith
    rw [integral_add hIY (integrable_const _), integral_const, probReal_univ, one_smul] at h2
    rw [integral_add hFX (integrable_const _), integral_const, probReal_univ, one_smul] at h1
    have : Lg / β = Real.log (Fintype.card U) / β + Real.log (Fintype.card T) / β := by
      rw [hLg, add_div]
    linarith
  have eX : ∫ ω, (⨅ u, ⨆ t, X u t ω) ∂P = ∫ ω, mm (fun a => X a.1 a.2 ω) ∂P := by rw [hmm]
  have eY : ∫ ω, (⨅ u, ⨆ t, Y u t ω) ∂Q = ∫ ω, mm (fun a => Y a.1 a.2 ω) ∂Q := by rw [hmm]
  rw [eX, eY]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hL0 : 0 ≤ Lg := add_nonneg (Real.log_nonneg (by exact_mod_cast Fintype.card_pos))
    (Real.log_nonneg (by exact_mod_cast Fintype.card_pos))
  have hβ : 0 < (Lg + 1) / ε := div_pos (by linarith) hε
  refine (key _ hβ).trans ?_
  gcongr
  rw [div_div_eq_mul_div, div_le_iff₀ (by linarith)]
  nlinarith

end Main

end GaussianMatrix

open GaussianMatrix

theorem solution {U T Ω Ω' : Type*} [Fintype U] [Fintype T] [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {P : Measure Ω} {Q : Measure Ω'}
    (X : U → T → Ω → ℝ) (Y : U → T → Ω' → ℝ)
    (hX : HasGaussianLaw (fun ω (p : U × T) => X p.1 p.2 ω) P)
    (hY : HasGaussianLaw (fun ω (p : U × T) => Y p.1 p.2 ω) Q)
    (hX0 : ∀ u t, ∫ ω, X u t ω ∂P = 0) (hY0 : ∀ u t, ∫ ω, Y u t ω ∂Q = 0)
    (hsame : ∀ u t s,
      ∫ ω, (X u t ω - X u s ω) ^ 2 ∂P ≤ ∫ ω, (Y u t ω - Y u s ω) ^ 2 ∂Q)
    (hdiff : ∀ u v t s, u ≠ v →
      ∫ ω, (Y u t ω - Y v s ω) ^ 2 ∂Q ≤ ∫ ω, (X u t ω - X v s ω) ^ 2 ∂P) :
    ∫ ω, (⨅ u, ⨆ t, X u t ω) ∂P ≤ ∫ ω, (⨅ u, ⨆ t, Y u t ω) ∂Q :=
  gmm_main X Y hX hY hX0 hY0 hsame hdiff
