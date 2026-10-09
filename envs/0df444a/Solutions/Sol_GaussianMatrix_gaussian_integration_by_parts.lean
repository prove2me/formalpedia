-- Prove2me | solution 1 for GaussianMatrix.gaussian_integration_by_parts
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T07:44:36.454293+00:00
-- url     : https://prove2.me/submissions/efa067ce-71ae-4d69-9d2c-b4bb4cbeb4e0

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

/-!
# Gaussian integration by parts

`𝔼[U · G(V)] = ∑ⱼ Cov(U, Vⱼ) 𝔼[∂ⱼ G(V)]` for jointly Gaussian `(U, V)` with `U` centered and
`G` bounded with bounded continuous partial derivatives. Proof: regress `V` on `U`
(`V = c U + W` with `W` independent of `U`), apply the one-dimensional identity
`∫ x h(x) dN(0,v) = v ∫ h'(x) dN(0,v)` in the `U` variable and integrate over `W` (Fubini).
-/

namespace GaussianMatrix

open Real in
lemma sf_hasDerivAt_pdf (v : NNReal) (hv : v ≠ 0) (x : ℝ) :
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

lemma sf_ibp_real (v : NNReal) (h h' : ℝ → ℝ) (hh : ∀ x, HasDerivAt h (h' x) x)
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
    (fun x _ => hh x) (fun x _ => sf_hasDerivAt_pdf v hv x) ?_ ?_ ?_
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


lemma sf_indep_regress {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω] {P : Measure Ω}
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


theorem sf_gaussian_ibp {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
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
  have hind := sf_indep_regress U W hUW hcovW
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
    have := sf_ibp_real σ2.toNNReal (fun u => G (u • c + w)) (fun u => F2 (u, w)) ?_
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

end GaussianMatrix

open GaussianMatrix

theorem solution {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    {P : Measure Ω} (U : Ω → ℝ) (V : ι → Ω → ℝ)
    (hUV : HasGaussianLaw (fun ω => (U ω, fun j => V j ω)) P) (hU0 : ∫ ω, U ω ∂P = 0)
    (G : (ι → ℝ) → ℝ) (G' : ι → (ι → ℝ) → ℝ)
    (hG : ∀ x, HasFDerivAt G
      (∑ j, G' j x • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) j) x)
    (hG'c : ∀ j, Continuous (G' j)) (C : ℝ) (hGb : ∀ x, |G x| ≤ C)
    (hG'b : ∀ j x, |G' j x| ≤ C) :
    ∫ ω, U ω * G (fun j => V j ω) ∂P = ∑ j, cov[U, V j; P] * ∫ ω, G' j (fun j => V j ω) ∂P :=
  sf_gaussian_ibp U V hUV hU0 G G' hG hG'c C hGb hG'b
