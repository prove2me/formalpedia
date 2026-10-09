-- Prove2me | solution 1 for GaussianMatrix.slepian_tail_comparison
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T08:37:03.866885+00:00
-- url     : https://prove2.me/submissions/9d3a4a1a-f27d-4f32-9255-5cf5c1b6bb88

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

/-!
# Slepian's inequality (tail comparison of Gaussian maxima)

Proof by Gaussian interpolation (Slepian 1962; Chatterjee's interpolation proof, as in
Vershynin, HDP Thm 7.2.1):

* `sl_gaussian_ibp` — Gaussian integration by parts (copied from the Sudakov–Fernique solution);
* `slF φ x = ∏ₜ φ(xₜ)` with gradient `slG` and Hessian `slH`; for `φ ≥ 0` nonincreasing the
  off-diagonal Hessian entries `φ'(xᵢ)φ'(xⱼ)∏_{t≠i,j}φ(xₜ)` are nonnegative;
* `sl_compare` — along `Z(θ) = cos θ X + sin θ Y`, `θ ↦ 𝔼 slF φ (Z θ)` is nonincreasing on
  `[0, π/2]` (equal variances kill the diagonal terms), so `𝔼 F(Y) ≤ 𝔼 F(X)`;
* `sl_cutoff` — the smooth cutoff `φ_δ(u) = smoothTransition((τ + δ - u)/δ)`;
* `sl_main` — `Q(max Y ≤ τ) ≤ 𝔼 F_δ(Y) ≤ 𝔼 F_δ(X) ≤ P(max X ≤ τ + δ)`, then `δ ↓ 0` by
  right-continuity of the distribution function of `max X`, and take complements.
-/

namespace GaussianMatrix

open Real in
lemma sl_hasDerivAt_pdf (v : NNReal) (hv : v ≠ 0) (x : ℝ) :
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

lemma sl_ibp_real (v : NNReal) (h h' : ℝ → ℝ) (hh : ∀ x, HasDerivAt h (h' x) x)
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
    (fun x _ => hh x) (fun x _ => sl_hasDerivAt_pdf v hv x) ?_ ?_ ?_
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


lemma sl_indep_regress {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω] {P : Measure Ω}
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


theorem sl_gaussian_ibp {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
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
  have hind := sl_indep_regress U W hUW hcovW
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
    have := sl_ibp_real σ2.toNNReal (fun u => G (u • c + w)) (fun u => F2 (u, w)) ?_
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
lemma sl_cov_DZ (X Y : ι → Ω → ℝ)
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
lemma sl_sq_sub (X : ι → Ω → ℝ) (hXm : ∀ t, MemLp (X t) 2 P) (i j : ι) :
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

section ProdFun

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local notation "PR" j => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) j

/-- `F(x) = ∏ₜ φ(xₜ)`, a smooth surrogate of the indicator of `{max x ≤ τ}`. -/
noncomputable def slF (φ : ℝ → ℝ) (x : ι → ℝ) : ℝ := ∏ t, φ (x t)

/-- the partial derivative `∂ᵢF` -/
noncomputable def slG (φ φ' : ℝ → ℝ) (i : ι) (x : ι → ℝ) : ℝ :=
  φ' (x i) * ∏ t ∈ Finset.univ.erase i, φ (x t)

/-- the second partial derivative `∂ⱼ∂ᵢF` -/
noncomputable def slH (φ φ' φ'' : ℝ → ℝ) (i j : ι) (x : ι → ℝ) : ℝ :=
  if j = i then φ'' (x i) * ∏ t ∈ Finset.univ.erase i, φ (x t)
  else φ' (x i) * (φ' (x j) * ∏ t ∈ (Finset.univ.erase i).erase j, φ (x t))

omit [DecidableEq ι] in
lemma sl_coord_hasFDerivAt (φ φ' : ℝ → ℝ) (hφ : ∀ u, HasDerivAt φ (φ' u) u) (t : ι)
    (x : ι → ℝ) : HasFDerivAt (fun y : ι → ℝ => φ (y t)) (φ' (x t) • PR t) x := by
  have h1 : HasDerivAt φ (φ' (x t)) ((PR t) x) := hφ (x t)
  exact h1.comp_hasFDerivAt x (PR t).hasFDerivAt

lemma slF_hasFDerivAt (φ φ' : ℝ → ℝ) (hφ : ∀ u, HasDerivAt φ (φ' u) u) (x : ι → ℝ) :
    HasFDerivAt (slF φ) (∑ i, slG φ φ' i x • PR i) x := by
  have h := HasFDerivAt.finsetProd (u := Finset.univ)
    (fun t _ => sl_coord_hasFDerivAt φ φ' hφ t x)
  refine h.congr_fderiv ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul, slG, mul_comm]

lemma slG_hasFDerivAt (φ φ' φ'' : ℝ → ℝ) (hφ : ∀ u, HasDerivAt φ (φ' u) u)
    (hφ' : ∀ u, HasDerivAt φ' (φ'' u) u) (i : ι) (x : ι → ℝ) :
    HasFDerivAt (slG φ φ' i) (∑ j, slH φ φ' φ'' i j x • PR j) x := by
  have h1 := sl_coord_hasFDerivAt φ' φ'' hφ' i x
  have h2 := HasFDerivAt.finsetProd (u := Finset.univ.erase i)
    (fun t _ => sl_coord_hasFDerivAt φ φ' hφ t x)
  have h := h1.mul h2
  refine h.congr_fderiv ?_
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  simp only [slH, if_true]
  have e : ∑ j ∈ Finset.univ.erase i, slH φ φ' φ'' i j x • (PR j)
      = ∑ j ∈ Finset.univ.erase i,
        (φ' (x i) * (φ' (x j) * ∏ t ∈ (Finset.univ.erase i).erase j, φ (x t))) • (PR j) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [slH, if_neg (Finset.ne_of_mem_erase hj)]
  simp only [slH] at e
  rw [e, add_comm, Finset.smul_sum]
  simp only [smul_smul]
  refine congrArg₂ (· + ·) ?_ ?_
  · rw [mul_comm]
  · refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    ring

variable {φ φ' φ'' : ℝ → ℝ}

omit [Fintype ι] [DecidableEq ι] in
lemma sl_prod_bounds (h0 : ∀ u, 0 ≤ φ u) (h1 : ∀ u, φ u ≤ 1) (s : Finset ι) (x : ι → ℝ) :
    0 ≤ ∏ t ∈ s, φ (x t) ∧ ∏ t ∈ s, φ (x t) ≤ 1 :=
  ⟨Finset.prod_nonneg fun _ _ => h0 _, Finset.prod_le_one (fun _ _ => h0 _) (fun _ _ => h1 _)⟩

omit [DecidableEq ι] in
lemma slF_nonneg (h0 : ∀ u, 0 ≤ φ u) (h1 : ∀ u, φ u ≤ 1) (x : ι → ℝ) : 0 ≤ slF φ x :=
  (sl_prod_bounds h0 h1 _ x).1

omit [DecidableEq ι] in
lemma slF_le_one (h0 : ∀ u, 0 ≤ φ u) (h1 : ∀ u, φ u ≤ 1) (x : ι → ℝ) : slF φ x ≤ 1 :=
  (sl_prod_bounds h0 h1 _ x).2

lemma slG_abs_le (h0 : ∀ u, 0 ≤ φ u) (h1 : ∀ u, φ u ≤ 1) {C : ℝ} (hC1 : ∀ u, |φ' u| ≤ C)
    (i : ι) (x : ι → ℝ) : |slG φ φ' i x| ≤ C := by
  obtain ⟨p0, p1⟩ := sl_prod_bounds h0 h1 (Finset.univ.erase i) x
  rw [slG, abs_mul, abs_of_nonneg p0]
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC1 0)
  calc |φ' (x i)| * _ ≤ C * 1 := mul_le_mul (hC1 _) p1 p0 hC0
    _ = C := mul_one C

lemma slH_abs_le (h0 : ∀ u, 0 ≤ φ u) (h1 : ∀ u, φ u ≤ 1) {C : ℝ} (hC1 : ∀ u, |φ' u| ≤ C)
    (hC2 : ∀ u, |φ'' u| ≤ C) (i j : ι) (x : ι → ℝ) : |slH φ φ' φ'' i j x| ≤ C + C * C := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC1 0)
  unfold slH
  split_ifs with hij
  · obtain ⟨p0, p1⟩ := sl_prod_bounds h0 h1 (Finset.univ.erase i) x
    rw [abs_mul, abs_of_nonneg p0]
    have := mul_le_mul (hC2 (x i)) p1 p0 hC0
    nlinarith
  · obtain ⟨p0, p1⟩ := sl_prod_bounds h0 h1 ((Finset.univ.erase i).erase j) x
    rw [abs_mul, abs_mul, abs_of_nonneg p0]
    have a1 := hC1 (x i)
    have a2 := hC1 (x j)
    have b1 := abs_nonneg (φ' (x i))
    have b2 := abs_nonneg (φ' (x j))
    have : |φ' (x j)| * ∏ t ∈ (Finset.univ.erase i).erase j, φ (x t) ≤ C :=
      (mul_le_mul a2 p1 p0 hC0).trans (le_of_eq (mul_one C))
    have h3 : 0 ≤ |φ' (x j)| * ∏ t ∈ (Finset.univ.erase i).erase j, φ (x t) :=
      mul_nonneg b2 p0
    have := mul_le_mul a1 this h3 hC0
    nlinarith

lemma slH_nonneg_of_ne (h0 : ∀ u, 0 ≤ φ u) (hd : ∀ u, φ' u ≤ 0) {i j : ι} (hij : j ≠ i)
    (x : ι → ℝ) : 0 ≤ slH φ φ' φ'' i j x := by
  rw [slH, if_neg hij]
  have p0 : 0 ≤ ∏ t ∈ (Finset.univ.erase i).erase j, φ (x t) := Finset.prod_nonneg fun _ _ => h0 _
  have := mul_nonpos_of_nonpos_of_nonneg (hd (x j)) p0
  exact mul_nonneg_of_nonpos_of_nonpos (hd (x i)) this

lemma slH_continuous (hφc : Continuous φ) (hφ'c : Continuous φ') (hφ''c : Continuous φ'')
    (i j : ι) : Continuous (slH (ι := ι) φ φ' φ'' i j) := by
  unfold slH
  split_ifs
  · exact (hφ''c.comp (continuous_apply i)).mul
      (continuous_finsetProd _ fun t _ => hφc.comp (continuous_apply t))
  · exact (hφ'c.comp (continuous_apply i)).mul ((hφ'c.comp (continuous_apply j)).mul
      (continuous_finsetProd _ fun t _ => hφc.comp (continuous_apply t)))

end ProdFun


section Compare

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω] {P : Measure Ω}

/-- Slepian's comparison for the smooth product functional `∏ₜ φ(xₜ)`, `φ` nonincreasing:
on one space with `(X, Y)` jointly Gaussian, centered, with vanishing cross-moments, equal
variances and dominated increments, `𝔼 F(Y) ≤ 𝔼 F(X)`. -/
theorem sl_compare (X Y : ι → Ω → ℝ)
    (hXY : HasGaussianLaw (fun ω => (fun t => X t ω, fun t => Y t ω)) P)
    (hX0 : ∀ t, ∫ ω, X t ω ∂P = 0) (hY0 : ∀ t, ∫ ω, Y t ω ∂P = 0)
    (hcross : ∀ s t, ∫ ω, X s ω * Y t ω ∂P = 0)
    (hvar : ∀ t, ∫ ω, X t ω * X t ω ∂P = ∫ ω, Y t ω * Y t ω ∂P)
    (hinc : ∀ s t, ∫ ω, (X s ω - X t ω) ^ 2 ∂P ≤ ∫ ω, (Y s ω - Y t ω) ^ 2 ∂P)
    (φ φ' φ'' : ℝ → ℝ) (hφ : ∀ u, HasDerivAt φ (φ' u) u)
    (hφ' : ∀ u, HasDerivAt φ' (φ'' u) u) (hφ''c : Continuous φ'')
    (h0 : ∀ u, 0 ≤ φ u) (h1 : ∀ u, φ u ≤ 1) (hd : ∀ u, φ' u ≤ 0)
    (C : ℝ) (hC1 : ∀ u, |φ' u| ≤ C) (hC2 : ∀ u, |φ'' u| ≤ C) :
    ∫ ω, slF φ (fun t => Y t ω) ∂P ≤ ∫ ω, slF φ (fun t => X t ω) ∂P := by
  have hP := hXY.isProbabilityMeasure
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC1 0)
  have hφc : Continuous φ := continuous_iff_continuousAt.2 fun u => (hφ u).continuousAt
  have hφ'c : Continuous φ' := continuous_iff_continuousAt.2 fun u => (hφ' u).continuousAt
  have hFc : Continuous (slF (ι := ι) φ) :=
    continuous_iff_continuousAt.2 fun x => (slF_hasFDerivAt φ φ' hφ x).continuousAt
  have hGc : ∀ i, Continuous (slG (ι := ι) φ φ' i) := fun i =>
    continuous_iff_continuousAt.2 fun x => (slG_hasFDerivAt φ φ' φ'' hφ hφ' i x).continuousAt
  have hHc : ∀ i j, Continuous (slH (ι := ι) φ φ' φ'' i j) := fun i j =>
    slH_continuous hφc hφ'c hφ''c i j
  have hXm : ∀ t, MemLp (X t) 2 P := fun t => (hXY.fst.eval t).memLp_two
  have hYm : ∀ t, MemLp (Y t) 2 P := fun t => (hXY.snd.eval t).memLp_two
  have hXi : ∀ t, Integrable (X t) P := fun t => (hXm t).integrable one_le_two
  have hYi : ∀ t, Integrable (Y t) P := fun t => (hYm t).integrable one_le_two
  have hXae : ∀ t, AEMeasurable (X t) P := fun t => (hXm t).aestronglyMeasurable.aemeasurable
  have hYae : ∀ t, AEMeasurable (Y t) P := fun t => (hYm t).aestronglyMeasurable.aemeasurable
  set Z : ℝ → Ω → ι → ℝ := fun θ ω t => Real.cos θ * X t ω + Real.sin θ * Y t ω with hZ
  set D : ℝ → Ω → ι → ℝ := fun θ ω t => -Real.sin θ * X t ω + Real.cos θ * Y t ω with hD
  set B : Ω → ℝ := fun ω => ∑ t, (|X t ω| + |Y t ω|) with hBdef
  have hB : Integrable B P :=
    integrable_finsetSum _ fun t _ => (hXi t).abs.add (hYi t).abs
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
  set Φ : ℝ → ℝ := fun θ => ∫ ω, slF φ (Z θ ω) ∂P with hΦ
  set F' : ℝ → Ω → ℝ := fun θ ω => ∑ i, slG φ φ' i (Z θ ω) * D θ ω i with hF'
  have hderiv : ∀ θ0, HasDerivAt Φ (∫ ω, F' θ0 ω ∂P) θ0 := by
    intro θ0
    have hFm : ∀ θ, AEStronglyMeasurable (fun ω => slF φ (Z θ ω)) P := fun θ =>
      (hFc.measurable.comp_aemeasurable (hZae θ)).aestronglyMeasurable
    have hFint : Integrable (fun ω => slF φ (Z θ0 ω)) P := by
      refine Integrable.mono' (integrable_const 1) (hFm θ0) (ae_of_all _ fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (slF_nonneg h0 h1 _)]
      exact slF_le_one h0 h1 _
    have hF'm : AEStronglyMeasurable (F' θ0) P := by
      refine (Finset.aemeasurable_fun_sum _ fun i _ => ?_).aestronglyMeasurable
      exact ((hGc i).measurable.comp_aemeasurable (hZae θ0)).mul (hDae θ0 i)
    have hbound : ∀ θ ω, ‖F' θ ω‖ ≤ C * B ω := by
      intro θ ω
      rw [Real.norm_eq_abs, hF', hBdef, Finset.mul_sum]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [abs_mul]
      exact mul_le_mul (slG_abs_le h0 h1 hC1 i _) (hDb θ ω i) (abs_nonneg _) hC0
    have hdiff : ∀ ω θ, HasDerivAt (fun θ => slF φ (Z θ ω)) (F' θ ω) θ := by
      intro ω θ
      have hZd : HasDerivAt (fun θ => Z θ ω) (D θ ω) θ := by
        rw [hasDerivAt_pi]
        intro t
        exact ((Real.hasDerivAt_cos θ).mul_const (X t ω)).add
          ((Real.hasDerivAt_sin θ).mul_const (Y t ω))
      have := (slF_hasFDerivAt φ φ' hφ (Z θ ω)).comp_hasDerivAt θ hZd
      refine this.congr_deriv ?_
      simp [hF']
    exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := P)
      (F := fun θ ω => slF φ (Z θ ω)) (F' := F') (x₀ := θ0) (bound := fun ω => C * B ω)
      (s := Set.univ) Filter.univ_mem (Filter.Eventually.of_forall hFm) hFint hF'm
      (ae_of_all _ fun ω θ _ => hbound θ ω) (hB.const_mul C)
      (ae_of_all _ fun ω θ _ => hdiff ω θ)).2
  -- covariance differences
  set Δ : ι → ι → ℝ := fun i j => ∫ ω, Y i ω * Y j ω ∂P - ∫ ω, X i ω * X j ω ∂P with hΔdef
  have hΔd : ∀ i, Δ i i = 0 := fun i => by simp only [hΔdef, hvar i, sub_self]
  have hΔo : ∀ i j, Δ i j ≤ 0 := by
    intro i j
    have h := hinc i j
    rw [sl_sq_sub X hXm i j, sl_sq_sub Y hYm i j] at h
    have ea : ∫ ω, X j ω * X i ω ∂P = ∫ ω, X i ω * X j ω ∂P := by
      congr 1; ext ω; ring
    have eb : ∫ ω, Y j ω * Y i ω ∂P = ∫ ω, Y i ω * Y j ω ∂P := by
      congr 1; ext ω; ring
    rw [ea, eb, hvar i, hvar j] at h
    simp only [hΔdef]
    linarith
  set K := C + C * C with hK
  have hHi : ∀ θ i j, Integrable (fun ω => slH φ φ' φ'' i j (Z θ ω)) P := fun θ i j =>
    Integrable.mono' (integrable_const K)
      ((hHc i j).measurable.comp_aemeasurable (hZae θ)).aestronglyMeasurable
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact slH_abs_le h0 h1 hC1 hC2 i j _)
  have hnonpos : ∀ θ, 0 ≤ Real.sin θ * Real.cos θ → ∫ ω, F' θ ω ∂P ≤ 0 := by
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
    have hKC : C ≤ K := by rw [hK]; nlinarith
    have hIBP : ∀ i, ∫ ω, D θ ω i * slG φ φ' i (Z θ ω) ∂P
        = ∑ j, (Real.sin θ * Real.cos θ * Δ i j) * ∫ ω, slH φ φ' φ'' i j (Z θ ω) ∂P := by
      intro i
      have h := sl_gaussian_ibp (fun ω => D θ ω i) (fun j ω => Z θ ω j) (hUV i)
        (hU0 i) (slG φ φ' i) (slH φ φ' φ'' i) (fun x => slG_hasFDerivAt φ φ' φ'' hφ hφ' i x)
        (fun j => hHc i j) K
        (fun x => (slG_abs_le h0 h1 hC1 i x).trans hKC)
        (fun j x => slH_abs_le h0 h1 hC1 hC2 i j x)
      refine h.trans (Finset.sum_congr rfl fun j _ => ?_)
      congr 1
      exact sl_cov_DZ X Y hXY hX0 hY0 hcross θ i j
    have hDp : ∀ i, Integrable (fun ω => D θ ω i * slG φ φ' i (Z θ ω)) P := by
      intro i
      refine Integrable.mono' (((hXi i).abs.add (hYi i).abs).const_mul C) (((hDae θ i).mul
        ((hGc i).measurable.comp_aemeasurable (hZae θ))).aestronglyMeasurable)
        (ae_of_all _ fun ω => ?_)
      rw [Real.norm_eq_abs, abs_mul, mul_comm]
      exact mul_le_mul (slG_abs_le h0 h1 hC1 i _) (hDb θ ω i) (abs_nonneg _) hC0
    have e1 : ∫ ω, F' θ ω ∂P = ∑ i, ∫ ω, D θ ω i * slG φ φ' i (Z θ ω) ∂P := by
      simp only [hF']
      rw [integral_finsetSum _ (fun i _ => by simpa only [mul_comm] using hDp i)]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1; ext ω; ring
    have e2 : ∑ i, ∑ j, (Real.sin θ * Real.cos θ * Δ i j) * ∫ ω, slH φ φ' φ'' i j (Z θ ω) ∂P
        = ∫ ω, ∑ i, ∑ j, (Real.sin θ * Real.cos θ * Δ i j) * slH φ φ' φ'' i j (Z θ ω) ∂P := by
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ =>
        (hHi θ i j).const_mul _)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum _ (fun j _ => (hHi θ i j).const_mul _)]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_const_mul]
    rw [e1]
    simp_rw [hIBP]
    rw [e2]
    refine integral_nonpos fun ω => ?_
    refine Finset.sum_nonpos fun i _ => Finset.sum_nonpos fun j _ => ?_
    by_cases hij : j = i
    · subst hij; rw [hΔd]; simp
    · rw [mul_assoc]
      exact mul_nonpos_of_nonneg_of_nonpos hsc
        (mul_nonpos_of_nonpos_of_nonneg (hΔo i j) (slH_nonneg_of_ne h0 hd hij _))
  have hcont : Continuous Φ := continuous_iff_continuousAt.2 fun θ => (hderiv θ).continuousAt
  have hanti : AntitoneOn Φ (Set.Icc 0 (Real.pi / 2)) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 (Real.pi / 2))
      hcont.continuousOn (fun θ _ => (hderiv θ).hasDerivWithinAt) (fun θ hθ => ?_)
    rw [interior_Icc] at hθ
    refine hnonpos θ (mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1.le (by linarith [hθ.2,
      Real.pi_pos])) (Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2.le⟩))
  have hpi : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have h := hanti ⟨le_refl 0, hpi⟩ ⟨hpi, le_refl _⟩ hpi
  have h0' : Φ 0 = ∫ ω, slF φ (fun t => X t ω) ∂P := by simp [hΦ, hZ]
  have h1' : Φ (Real.pi / 2) = ∫ ω, slF φ (fun t => Y t ω) ∂P := by simp [hΦ, hZ]
  rw [← h0', ← h1']; exact h

end Compare


section Cutoff

lemma sl_deriv_zero_of_const {f : ℝ → ℝ} {c x : ℝ} {U : Set ℝ} (hU : IsOpen U) (hx : x ∈ U)
    (hf : ∀ y ∈ U, f y = c) : deriv f x = 0 ∧ deriv (deriv f) x = 0 := by
  have h1 : ∀ y ∈ U, deriv f y = 0 := fun y hy => by
    have : f =ᶠ[nhds y] fun _ => c := Filter.eventually_of_mem (hU.mem_nhds hy) hf
    rw [this.deriv_eq]; exact deriv_const _ _
  refine ⟨h1 x hx, ?_⟩
  have : deriv f =ᶠ[nhds x] fun _ => (0 : ℝ) := Filter.eventually_of_mem (hU.mem_nhds hx) h1
  rw [this.deriv_eq]; exact deriv_const _ _

lemma sl_sT_deriv_zero {x : ℝ} (hx : x ∉ Set.Icc (0 : ℝ) 1) :
    deriv Real.smoothTransition x = 0 ∧ deriv (deriv Real.smoothTransition) x = 0 := by
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
  rcases hx with hx | hx
  · exact sl_deriv_zero_of_const isOpen_Iio hx
      (fun y hy => Real.smoothTransition.zero_of_nonpos (le_of_lt hy))
  · exact sl_deriv_zero_of_const isOpen_Ioi hx
      (fun y hy => Real.smoothTransition.one_of_one_le (le_of_lt hy))

lemma sl_sT_props :
    (∀ x, HasDerivAt Real.smoothTransition (deriv Real.smoothTransition x) x) ∧
    (∀ x, HasDerivAt (deriv Real.smoothTransition)
      (deriv (deriv Real.smoothTransition) x) x) ∧
    Continuous (deriv (deriv Real.smoothTransition)) ∧
    (∀ x, 0 ≤ deriv Real.smoothTransition x) ∧
    ∃ C, (∀ x, |deriv Real.smoothTransition x| ≤ C) ∧
      (∀ x, |deriv (deriv Real.smoothTransition) x| ≤ C) := by
  have hc : ContDiff ℝ (⊤ : ℕ∞) Real.smoothTransition := Real.smoothTransition.contDiff
  have hc1 : ContDiff ℝ (⊤ : ℕ∞) (deriv Real.smoothTransition) := by
    simpa using hc.iterate_deriv 1
  have hc2 : ContDiff ℝ (⊤ : ℕ∞) (deriv (deriv Real.smoothTransition)) := by
    have := hc.iterate_deriv 2
    simpa [Function.iterate_succ] using this
  have hd0 := hc.differentiable (by simp)
  have hd1 := hc1.differentiable (by simp)
  refine ⟨fun x => (hd0 x).hasDerivAt, fun x => (hd1 x).hasDerivAt, hc2.continuous,
    fun x => Real.smoothTransition.monotone.deriv_nonneg, ?_⟩
  have s1 : HasCompactSupport (deriv Real.smoothTransition) :=
    HasCompactSupport.intro isCompact_Icc fun x hx => (sl_sT_deriv_zero hx).1
  have s2 : HasCompactSupport (deriv (deriv Real.smoothTransition)) :=
    HasCompactSupport.intro isCompact_Icc fun x hx => (sl_sT_deriv_zero hx).2
  obtain ⟨C1, hC1⟩ := hc1.continuous.bounded_above_of_compact_support s1
  obtain ⟨C2, hC2⟩ := hc2.continuous.bounded_above_of_compact_support s2
  refine ⟨max C1 C2, fun x => ?_, fun x => ?_⟩
  · exact (hC1 x).trans (le_max_left _ _)
  · exact (hC2 x).trans (le_max_right _ _)

/-- the cutoff `φ_δ(u) = s((τ + δ - u)/δ)`: `1` on `(-∞, τ]`, `0` on `[τ + δ, ∞)` -/
noncomputable def slφ (τ δ u : ℝ) : ℝ := Real.smoothTransition ((τ + δ - u) / δ)
noncomputable def slφ1 (τ δ u : ℝ) : ℝ :=
  -(1 / δ) * deriv Real.smoothTransition ((τ + δ - u) / δ)
noncomputable def slφ2 (τ δ u : ℝ) : ℝ :=
  (1 / δ) ^ 2 * deriv (deriv Real.smoothTransition) ((τ + δ - u) / δ)

lemma sl_cutoff (τ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    (∀ u, HasDerivAt (slφ τ δ) (slφ1 τ δ u) u) ∧
    (∀ u, HasDerivAt (slφ1 τ δ) (slφ2 τ δ u) u) ∧
    Continuous (slφ2 τ δ) ∧
    (∀ u, 0 ≤ slφ τ δ u) ∧ (∀ u, slφ τ δ u ≤ 1) ∧ (∀ u, slφ1 τ δ u ≤ 0) ∧
    (∀ u, u ≤ τ → slφ τ δ u = 1) ∧ (∀ u, τ + δ ≤ u → slφ τ δ u = 0) ∧
    ∃ C, (∀ u, |slφ1 τ δ u| ≤ C) ∧ (∀ u, |slφ2 τ δ u| ≤ C) := by
  obtain ⟨d0, d1, c2, pos, C, hC1, hC2⟩ := sl_sT_props
  have ha : ∀ u, HasDerivAt (fun u => (τ + δ - u) / δ) (-1 / δ) u := fun u => by
    simpa using ((hasDerivAt_id u).const_sub (τ + δ)).div_const δ
  refine ⟨fun u => ?_, fun u => ?_, ?_, fun u => Real.smoothTransition.nonneg _,
    fun u => Real.smoothTransition.le_one _, fun u => ?_, fun u hu => ?_, fun u hu => ?_,
    ⟨(1 / δ + (1 / δ) ^ 2) * C, fun u => ?_, fun u => ?_⟩⟩
  · have := (d0 ((τ + δ - u) / δ)).comp u (ha u)
    refine this.congr_deriv ?_
    simp only [slφ1]; ring
  · have := ((d1 ((τ + δ - u) / δ)).comp u (ha u)).const_mul (-(1 / δ))
    refine this.congr_deriv ?_
    simp only [slφ2]; ring
  · unfold slφ2; fun_prop
  · simp only [slφ1]
    have := pos ((τ + δ - u) / δ)
    have : 0 < 1 / δ := by positivity
    nlinarith
  · simp only [slφ]
    apply Real.smoothTransition.one_of_one_le
    rw [le_div_iff₀ hδ]; linarith
  · simp only [slφ]
    apply Real.smoothTransition.zero_of_nonpos
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le
  · have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC1 0)
    simp only [slφ1, abs_mul, abs_neg, abs_of_pos (one_div_pos.2 hδ)]
    have := mul_le_mul_of_nonneg_left (hC1 ((τ + δ - u) / δ)) (one_div_pos.2 hδ).le
    nlinarith [sq_nonneg (1 / δ)]
  · have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC1 0)
    simp only [slφ2, abs_mul, abs_pow, abs_of_pos (one_div_pos.2 hδ)]
    have := mul_le_mul_of_nonneg_left (hC2 ((τ + δ - u) / δ)) (sq_nonneg (1 / δ))
    nlinarith [one_div_pos.2 hδ]

end Cutoff


section Main

theorem sl_main {ι Ω Ω' : Type*} [Fintype ι] [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {P : Measure Ω} {Q : Measure Ω'} (X : ι → Ω → ℝ) (Y : ι → Ω' → ℝ)
    (hX : HasGaussianLaw (fun ω t => X t ω) P) (hY : HasGaussianLaw (fun ω t => Y t ω) Q)
    (hX0 : ∀ t, ∫ ω, X t ω ∂P = 0) (hY0 : ∀ t, ∫ ω, Y t ω ∂Q = 0)
    (hvar : ∀ t, ∫ ω, X t ω ^ 2 ∂P = ∫ ω, Y t ω ^ 2 ∂Q)
    (hinc : ∀ s t, ∫ ω, (X s ω - X t ω) ^ 2 ∂P ≤ ∫ ω, (Y s ω - Y t ω) ^ 2 ∂Q) (τ : ℝ) :
    P {ω | τ < ⨆ t, X t ω} ≤ Q {ω | τ < ⨆ t, Y t ω} := by
  have hP := hX.isProbabilityMeasure
  have hQ := hY.isProbabilityMeasure
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp only [Real.iSup_of_isEmpty]
    by_cases h : τ < 0 <;> simp [h]
  classical
  set μX := P.map (fun ω t => X t ω) with hμX
  set μY := Q.map (fun ω t => Y t ω) with hμY
  have : IsGaussian μX := hX.isGaussian_map
  have : IsGaussian μY := hY.isGaussian_map
  have : IsProbabilityMeasure μX := Measure.isProbabilityMeasure_map hX.aemeasurable
  have : IsProbabilityMeasure μY := Measure.isProbabilityMeasure_map hY.aemeasurable
  have hsup : Measurable (fun x : ι → ℝ => ⨆ t, x t) :=
    Measurable.iSup fun t => measurable_pi_apply t
  set S : Set (ι → ℝ) := {x | τ < ⨆ t, x t} with hSdef
  have hS : MeasurableSet S := measurableSet_lt measurable_const hsup
  have eX : P {ω | τ < ⨆ t, X t ω} = μX S :=
    (Measure.map_apply_of_aemeasurable hX.aemeasurable hS).symm
  have eY : Q {ω | τ < ⨆ t, Y t ω} = μY S :=
    (Measure.map_apply_of_aemeasurable hY.aemeasurable hS).symm
  rw [eX, eY]
  set T : ℝ → Set (ι → ℝ) := fun a => {x | ⨆ t, x t ≤ a} with hTdef
  have hT : ∀ a, MeasurableSet (T a) := fun a => measurableSet_le hsup measurable_const
  have hmemT : ∀ a x, x ∈ T a ↔ ∀ t, x t ≤ a := fun a x =>
    ciSup_le_iff (Set.finite_range x).bddAbove
  -- one product space
  set μ := μX.prod μY with hμ
  have hlaw : HasGaussianLaw (fun p : (ι → ℝ) × (ι → ℝ) => (fun t => p.1 t, fun t => p.2 t)) μ :=
    IsGaussian.hasGaussianLaw_id
  have hfst : ∀ f : (ι → ℝ) → ℝ, Measurable f → ∫ p, f p.1 ∂μ = ∫ x, f x ∂μX := by
    intro f hf
    have h1 : ∫ p, f p.1 ∂μ = ∫ x, f x ∂(μ.map Prod.fst) :=
      (integral_map measurable_fst.aemeasurable hf.aestronglyMeasurable).symm
    rw [h1, hμ, Measure.map_fst_prod, measure_univ, one_smul]
  have hsnd : ∀ f : (ι → ℝ) → ℝ, Measurable f → ∫ p, f p.2 ∂μ = ∫ x, f x ∂μY := by
    intro f hf
    have h1 : ∫ p, f p.2 ∂μ = ∫ x, f x ∂(μ.map Prod.snd) :=
      (integral_map measurable_snd.aemeasurable hf.aestronglyMeasurable).symm
    rw [h1, hμ, Measure.map_snd_prod, measure_univ, one_smul]
  have hXf : ∀ f : (ι → ℝ) → ℝ, Measurable f →
      ∫ p, f p.1 ∂μ = ∫ ω, f (fun t => X t ω) ∂P := fun f hf => by
    rw [hfst f hf, hμX, integral_map hX.aemeasurable hf.aestronglyMeasurable]
  have hYf : ∀ f : (ι → ℝ) → ℝ, Measurable f →
      ∫ p, f p.2 ∂μ = ∫ ω, f (fun t => Y t ω) ∂Q := fun f hf => by
    rw [hsnd f hf, hμY, integral_map hY.aemeasurable hf.aestronglyMeasurable]
  have hX0' : ∀ t, ∫ p, p.1 t ∂μ = 0 := fun t => by
    rw [hXf (fun x => x t) (measurable_pi_apply t)]; exact hX0 t
  have hY0' : ∀ t, ∫ p, p.2 t ∂μ = 0 := fun t => by
    rw [hYf (fun x => x t) (measurable_pi_apply t)]; exact hY0 t
  have hcross : ∀ s t, ∫ p, p.1 s * p.2 t ∂μ = 0 := by
    intro s t
    rw [hμ, integral_prod_mul (fun x : ι → ℝ => x s) (fun y : ι → ℝ => y t)]
    have : ∫ x, x s ∂μX = 0 := by
      rw [hμX, integral_map hX.aemeasurable (measurable_pi_apply s).aestronglyMeasurable]
      exact hX0 s
    rw [this, zero_mul]
  have hvar' : ∀ t, ∫ p, p.1 t * p.1 t ∂μ = ∫ p, p.2 t * p.2 t ∂μ := by
    intro t
    rw [hXf (fun x => x t * x t) (by fun_prop), hYf (fun x => x t * x t) (by fun_prop)]
    simpa only [sq] using hvar t
  have hinc' : ∀ s t, ∫ p, (p.1 s - p.1 t) ^ 2 ∂μ ≤ ∫ p, (p.2 s - p.2 t) ^ 2 ∂μ := by
    intro s t
    rw [hXf (fun x => (x s - x t) ^ 2) (by fun_prop),
      hYf (fun x => (x s - x t) ^ 2) (by fun_prop)]
    exact hinc s t
  -- smoothed comparison
  have key : ∀ δ : ℝ, 0 < δ → μY.real (T τ) ≤ μX.real (T (τ + δ)) := by
    intro δ hδ
    obtain ⟨d0, d1, c2, p0, p1, pd, pτ, pτδ, C, hC1, hC2⟩ := sl_cutoff τ hδ
    have hc := sl_compare (P := μ) (fun t p => p.1 t) (fun t p => p.2 t) hlaw hX0' hY0'
      hcross hvar' hinc' (slφ τ δ) (slφ1 τ δ) (slφ2 τ δ) d0 d1 c2 p0 p1 pd C hC1 hC2
    have hFc : Continuous (slF (ι := ι) (slφ τ δ)) :=
      continuous_iff_continuousAt.2 fun x =>
        (slF_hasFDerivAt (slφ τ δ) (slφ1 τ δ) d0 x).continuousAt
    rw [hfst _ hFc.measurable, hsnd _ hFc.measurable] at hc
    have hFint : ∀ ν : Measure (ι → ℝ), IsFiniteMeasure ν → Integrable (slF (slφ τ δ)) ν :=
      fun ν _ => Integrable.mono' (integrable_const 1) hFc.aestronglyMeasurable
        (ae_of_all _ fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (slF_nonneg p0 p1 _)]; exact slF_le_one p0 p1 _)
    have hlow : μY.real (T τ) ≤ ∫ x, slF (slφ τ δ) x ∂μY := by
      rw [← integral_indicator_one (hT τ)]
      refine integral_mono ((integrable_const 1).indicator (hT τ)) (hFint μY inferInstance)
        fun x => ?_
      by_cases hx : x ∈ T τ
      · rw [Set.indicator_of_mem hx, Pi.one_apply]
        have : slF (slφ τ δ) x = 1 :=
          Finset.prod_eq_one fun t _ => pτ (x t) ((hmemT τ x).1 hx t)
        rw [this]
      · rw [Set.indicator_of_notMem hx]; exact slF_nonneg p0 p1 _
    have hup : ∫ x, slF (slφ τ δ) x ∂μX ≤ μX.real (T (τ + δ)) := by
      rw [← integral_indicator_one (hT (τ + δ))]
      refine integral_mono (hFint μX inferInstance)
        ((integrable_const 1).indicator (hT (τ + δ))) fun x => ?_
      by_cases hx : x ∈ T (τ + δ)
      · rw [Set.indicator_of_mem hx, Pi.one_apply]; exact slF_le_one p0 p1 _
      · rw [Set.indicator_of_notMem hx]
        have : ¬ ∀ t, x t ≤ τ + δ := fun h => hx ((hmemT _ x).2 h)
        push Not at this
        obtain ⟨t, ht⟩ := this
        have : slF (slφ τ δ) x = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ t) (pτδ (x t) ht.le)
        rw [this]
    linarith
  -- right-continuity of the distribution function of `max X`
  set ν := μX.map (fun x : ι → ℝ => ⨆ t, x t) with hν
  have : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hsup.aemeasurable
  have hνT : ∀ a, μX.real (T a) = cdf ν a := by
    intro a
    rw [cdf_eq_real, measureReal_def, measureReal_def, hν,
      Measure.map_apply hsup measurableSet_Iic]
    rfl
  have hlim : Filter.Tendsto (cdf ν) (nhdsWithin τ (Set.Ioi τ)) (nhds (cdf ν τ)) :=
    ((cdf ν).right_continuous τ).mono Set.Ioi_subset_Ici_self
  have hreal : μY.real (T τ) ≤ μX.real (T τ) := by
    rw [hνT]
    refine ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun a ha => ?_)
    have := key (a - τ) (sub_pos.2 ha)
    rw [hνT, add_sub_cancel] at this
    exact this
  have hle : μY (T τ) ≤ μX (T τ) := by
    rw [← ofReal_measureReal (μ := μY), ← ofReal_measureReal (μ := μX)]
    exact ENNReal.ofReal_le_ofReal hreal
  have hSc : S = (T τ)ᶜ := by
    ext x; simp [hSdef, hTdef, not_le]
  rw [hSc, prob_compl_eq_one_sub (hT τ), prob_compl_eq_one_sub (hT τ)]
  exact tsub_le_tsub_left hle 1

end Main

end GaussianMatrix

open GaussianMatrix

theorem solution {ι Ω Ω' : Type*} [Fintype ι] [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {P : Measure Ω} {Q : Measure Ω'} (X : ι → Ω → ℝ) (Y : ι → Ω' → ℝ)
    (hX : HasGaussianLaw (fun ω t => X t ω) P) (hY : HasGaussianLaw (fun ω t => Y t ω) Q)
    (hX0 : ∀ t, ∫ ω, X t ω ∂P = 0) (hY0 : ∀ t, ∫ ω, Y t ω ∂Q = 0)
    (hvar : ∀ t, ∫ ω, X t ω ^ 2 ∂P = ∫ ω, Y t ω ^ 2 ∂Q)
    (hinc : ∀ s t, ∫ ω, (X s ω - X t ω) ^ 2 ∂P ≤ ∫ ω, (Y s ω - Y t ω) ^ 2 ∂Q) (τ : ℝ) :
    P {ω | τ < ⨆ t, X t ω} ≤ Q {ω | τ < ⨆ t, Y t ω} :=
  sl_main X Y hX hY hX0 hY0 hvar hinc τ
