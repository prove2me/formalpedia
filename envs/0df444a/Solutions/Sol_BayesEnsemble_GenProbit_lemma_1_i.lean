-- Prove2me | solution 1 for BayesEnsemble.GenProbit.lemma_1_i
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-02T04:10:38.291907+00:00
-- url     : https://prove2.me/submissions/43298933-d152-40a1-9086-5d62a97200c9

import Mathlib
import Definitions.Def_BayesEnsemble_GenProbit_Model

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory RealInnerProductSpace
open Matrix

namespace GPAux
open BayesEnsemble.GenProbit

variable {k : ℕ}

lemma G_eq_integral (P : Params k) (hP : Standing P) (v u : ℝ) :
    G P v u = ∫ g, cdf P.nu (u + g) ∂(gaussianReal 0 v.toNNReal) := by
  have := hP.prob
  set γ := gaussianReal 0 v.toNNReal
  have hF : Measurable (cdf P.nu) := (monotone_cdf _).measurable
  have key : P.nu ∗ γ = γ ∗ P.nu := Measure.conv_comm _ _
  unfold G
  rw [key, cdf_eq_real]
  have hmeas : MeasurableSet {p : ℝ × ℝ | p.1 + p.2 ≤ u} :=
    measurableSet_le (by fun_prop) measurable_const
  have h1 : (γ ∗ P.nu) (Set.Iic u) = ∫⁻ g, ENNReal.ofReal (cdf P.nu (u - g)) ∂γ := by
    rw [Measure.conv, Measure.map_apply (by fun_prop) measurableSet_Iic,
      Measure.prod_apply (measurable_add measurableSet_Iic)]
    refine lintegral_congr fun g => ?_
    rw [ofReal_cdf]
    congr 1
    ext z; simp [Set.mem_preimage, Set.mem_Iic]; constructor <;> intro h <;> linarith
  have hint : Integrable (fun g => cdf P.nu (u - g)) γ := by
    refine Integrable.of_bound (C := 1) ?_ (Filter.Eventually.of_forall fun g => ?_)
    · exact (hF.comp (by fun_prop)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (cdf_nonneg _ _)]; exact cdf_le_one _ _
  have h2 : (γ ∗ P.nu).real (Set.Iic u) = ∫ g, cdf P.nu (u - g) ∂γ := by
    rw [measureReal_def, h1, ← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun g => cdf_nonneg _ _), ENNReal.toReal_ofReal
      (integral_nonneg fun g => cdf_nonneg _ _)]
  rw [h2]
  have hneg : γ.map (fun x => -x) = γ := by
    simp [γ, gaussianReal_map_neg]
  conv_rhs => rw [← hneg]
  rw [integral_map (f := fun g => cdf P.nu (u + g)) (by fun_prop)
    (hF.comp (by fun_prop)).aestronglyMeasurable]
  simp [sub_eq_add_neg]


lemma integral_cdf_gaussian (P : Params k) (hP : Standing P) (v m a : ℝ) :
    ∫ w, cdf P.nu (w + a) ∂(gaussianReal m v.toNNReal) = G P v (m + a) := by
  have hF : Measurable (cdf P.nu) := (monotone_cdf _).measurable
  rw [G_eq_integral P hP]
  have : gaussianReal m v.toNNReal = (gaussianReal 0 v.toNNReal).map (fun g => g + m) := by
    rw [gaussianReal_map_add_const]; simp
  rw [this, integral_map (f := fun w => cdf P.nu (w + a)) (by fun_prop)
    (hF.comp (by fun_prop)).aestronglyMeasurable]
  congr 1; ext g; congr 1; ring

lemma G_strictMono (P : Params k) (hP : Standing P) (v : ℝ) : StrictMono (G P v) := by
  have := hP.prob
  have hF : Measurable (cdf P.nu) := (monotone_cdf _).measurable
  intro w u hwu
  rw [G_eq_integral P hP, G_eq_integral P hP]
  have hint : ∀ c : ℝ, Integrable (fun g => cdf P.nu (c + g)) (gaussianReal 0 v.toNNReal) := by
    intro c
    refine Integrable.of_bound (C := 1) ?_ (Filter.Eventually.of_forall fun g => ?_)
    · exact (hF.comp (by fun_prop)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (cdf_nonneg _ _)]; exact cdf_le_one _ _
  rw [← sub_pos, ← integral_sub (hint u) (hint w)]
  have hpos : ∀ g, 0 < cdf P.nu (u + g) - cdf P.nu (w + g) := by
    intro g
    have h1 : P.nu (Set.Ioc (w + g) (u + g)) = ENNReal.ofReal (cdf P.nu (u + g) - cdf P.nu (w + g)) := by
      conv_lhs => rw [← measure_cdf (μ := P.nu)]
      rw [StieltjesFunction.measure_Ioc]
    have h2 : 0 < P.nu (Set.Ioc (w + g) (u + g)) :=
      lt_of_lt_of_le (hP.fullSupport _ _ (by linarith)) (measure_mono Set.Ioo_subset_Ioc_self)
    rw [h1] at h2
    exact ENNReal.ofReal_pos.mp h2
  have hi : Integrable (fun g => cdf P.nu (u + g) - cdf P.nu (w + g)) (gaussianReal 0 v.toNNReal) :=
    (hint u).sub (hint w)
  rw [integral_pos_iff_support_of_nonneg (fun g => (hpos g).le) hi]
  have : Function.support (fun g => cdf P.nu (u + g) - cdf P.nu (w + g)) = Set.univ := by
    ext g; simp [(hpos g).ne']
  rw [this]; simp

lemma Ginv_G (P : Params k) (hP : Standing P) (v u : ℝ) : Ginv P v (G P v u) = u := by
  unfold Ginv
  have : {w : ℝ | G P v u ≤ G P v w} = Set.Ici u := by
    ext w; simp [(G_strictMono P hP v).le_iff_le]
  rw [this, csInf_Ici]


section
variable (P : Params k) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (x : Ω → EuclideanSpace ℝ (Fin k)) (hx : Measurable x)
    (hlaw : μ.map x = multivariateGaussian P.mean P.S)

include hx hlaw

lemma hasGL : HasGaussianLaw x μ := ⟨by rw [hlaw]; infer_instance⟩

lemma mean_inner (a : EuclideanSpace ℝ (Fin k)) :
    ∫ ω, ⟪a, x ω⟫ ∂μ = ⟪a, P.mean⟫ := by
  have : ∫ ω, ⟪a, x ω⟫ ∂μ = ∫ y, ⟪a, y⟫ ∂(μ.map x) := by
    rw [integral_map hx.aemeasurable (by fun_prop)]
  rw [this, hlaw]
  have h2 := integral_inner (𝕜 := ℝ) (f := id) (μ := multivariateGaussian P.mean P.S)
    IsGaussian.integrable_id a
  simp only [id] at h2
  rw [h2, integral_id_multivariateGaussian]

lemma cov_inner (hS : P.S.PosSemidef) (a b : EuclideanSpace ℝ (Fin k)) :
    cov[fun ω => ⟪a, x ω⟫, fun ω => ⟪b, x ω⟫; μ] = a ⬝ᵥ P.S *ᵥ b := by
  have : cov[fun ω => ⟪a, x ω⟫, fun ω => ⟪b, x ω⟫; μ] =
      cov[fun y => ⟪a, y⟫, fun y => ⟪b, y⟫; μ.map x] := by
    rw [covariance_map (by fun_prop) (by fun_prop) hx.aemeasurable]; rfl
  rw [this, hlaw, ← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
    covarianceBilin_multivariateGaussian hS]

lemma map_inner (hS : P.S.PosSemidef) (a : EuclideanSpace ℝ (Fin k)) :
    μ.map (fun ω => ⟪a, x ω⟫) = gaussianReal ⟪a, P.mean⟫ (a ⬝ᵥ P.S *ᵥ a).toNNReal := by
  have h : HasGaussianLaw (fun ω => ⟪a, x ω⟫) μ := (hasGL P μ x hx hlaw).map_fun (innerSL ℝ a)
  rw [h.map_eq_gaussianReal, ← covariance_self (by fun_prop), cov_inner P μ x hx hlaw hS,
    mean_inner P μ x hx hlaw]

lemma indep_inner (hS : P.S.PosSemidef) (a b : EuclideanSpace ℝ (Fin k))
    (h0 : a ⬝ᵥ P.S *ᵥ b = 0) :
    IndepFun (fun ω => ⟪a, x ω⟫) (fun ω => ⟪b, x ω⟫) μ := by
  have h : HasGaussianLaw (fun ω => (⟪a, x ω⟫, ⟪b, x ω⟫)) μ :=
    (hasGL P μ x hx hlaw).map_fun ((innerSL ℝ a).prod (innerSL ℝ b))
  exact h.indepFun_of_covariance_eq_zero (by rw [cov_inner P μ x hx hlaw hS, h0])

end

lemma condExp_indep_freeze {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T W : Ω → ℝ) (hT : Measurable T) (hW : Measurable W) (hind : IndepFun T W μ)
    (f : ℝ × ℝ → ℝ) (hf : StronglyMeasurable f) (hfi : Integrable (fun ω => f (T ω, W ω)) μ) :
    μ[fun ω => f (T ω, W ω) | MeasurableSpace.comap T inferInstance] =ᵐ[μ]
      fun ω => ∫ w, f (T ω, w) ∂(μ.map W) := by
  have h1 := condExp_prod_ae_eq_integral_condDistrib hT hW.aemeasurable hf hfi
  have h2 : condDistrib W T μ =ᵐ[μ.map T] Kernel.const ℝ (μ.map W) := by
    apply condDistrib_ae_eq_of_measure_eq_compProd T hW.aemeasurable
    rw [Measure.compProd_const]
    exact (indepFun_iff_map_prod_eq_prod_map_map hT.aemeasurable hW.aemeasurable).mp hind
  have h3 := ae_of_ae_map hT.aemeasurable h2
  filter_upwards [h1, h3] with ω hω1 hω3
  rw [hω1, hω3, Kernel.const_apply]


lemma alpha_quad (P : Params k) :
    (WithLp.toLp 2 P.alpha : EuclideanSpace ℝ (Fin k)) ⬝ᵥ P.S *ᵥ (WithLp.toLp 2 P.alpha) = v0 P := by
  simp only [v0, dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma alpha_inner (P : Params k) (y : EuclideanSpace ℝ (Fin k)) :
    ⟪(WithLp.toLp 2 P.alpha : EuclideanSpace ℝ (Fin k)), y⟫ = ∑ i, P.alpha i * y i := by
  simp [PiLp.inner_apply, mul_comm]

lemma prior_main (P : Params k) (hP : Standing P)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (x : Ω → EuclideanSpace ℝ (Fin k)) (hx : Measurable x)
    (hlaw : μ.map x = multivariateGaussian P.mean P.S)
    (Y : Set Ω) (hY : MeasurableSet Y)
    (hglm : μ[Y.indicator (1 : Ω → ℝ) | MeasurableSpace.comap x inferInstance]
      =ᵐ[μ] fun ω => cdf P.nu (P.alpha0 + ∑ i, P.alpha i * x ω i)) :
    μ.real Y = G P (v0 P) (m0 P) := by
  have hF : Measurable (cdf P.nu) := (monotone_cdf _).measurable
  set a : EuclideanSpace ℝ (Fin k) := WithLp.toLp 2 P.alpha
  have h1 : μ.real Y = ∫ ω, Y.indicator (1 : Ω → ℝ) ω ∂μ := by
    rw [integral_indicator hY]; simp
  rw [h1, ← integral_condExp hx.comap_le, integral_congr_ae hglm]
  have h2 : (fun ω => cdf P.nu (P.alpha0 + ∑ i, P.alpha i * x ω i)) =
      fun ω => (fun w => cdf P.nu (w + P.alpha0)) (⟪a, x ω⟫) := by
    ext ω; simp only [a, alpha_inner]; rw [add_comm]
  rw [h2, ← integral_map (f := fun w => cdf P.nu (w + P.alpha0)) (φ := fun ω => ⟪a, x ω⟫) (μ := μ) (by fun_prop) (hF.comp (by fun_prop)).aestronglyMeasurable,
    map_inner P μ x hx hlaw hP.posSemidef a, alpha_quad, integral_cdf_gaussian P hP]
  congr 1
  simp only [m0, alpha_inner, a]; ring


lemma S_symm (P : Params k) (hS : P.S.PosSemidef) (i j : Fin k) : P.S j i = P.S i j := by
  have := hS.1.apply i j
  simpa using this

lemma v0_split (P : Params k) (hS : P.S.PosSemidef) (i : Fin k) :
    v0 P = bMM P i + 2 * P.alpha i * (∑ j ∈ Finset.univ.erase i, P.alpha j * P.S i j)
      + P.alpha i ^ 2 * P.S i i := by
  unfold v0 bMM
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have h1 : ∀ j ∈ Finset.univ.erase i, (∑ j', P.alpha j * P.alpha j' * P.S j j') =
      P.alpha j * P.alpha i * P.S j i + ∑ j' ∈ Finset.univ.erase i, P.alpha j * P.alpha j' * P.S j j' := by
    intro j _
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib]
  have h2 : ∑ j ∈ Finset.univ.erase i, P.alpha j * P.alpha i * P.S j i =
      P.alpha i * ∑ j ∈ Finset.univ.erase i, P.alpha j * P.S i j := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
    rw [S_symm P hS]; ring
  have h3 : ∑ j' ∈ Finset.univ.erase i, P.alpha i * P.alpha j' * P.S i j' =
      P.alpha i * ∑ j ∈ Finset.univ.erase i, P.alpha j * P.S i j := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [h2, h3]; ring

lemma D_split (P : Params k) (i : Fin k) :
    (∑ j, P.alpha j * P.S i j) = (∑ j ∈ Finset.univ.erase i, P.alpha j * P.S i j)
      + P.alpha i * P.S i i := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]; ring

lemma vi_eq (P : Params k) (hS : P.S.PosSemidef) (i : Fin k) (hs : 0 < P.S i i) :
    vi P i = v0 P - (∑ j, P.alpha j * P.S i j) ^ 2 / P.S i i := by
  rw [v0_split P hS i, D_split P i, vi]
  field_simp
  ring

lemma beta_inv_mul (P : Params k) (hP : Standing P) (i : Fin k) :
    (BayesEnsemble.GenProbit.beta P i)⁻¹ * P.alpha i = (∑ j, P.alpha j * P.S i j) / P.S i i := by
  have hs := hP.diag_pos i
  have hsq : Real.sqrt (P.S i i) ≠ 0 := (Real.sqrt_pos.mpr hs).ne'
  have hden : ∑ j, P.alpha j * Real.sqrt (P.S j j) * rho P i j =
      (∑ j, P.alpha j * P.S i j) / Real.sqrt (P.S i i) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hj : Real.sqrt (P.S j j) ≠ 0 := (Real.sqrt_pos.mpr (hP.diag_pos j)).ne'
    unfold rho
    field_simp
  have hα := hP.alpha_ne i
  have hD := hP.denom_ne i
  unfold BayesEnsemble.GenProbit.beta
  rw [hden]
  have hss : Real.sqrt (P.S i i) * Real.sqrt (P.S i i) = P.S i i := Real.mul_self_sqrt hs.le
  field_simp
  rw [Real.sq_sqrt hs.le]


lemma inner_single_coord (i : Fin k) (y : EuclideanSpace ℝ (Fin k)) :
    ⟪EuclideanSpace.single i (1:ℝ), y⟫ = y i := by
  simp [EuclideanSpace.inner_single_left]

lemma mulVec_alpha_i (P : Params k) (i : Fin k) :
    (P.S *ᵥ P.alpha) i = ∑ j, P.alpha j * P.S i j := by
  simp [mulVec, dotProduct, mul_comm]

lemma alpha_col_i (P : Params k) (hS : P.S.PosSemidef) (i : Fin k) :
    P.alpha ⬝ᵥ P.S.col i = ∑ j, P.alpha j * P.S i j := by
  simp only [dotProduct, col_apply]
  exact Finset.sum_congr rfl fun j _ => by rw [S_symm P hS]

lemma cross_zero (P : Params k) (hS : P.S.PosSemidef) (i : Fin k) (hs : 0 < P.S i i) :
    let e : EuclideanSpace ℝ (Fin k) := EuclideanSpace.single i 1
    let c : ℝ := (∑ j, P.alpha j * P.S i j) / P.S i i
    let a : EuclideanSpace ℝ (Fin k) := WithLp.toLp 2 P.alpha - c • e
    e ⬝ᵥ P.S *ᵥ a = 0 := by
  intro e c a
  simp [e, a, c, mulVec_sub, mulVec_smul, dotProduct_sub]
  rw [mulVec_alpha_i P i]
  field_simp
  ring

lemma quad_a (P : Params k) (hS : P.S.PosSemidef) (i : Fin k) (hs : 0 < P.S i i) :
    let e : EuclideanSpace ℝ (Fin k) := EuclideanSpace.single i 1
    let c : ℝ := (∑ j, P.alpha j * P.S i j) / P.S i i
    let a : EuclideanSpace ℝ (Fin k) := WithLp.toLp 2 P.alpha - c • e
    a ⬝ᵥ P.S *ᵥ a = vi P i := by
  intro e c a
  rw [vi_eq P hS i hs, ← alpha_quad]
  simp [e, a, c, mulVec_sub, mulVec_smul, dotProduct_sub, sub_dotProduct]
  rw [mulVec_alpha_i P i, alpha_col_i P hS i]
  field_simp
  ring

lemma report_main (P : Params k) (hP : Standing P)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (x : Ω → EuclideanSpace ℝ (Fin k)) (hx : Measurable x)
    (hlaw : μ.map x = multivariateGaussian P.mean P.S)
    (Y : Set Ω) (hY : MeasurableSet Y)
    (hglm : μ[Y.indicator (1 : Ω → ℝ) | MeasurableSpace.comap x inferInstance]
      =ᵐ[μ] fun ω => cdf P.nu (P.alpha0 + ∑ i, P.alpha i * x ω i))
    (i : Fin k) :
    report μ x Y i =ᵐ[μ] fun ω =>
      G P (vi P i) (m0 P + (BayesEnsemble.GenProbit.beta P i)⁻¹ * P.alpha i * (x ω i - P.mean i)) := by
  have hS := hP.posSemidef
  have hs := hP.diag_pos i
  have hF : Measurable (cdf P.nu) := (monotone_cdf _).measurable
  set e : EuclideanSpace ℝ (Fin k) := EuclideanSpace.single i 1 with he
  set c : ℝ := (∑ j, P.alpha j * P.S i j) / P.S i i with hc
  set a : EuclideanSpace ℝ (Fin k) := WithLp.toLp 2 P.alpha - c • e with ha
  set T : Ω → ℝ := fun ω => x ω i with hT
  set W : Ω → ℝ := fun ω => ⟪a, x ω⟫ with hW
  have hTm : Measurable T := by fun_prop
  have hWm : Measurable W := by fun_prop
  have hTe : T = fun ω => ⟪e, x ω⟫ := by
    ext ω; simp only [T, e, inner_single_coord]
  have hind : IndepFun T W μ := by
    rw [hTe]; exact indep_inner P μ x hx hlaw hS e a (cross_zero P hS i hs)
  -- decomposition of the linear predictor
  have hdec : ∀ ω, P.alpha0 + ∑ j, P.alpha j * x ω j = W ω + (P.alpha0 + c * T ω) := by
    intro ω
    simp only [W, T, a, inner_sub_left, inner_smul_left, alpha_inner, e, inner_single_coord]
    simp; ring
  -- tower property
  have hle : MeasurableSpace.comap T inferInstance ≤ MeasurableSpace.comap x inferInstance := by
    rw [hT]
    have : (fun ω => x ω i) = (fun y : EuclideanSpace ℝ (Fin k) => y i) ∘ x := rfl
    rw [this, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (by fun_prop : Measurable fun y : EuclideanSpace ℝ (Fin k) => y i).comap_le
  have h1 : report μ x Y i =ᵐ[μ]
      μ[μ[Y.indicator (1 : Ω → ℝ) | MeasurableSpace.comap x inferInstance] |
        MeasurableSpace.comap T inferInstance] :=
    (condExp_condExp_of_le hle hx.comap_le).symm
  have h2 := condExp_congr_ae (m := MeasurableSpace.comap T inferInstance) hglm
  set f : ℝ × ℝ → ℝ := fun p => cdf P.nu (p.2 + (P.alpha0 + c * p.1)) with hf
  have hfm : StronglyMeasurable f := (hF.comp (by fun_prop)).stronglyMeasurable
  have hfi : Integrable (fun ω => f (T ω, W ω)) μ := by
    refine Integrable.of_bound (C := 1) ?_ (Filter.Eventually.of_forall fun ω => ?_)
    · exact (hfm.measurable.comp (hTm.prodMk hWm)).aestronglyMeasurable
    · simp only [f]
      rw [Real.norm_eq_abs, abs_of_nonneg (cdf_nonneg _ _)]; exact cdf_le_one _ _
  have h3 : (fun ω => cdf P.nu (P.alpha0 + ∑ j, P.alpha j * x ω j)) = fun ω => f (T ω, W ω) := by
    ext ω; simp only [f]; rw [hdec ω]
  rw [h3] at h2
  have h4 := condExp_indep_freeze μ T W hTm hWm hind f hfm hfi
  have hlawW : μ.map W = gaussianReal ⟪a, P.mean⟫ (vi P i).toNNReal := by
    rw [hW, map_inner P μ x hx hlaw hS a, quad_a P hS i hs]
  filter_upwards [h1, h2, h4] with ω hω1 hω2 hω4
  rw [hω1, hω2, hω4, hlawW]
  simp only [f]
  rw [integral_cdf_gaussian P hP, beta_inv_mul P hP i]
  congr 1
  simp only [a, T, inner_sub_left, inner_smul_left, alpha_inner, e, inner_single_coord, m0]
  simp; ring

lemma Ginv_out (P : Params k) (hP : Standing P) (v p : ℝ) (hp : p ∉ Set.Ioo (0:ℝ) 1) :
    Ginv P v p = 0 := by
  unfold Ginv
  rcases le_or_gt p 0 with h | h
  · have : {u : ℝ | p ≤ G P v u} = Set.univ := by
      ext u; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact h.trans (cdf_nonneg _ _)
    rw [this, Real.sInf_univ]
  · have h1 : 1 ≤ p := by
      by_contra h1; exact hp ⟨h, lt_of_not_ge h1⟩
    have : {u : ℝ | p ≤ G P v u} = ∅ := by
      ext u; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
      calc G P v u < G P v (u + 1) := G_strictMono P hP v (by linarith)
        _ ≤ 1 := cdf_le_one _ _
        _ ≤ p := h1
    rw [this, Real.sInf_empty]

lemma Ginv_monotoneOn (P : Params k) (v : ℝ) :
    MonotoneOn (Ginv P v) (Set.Ioo (0:ℝ) 1) := by
  intro p hp q hq hpq
  unfold Ginv
  apply csInf_le_csInf
  · -- bounded below
    have ht := (tendsto_cdf_atBot (P.nu ∗ gaussianReal 0 v.toNNReal))
    have : ∀ᶠ u in Filter.atBot, cdf (P.nu ∗ gaussianReal 0 v.toNNReal) u < p :=
      ht.eventually (gt_mem_nhds hp.1)
    obtain ⟨u0, hu0⟩ := Filter.eventually_atBot.mp this
    refine ⟨u0, fun u hu => ?_⟩
    by_contra hlt
    push_neg at hlt
    have := hu0 u hlt.le
    exact absurd hu (not_le.mpr this)
  · have ht := (tendsto_cdf_atTop (P.nu ∗ gaussianReal 0 v.toNNReal))
    have : ∀ᶠ u in Filter.atTop, q < cdf (P.nu ∗ gaussianReal 0 v.toNNReal) u :=
      ht.eventually (lt_mem_nhds hq.2)
    obtain ⟨u0, hu0⟩ := Filter.eventually_atTop.mp this
    exact ⟨u0, (hu0 u0 le_rfl).le⟩
  · intro u hu
    exact hpq.trans hu

lemma Ginv_measurable (P : Params k) (hP : Standing P) (v : ℝ) : Measurable (Ginv P v) := by
  apply measurable_of_restrict_of_restrict_compl (s := Set.Ioo (0:ℝ) 1) measurableSet_Ioo
  · have : Monotone ((Set.Ioo (0:ℝ) 1).domRestrict (Ginv P v)) :=
      fun a b hab => Ginv_monotoneOn P v a.2 b.2 hab
    exact this.measurable
  · have : (Set.Ioo (0:ℝ) 1)ᶜ.domRestrict (Ginv P v) = fun _ => 0 := by
      ext p; exact Ginv_out P hP v p p.2
    rw [this]; exact measurable_const

lemma beta_ne (P : Params k) (hP : Standing P) (i : Fin k) :
    BayesEnsemble.GenProbit.beta P i ≠ 0 := by
  intro h
  have := beta_inv_mul P hP i
  rw [h, _root_.inv_zero, zero_mul] at this
  exact div_ne_zero (hP.denom_ne i) (hP.diag_pos i).ne' this.symm

lemma ensemble_measurable (P : Params k) (hP : Standing P) (prior : ℝ) :
    Measurable (fun p : Fin k → ℝ => ensemble P prior p) := by
  have hF : Measurable (cdf P.nu) := (monotone_cdf _).measurable
  unfold ensemble
  refine hF.comp (measurable_const.add (Finset.measurable_sum _ fun i _ => ?_))
  exact measurable_const.mul ((Ginv_measurable P hP (vi P i)).comp (measurable_pi_apply i))

lemma ensemble_eval (P : Params k) (hP : Standing P) (y : EuclideanSpace ℝ (Fin k)) :
    ensemble P (G P (v0 P) (m0 P))
      (fun i => G P (vi P i) (m0 P + (BayesEnsemble.GenProbit.beta P i)⁻¹ * P.alpha i *
        (y i - P.mean i))) = cdf P.nu (P.alpha0 + ∑ i, P.alpha i * y i) := by
  unfold ensemble
  simp only [Ginv_G P hP]
  congr 1
  have h : ∀ i, BayesEnsemble.GenProbit.beta P i * (m0 P + (BayesEnsemble.GenProbit.beta P i)⁻¹
      * P.alpha i * (y i - P.mean i)) =
      BayesEnsemble.GenProbit.beta P i * m0 P + (P.alpha i * y i - P.alpha i * P.mean i) := by
    intro i
    have := beta_ne P hP i
    field_simp
  rw [Finset.sum_congr rfl (fun i _ => h i)]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, beta0, m0, ← Finset.sum_mul]
  ring

lemma agg_main (P : Params k) (hP : Standing P)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (x : Ω → EuclideanSpace ℝ (Fin k)) (hx : Measurable x)
    (hlaw : μ.map x = multivariateGaussian P.mean P.S)
    (Y : Set Ω) (hY : MeasurableSet Y)
    (hglm : μ[Y.indicator (1 : Ω → ℝ) | MeasurableSpace.comap x inferInstance]
      =ᵐ[μ] fun ω => cdf P.nu (P.alpha0 + ∑ i, P.alpha i * x ω i)) :
    aggregate μ x Y =ᵐ[μ] fun ω =>
      ensemble P (μ.real Y) (fun i => report μ x Y i ω) := by
  have hF : Measurable (cdf P.nu) := (monotone_cdf _).measurable
  set R : Ω → (Fin k → ℝ) := fun ω i => report μ x Y i ω with hRdef
  have hRm : Measurable[MeasurableSpace.comap x inferInstance] R := by
    refine @measurable_pi_lambda Ω (Fin k) (fun _ => ℝ) (MeasurableSpace.comap x inferInstance) _ R
      (fun i => ?_)
    have h1 : Measurable[MeasurableSpace.comap (fun ω => x ω i) inferInstance] (report μ x Y i) :=
      stronglyMeasurable_condExp.measurable
    have hle : MeasurableSpace.comap (fun ω => x ω i) inferInstance ≤
        MeasurableSpace.comap x inferInstance := by
      have : (fun ω => x ω i) = (fun y : EuclideanSpace ℝ (Fin k) => y i) ∘ x := rfl
      rw [this, ← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono
        (by fun_prop : Measurable fun y : EuclideanSpace ℝ (Fin k) => y i).comap_le
    exact h1.mono hle le_rfl
  have hRle : MeasurableSpace.comap R inferInstance ≤ MeasurableSpace.comap x inferInstance :=
    hRm.comap_le
  have hRle0 : MeasurableSpace.comap R inferInstance ≤ ‹MeasurableSpace Ω› :=
    hRle.trans hx.comap_le
  have h1 : aggregate μ x Y =ᵐ[μ]
      μ[μ[Y.indicator (1 : Ω → ℝ) | MeasurableSpace.comap x inferInstance] |
        MeasurableSpace.comap R inferInstance] :=
    (condExp_condExp_of_le hRle hx.comap_le).symm
  have h2 := condExp_congr_ae (m := MeasurableSpace.comap R inferInstance) hglm
  have hprior := prior_main P hP μ x hx hlaw Y hY hglm
  have hrep : ∀ᵐ ω ∂μ, ∀ i, report μ x Y i ω =
      G P (vi P i) (m0 P + (BayesEnsemble.GenProbit.beta P i)⁻¹ * P.alpha i * (x ω i - P.mean i)) :=
    ae_all_iff.mpr fun i => report_main P hP μ x hx hlaw Y hY hglm i
  have hFL : (fun ω => cdf P.nu (P.alpha0 + ∑ i, P.alpha i * x ω i)) =ᵐ[μ]
      fun ω => ensemble P (μ.real Y) (R ω) := by
    filter_upwards [hrep] with ω hω
    simp only [R]
    rw [hprior]
    simp only [hω]
    rw [ensemble_eval P hP]
  have h3 := condExp_congr_ae (m := MeasurableSpace.comap R inferInstance) hFL
  have hφ := ensemble_measurable P hP (μ.real Y)
  have hsm : StronglyMeasurable[MeasurableSpace.comap R inferInstance]
      (fun ω => ensemble P (μ.real Y) (R ω)) :=
    (hφ.comp (Measurable.of_comap_le le_rfl)).stronglyMeasurable
  have hint : Integrable (fun ω => ensemble P (μ.real Y) (R ω)) μ := by
    refine Integrable.of_bound (C := 1) ?_ (Filter.Eventually.of_forall fun ω => ?_)
    · exact (hsm.measurable.mono hRle0 le_rfl).aestronglyMeasurable
    · unfold ensemble
      rw [Real.norm_eq_abs, abs_of_nonneg (cdf_nonneg _ _)]; exact cdf_le_one _ _
  have h4 := condExp_of_stronglyMeasurable hRle0 hsm hint
  filter_upwards [h1, h2, h3] with ω hω1 hω2 hω3
  rw [hω1, hω2, hω3, h4]

end GPAux

open BayesEnsemble.GenProbit

theorem solution {k : ℕ} (P : Params k) (hS : P.S.PosSemidef) :
    (multivariateGaussian P.mean P.S).map
      (fun y => P.alpha0 + ∑ i, P.alpha i * y i) =
      gaussianReal (m0 P) (v0 P).toNNReal := by
  have h := GPAux.map_inner P (multivariateGaussian P.mean P.S) id measurable_id
    (Measure.map_id) hS (WithLp.toLp 2 P.alpha)
  rw [GPAux.alpha_quad] at h
  simp only [id] at h
  have h2 : (fun y : EuclideanSpace ℝ (Fin k) => P.alpha0 + ∑ i, P.alpha i * y i) =
      (fun t => P.alpha0 + t) ∘ (fun y => ⟪(WithLp.toLp 2 P.alpha : EuclideanSpace ℝ (Fin k)), y⟫) := by
    ext y; simp [GPAux.alpha_inner]
  rw [h2, ← Measure.map_map (by fun_prop) (by fun_prop), h, gaussianReal_map_const_add]
  congr 1
  simp [m0, GPAux.alpha_inner, add_comm]
