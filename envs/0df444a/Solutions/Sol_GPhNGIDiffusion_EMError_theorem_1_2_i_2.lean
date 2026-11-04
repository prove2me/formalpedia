-- Prove2me | solution 2 for GPhNGIDiffusion.EMError.theorem_1_2_i
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T17:56:53.446655+00:00
-- url     : https://prove2.me/submissions/e5649bd5-4332-4ae0-a626-f0fde5e27e02
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_GPhNGIDiffusion_EMError_proposition_2_1_unique_moments
import Theorems.Thm_GPhNGIDiffusion_EMError_lemma_2_2
import Theorems.Thm_GPhNGIDiffusion_EMError_claims_2_7_2_8

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace EMErrAux
open GPhNGIDiffusion.EMError

variable {d : ℕ}

lemma sum_single (u : EthierKurtz.SDEState d) : ∑ i, u i • EuclideanSpace.single i (1:ℝ) = u := by
  have := (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr u
  simpa using this

lemma expand1 (L : EthierKurtz.SDEState d →L[ℝ] ℝ) (v : EthierKurtz.SDEState d) :
    L v = ∑ i, v i * L (EuclideanSpace.single i 1) := by
  conv_lhs => rw [← sum_single v]
  simp [map_sum, map_smul]

lemma expand2 (B : EthierKurtz.SDEState d →L[ℝ] EthierKurtz.SDEState d →L[ℝ] ℝ)
    (u v : EthierKurtz.SDEState d) :
    B u v = ∑ i, ∑ j, u i * v j * B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  rw [expand1 (B u) v]
  conv_lhs => rw [← sum_single u]
  simp only [map_sum, map_smul, FunLike.coe_sum, Finset.sum_apply,
    FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  ring

lemma mv_apply (σ : Matrix (Fin d) (Fin d) ℝ) (z : EthierKurtz.SDEState d) (i : Fin d) :
    mv σ z i = inner ℝ (WithLp.toLp 2 (fun k => σ i k) : EthierKurtz.SDEState d) z := by
  simp [mv, Matrix.mulVec, dotProduct, PiLp.inner_apply, mul_comm]


noncomputable def Jf (f : EthierKurtz.SDEState d → ℝ) (w u : EthierKurtz.SDEState d) : ℝ :=
  ∫ r in (0 : ℝ)..1, ∫ r' in (0 : ℝ)..1,
    r * ∑ i, ∑ j, u i * u j * (partial2 f i j (w + (r' * r) • u) - partial2 f i j w)

lemma partial2_eq (f : EthierKurtz.SDEState d → ℝ) (i j : Fin d) (y : EthierKurtz.SDEState d) :
    partial2 f i j y = fderiv ℝ (fderiv ℝ f) y (EuclideanSpace.single i 1)
      (EuclideanSpace.single j 1) := by
  simp [partial2, iteratedFDeriv_two_apply]

lemma taylor (f : EthierKurtz.SDEState d → ℝ) (hf : ContDiff ℝ 2 f) (w u : EthierKurtz.SDEState d) :
    f (w + u) = f w + ∑ i, u i * partial1 f i w
      + (1 / 2) * ∑ i, ∑ j, u i * u j * partial2 f i j w + Jf f w u := by
  set F1 := fderiv ℝ f with hF1
  set F2 := fderiv ℝ F1 with hF2
  have hd1 : Differentiable ℝ f := hf.differentiable two_ne_zero
  have hc1 : ContDiff ℝ 1 F1 := hf.fderiv_right (by norm_num)
  have hd2 : Differentiable ℝ F1 := hc1.differentiable one_ne_zero
  have hcF2 : Continuous F2 := hc1.continuous_fderiv one_ne_zero
  let ℓ : ℝ → EthierKurtz.SDEState d := fun t => w + t • u
  have hℓ : ∀ t, HasDerivAt ℓ u t := fun t => by
    have := ((hasDerivAt_id' t).smul_const u).const_add w
    rwa [one_smul] at this
  let φ0 : ℝ → ℝ := fun t => f (ℓ t)
  let φ1 : ℝ → ℝ := fun t => F1 (ℓ t) u
  let ψ : ℝ → ℝ := fun t => F2 (ℓ t) u u
  have hφ0 : ∀ t, HasDerivAt φ0 (φ1 t) t := fun t =>
    (hd1 (ℓ t)).hasFDerivAt.comp_hasDerivAt t (hℓ t)
  have hφ1 : ∀ t, HasDerivAt φ1 (ψ t) t := fun t => by
    have h1 : HasDerivAt (fun s => F1 (ℓ s)) (F2 (ℓ t) u) t :=
      (hd2 (ℓ t)).hasFDerivAt.comp_hasDerivAt t (hℓ t)
    simpa using h1.clm_apply (hasDerivAt_const t u)
  have hcℓ : Continuous ℓ := by fun_prop
  have hψc : Continuous ψ := by
    have : Continuous fun t => F2 (ℓ t) := hcF2.comp hcℓ
    exact (this.clm_apply continuous_const).clm_apply continuous_const
  have hφ1c : Continuous φ1 :=
    continuous_iff_continuousAt.2 fun t => (hφ1 t).continuousAt
  have hinner : ∀ r : ℝ, (∫ r' in (0 : ℝ)..1,
      r * ∑ i, ∑ j, u i * u j * (partial2 f i j (w + (r' * r) • u) - partial2 f i j w))
        = φ1 r - φ1 0 - r * ψ 0 := by
    intro r
    have hsum : ∀ r' : ℝ, ∑ i, ∑ j, u i * u j * (partial2 f i j (w + (r' * r) • u)
        - partial2 f i j w) = ψ (r' * r) - ψ 0 := by
      intro r'
      simp only [ψ, ℓ, zero_smul, add_zero, expand2 (F2 _) u u, partial2_eq, ← hF1, ← hF2,
        ← Finset.sum_sub_distrib, mul_sub]
    simp_rw [hsum]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
      (f := fun x => ψ (x * r)) (g := fun _ => ψ 0)
      (by apply Continuous.intervalIntegrable; fun_prop) intervalIntegrable_const,
      intervalIntegral.integral_const]
    rcases eq_or_ne r 0 with rfl | hr
    · simp
    · rw [intervalIntegral.integral_comp_mul_right ψ hr,
        intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hφ1 t)
          (hψc.intervalIntegrable _ _)]
      simp only [zero_mul, one_mul, sub_zero, smul_eq_mul]
      field_simp
  have houter : Jf f w u = (φ0 1 - φ0 0) - φ1 0 - ψ 0 / 2 := by
    unfold Jf
    simp_rw [hinner]
    rw [intervalIntegral.integral_sub, intervalIntegral.integral_sub,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hφ0 t)
        (hφ1c.intervalIntegrable _ _),
      intervalIntegral.integral_const, intervalIntegral.integral_mul_const, integral_id]
    · simp; ring
    · exact hφ1c.intervalIntegrable _ _
    · exact intervalIntegrable_const
    · exact (hφ1c.sub continuous_const).intervalIntegrable _ _
    · exact (continuous_id.mul continuous_const).intervalIntegrable _ _
  have e0 : φ0 1 = f (w + u) := by simp [φ0, ℓ]
  have e1 : φ0 0 = f w := by simp [φ0, ℓ]
  have e2 : φ1 0 = ∑ i, u i * partial1 f i w := by
    simp only [φ1, ℓ, zero_smul, add_zero, partial1, ← hF1]
    exact expand1 _ u
  have e3 : ψ 0 = ∑ i, ∑ j, u i * u j * partial2 f i j w := by
    simp only [ψ, ℓ, zero_smul, add_zero, partial2_eq, ← hF1, ← hF2]
    exact expand2 _ u u
  rw [houter, ← e0, ← e1, e2, e3]
  ring



lemma g_int1 (v : EthierKurtz.SDEState d) :
    Integrable (fun z => inner ℝ v z) (stdGaussian (EthierKurtz.SDEState d)) :=
  (innerSL ℝ v).integrable_comp IsGaussian.integrable_id

lemma g_int1_eq (v : EthierKurtz.SDEState d) : ∫ z, inner ℝ v z ∂(stdGaussian (EthierKurtz.SDEState d)) = 0 := by
  have := integral_inner (𝕜 := ℝ) (μ := stdGaussian (EthierKurtz.SDEState d)) (f := fun z => z) IsGaussian.integrable_id v
  rw [this, integral_id_stdGaussian, inner_zero_right]

lemma g_memLp (v : EthierKurtz.SDEState d) : MemLp (fun z => inner ℝ v z) 2 (stdGaussian (EthierKurtz.SDEState d)) :=
  (innerSL ℝ v).comp_memLp' (IsGaussian.memLp_two_id)

lemma g_int2 (v v' : EthierKurtz.SDEState d) :
    Integrable (fun z => inner ℝ v z * inner ℝ v' z) (stdGaussian (EthierKurtz.SDEState d)) :=
  (g_memLp v).integrable_mul (g_memLp v')

lemma g_int2_eq (v v' : EthierKurtz.SDEState d) :
    ∫ z, inner ℝ v z * inner ℝ v' z ∂(stdGaussian (EthierKurtz.SDEState d)) = inner ℝ v v' := by
  have h := covarianceBilin_apply (μ := stdGaussian (EthierKurtz.SDEState d)) IsGaussian.memLp_two_id v v'
  rw [covarianceBilin_stdGaussian] at h
  rw [innerSL_apply_apply] at h
  simpa using h.symm


lemma g_term1 (v : EthierKurtz.SDEState d) (c0 c1 : ℝ) :
    Integrable (fun z => c0 + c1 * inner ℝ v z) (stdGaussian (EthierKurtz.SDEState d)) ∧
      ∫ z, (c0 + c1 * inner ℝ v z) ∂(stdGaussian (EthierKurtz.SDEState d)) = c0 := by
  have h1 := (g_int1 v).const_mul c1
  refine ⟨(integrable_const c0).add h1, ?_⟩
  rw [integral_add (integrable_const c0) h1, integral_const_mul, g_int1_eq]
  simp

lemma g_term2 (v v' : EthierKurtz.SDEState d) (c0 c1 c2 c3 : ℝ) :
    Integrable (fun z => c0 + c1 * inner ℝ v z + c2 * inner ℝ v' z
      + c3 * (inner ℝ v z * inner ℝ v' z)) (stdGaussian (EthierKurtz.SDEState d)) ∧
      ∫ z, (c0 + c1 * inner ℝ v z + c2 * inner ℝ v' z
      + c3 * (inner ℝ v z * inner ℝ v' z)) ∂(stdGaussian (EthierKurtz.SDEState d)) = c0 + c3 * inner ℝ v v' := by
  have h1 := (g_int1 v).const_mul c1
  have h2 := (g_int1 v').const_mul c2
  have h3 := (g_int2 v v').const_mul c3
  have h01 : Integrable (fun z => c0 + c1 * inner ℝ v z) (stdGaussian (EthierKurtz.SDEState d)) := (integrable_const c0).add h1
  have h012 : Integrable (fun z => c0 + c1 * inner ℝ v z + c2 * inner ℝ v' z) (stdGaussian (EthierKurtz.SDEState d)) :=
    h01.add h2
  refine ⟨h012.add h3, ?_⟩
  rw [integral_add h012 h3, integral_add h01 h2, integral_add (integrable_const c0) h1,
    integral_const_mul, integral_const_mul, integral_const_mul, g_int1_eq, g_int1_eq, g_int2_eq]
  simp

lemma row_inner (σ : Matrix (Fin d) (Fin d) ℝ) (i j : Fin d) :
    inner ℝ (WithLp.toLp 2 (fun k => σ i k) : EthierKurtz.SDEState d)
      (WithLp.toLp 2 (fun k => σ j k)) = (σ * Matrix.transpose σ) i j := by
  simp [PiLp.inner_apply, Matrix.mul_apply, mul_comm]

lemma gauss1 (σ : Matrix (Fin d) (Fin d) ℝ) (a : EthierKurtz.SDEState d) (s : ℝ)
    (p : Fin d → ℝ) :
    Integrable (fun z => ∑ i, (a + s • mv σ z) i * p i) (stdGaussian (EthierKurtz.SDEState d)) ∧
      ∫ z, ∑ i, (a + s • mv σ z) i * p i ∂(stdGaussian (EthierKurtz.SDEState d)) = ∑ i, a i * p i := by
  have key : ∀ i, Integrable (fun z => (a + s • mv σ z) i * p i) (stdGaussian (EthierKurtz.SDEState d)) ∧
      ∫ z, (a + s • mv σ z) i * p i ∂(stdGaussian (EthierKurtz.SDEState d)) = a i * p i := by
    intro i
    have e : (fun z => (a + s • mv σ z) i * p i) = fun z =>
        a i * p i + (s * p i) * inner ℝ (WithLp.toLp 2 (fun k => σ i k) : EthierKurtz.SDEState d) z := by
      funext z; simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, mv_apply]; ring
    rw [e]; exact g_term1 _ _ _
  refine ⟨integrable_finsetSum _ (fun i _ => (key i).1), ?_⟩
  rw [integral_finsetSum _ (fun i _ => (key i).1)]
  exact Finset.sum_congr rfl (fun i _ => (key i).2)

lemma gauss2 (σ : Matrix (Fin d) (Fin d) ℝ) (a : EthierKurtz.SDEState d) (s : ℝ)
    (Q : Fin d → Fin d → ℝ) :
    Integrable (fun z => ∑ i, ∑ j, (a + s • mv σ z) i * (a + s • mv σ z) j * Q i j) (stdGaussian (EthierKurtz.SDEState d)) ∧
      ∫ z, ∑ i, ∑ j, (a + s • mv σ z) i * (a + s • mv σ z) j * Q i j ∂(stdGaussian (EthierKurtz.SDEState d))
        = ∑ i, ∑ j, (a i * a j + s ^ 2 * (σ * Matrix.transpose σ) i j) * Q i j := by
  have key : ∀ i j, Integrable (fun z => (a + s • mv σ z) i * (a + s • mv σ z) j * Q i j) (stdGaussian (EthierKurtz.SDEState d)) ∧
      ∫ z, (a + s • mv σ z) i * (a + s • mv σ z) j * Q i j ∂(stdGaussian (EthierKurtz.SDEState d))
        = (a i * a j + s ^ 2 * (σ * Matrix.transpose σ) i j) * Q i j := by
    intro i j
    have e : (fun z => (a + s • mv σ z) i * (a + s • mv σ z) j * Q i j) = fun z =>
        a i * a j * Q i j
          + (s * a j * Q i j) * inner ℝ (WithLp.toLp 2 (fun k => σ i k) : EthierKurtz.SDEState d) z
          + (s * a i * Q i j) * inner ℝ (WithLp.toLp 2 (fun k => σ j k) : EthierKurtz.SDEState d) z
          + (s ^ 2 * Q i j) *
            (inner ℝ (WithLp.toLp 2 (fun k => σ i k) : EthierKurtz.SDEState d) z
              * inner ℝ (WithLp.toLp 2 (fun k => σ j k) : EthierKurtz.SDEState d) z) := by
      funext z; simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, mv_apply]; ring
    rw [e]
    refine ⟨(g_term2 _ _ _ _ _ _).1, ?_⟩
    rw [(g_term2 _ _ _ _ _ _).2, row_inner]; ring
  have hi : ∀ i, Integrable (fun z => ∑ j, (a + s • mv σ z) i * (a + s • mv σ z) j * Q i j) (stdGaussian (EthierKurtz.SDEState d)) :=
    fun i => integrable_finsetSum _ (fun j _ => (key i j).1)
  refine ⟨integrable_finsetSum _ (fun i _ => hi i), ?_⟩
  rw [integral_finsetSum _ (fun i _ => hi i)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [integral_finsetSum _ (fun j _ => (key i j).1)]
  exact Finset.sum_congr rfl (fun j _ => (key i j).2)


lemma bind_eq_map (b : EthierKurtz.SDEState d → EthierKurtz.SDEState d) (hb : Continuous b)
    (σ : Matrix (Fin d) (Fin d) ℝ) (η : ℝ) (μt : Measure (EthierKurtz.SDEState d)) [SFinite μt] :
    μt.bind (emStep b σ η) =
      (μt.prod (stdGaussian (EthierKurtz.SDEState d))).map (fun q => q.1 + η • b q.1 + Real.sqrt η • mv σ q.2) := by
  have hT : Measurable (fun q : EthierKurtz.SDEState d × EthierKurtz.SDEState d =>
      q.1 + η • b q.1 + Real.sqrt η • mv σ q.2) := by
    apply Continuous.measurable; unfold mv; fun_prop
  have hT' : ∀ x, Measurable (fun z : EthierKurtz.SDEState d => x + η • b x + Real.sqrt η • mv σ z) :=
    fun x => hT.comp measurable_prodMk_left
  have hκ : Measurable (emStep b σ η) := by
    refine Measure.measurable_of_measurable_coe _ (fun s hs => ?_)
    have : (fun x => emStep b σ η x s) = fun x => (stdGaussian (EthierKurtz.SDEState d)) (Prod.mk x ⁻¹' ((fun q :
        EthierKurtz.SDEState d × EthierKurtz.SDEState d =>
        q.1 + η • b q.1 + Real.sqrt η • mv σ q.2) ⁻¹' s)) := by
      funext x; rw [emStep, Measure.map_apply (hT' x) hs]; rfl
    rw [this]; exact measurable_measure_prodMk_left (hT hs)
  ext s hs
  rw [Measure.bind_apply hs hκ.aemeasurable, Measure.map_apply hT hs, Measure.prod_apply (hT hs)]
  refine lintegral_congr (fun x => ?_)
  rw [emStep, Measure.map_apply (hT' x) hs]; rfl


lemma grad_inner (f : EthierKurtz.SDEState d → ℝ) (w v : EthierKurtz.SDEState d) :
    inner ℝ (gradient f w) v = ∑ i, v i * partial1 f i w := by
  rw [gradient, InnerProductSpace.toDual_symm_apply]
  exact expand1 _ v

lemma core (b : EthierKurtz.SDEState d → EthierKurtz.SDEState d) (hb : Continuous b)
    (σ : Matrix (Fin d) (Fin d) ℝ) (η : ℝ) (hη : 0 ≤ η)
    (μt : Measure (EthierKurtz.SDEState d)) [IsProbabilityMeasure μt]
    (hinv : μt.bind (emStep b σ η) = μt)
    (f : EthierKurtz.SDEState d → ℝ) (hf : ContDiff ℝ 2 f) (hfint : Integrable f μt)
    (hA : Integrable (generator b σ f) μt)
    (hD : Integrable (fun w => ∑ i, ∑ j, b w i * b w j * partial2 f i j w) μt) :
    ∫ w, ∫ z, Jf f w (η • b w + Real.sqrt η • mv σ z) ∂(stdGaussian (EthierKurtz.SDEState d)) ∂μt =
      -(η * ∫ w, generator b σ f w ∂μt)
        - η ^ 2 / 2 * ∫ w, ∑ i, ∑ j, b w i * b w j * partial2 f i j w ∂μt := by
  set T : EthierKurtz.SDEState d × EthierKurtz.SDEState d → EthierKurtz.SDEState d :=
    fun q => q.1 + η • b q.1 + Real.sqrt η • mv σ q.2 with hTdef
  have hTm : Measurable T := by
    apply Continuous.measurable; simp only [hTdef]; unfold mv; fun_prop
  have hmap := bind_eq_map b hb σ η μt
  rw [hinv] at hmap
  have hfc : Continuous f := hf.continuous
  have hFint : Integrable (fun q => f (T q)) (μt.prod (stdGaussian (EthierKurtz.SDEState d))) := by
    have : Integrable f ((μt.prod (stdGaussian (EthierKurtz.SDEState d))).map T) := by rw [← hmap]; exact hfint
    exact (integrable_map_measure hfc.aestronglyMeasurable hTm.aemeasurable).1 this
  have hG : Integrable (fun w => ∫ z, f (T (w, z)) ∂(stdGaussian (EthierKurtz.SDEState d))) μt := hFint.integral_prod_left
  have hGeq : ∫ w, ∫ z, f (T (w, z)) ∂(stdGaussian (EthierKurtz.SDEState d)) ∂μt = ∫ w, f w ∂μt := by
    rw [← integral_prod _ hFint]
    conv_rhs => rw [hmap]
    rw [integral_map hTm.aemeasurable hfc.aestronglyMeasurable]
  have hsec := hFint.prod_right_ae
  have hpt : ∀ᵐ w ∂μt, ∫ z, Jf f w (η • b w + Real.sqrt η • mv σ z) ∂(stdGaussian (EthierKurtz.SDEState d)) =
      (∫ z, f (T (w, z)) ∂(stdGaussian (EthierKurtz.SDEState d))) - f w - η * generator b σ f w
        - η ^ 2 / 2 * ∑ i, ∑ j, b w i * b w j * partial2 f i j w := by
    filter_upwards [hsec] with w hw
    obtain ⟨i1, e1⟩ := gauss1 σ (η • b w) (Real.sqrt η) (fun i => partial1 f i w)
    obtain ⟨i2, e2⟩ := gauss2 σ (η • b w) (Real.sqrt η) (fun i j => partial2 f i j w)
    have hJ : (fun z => Jf f w (η • b w + Real.sqrt η • mv σ z)) = fun z =>
        f (T (w, z)) - f w - ∑ i, (η • b w + Real.sqrt η • mv σ z) i * partial1 f i w
          - (1 / 2) * ∑ i, ∑ j, (η • b w + Real.sqrt η • mv σ z) i
              * (η • b w + Real.sqrt η • mv σ z) j * partial2 f i j w := by
      funext z
      have hT : T (w, z) = w + (η • b w + Real.sqrt η • mv σ z) := by
        simp only [hTdef, add_assoc]
      rw [hT, taylor f hf w (η • b w + Real.sqrt η • mv σ z)]; ring
    have ha : Integrable (fun z => f (T (w, z)) - f w) (stdGaussian (EthierKurtz.SDEState d)) := hw.sub (integrable_const _)
    have hb' : Integrable (fun z => f (T (w, z)) - f w
        - ∑ i, (η • b w + Real.sqrt η • mv σ z) i * partial1 f i w) (stdGaussian (EthierKurtz.SDEState d)) := ha.sub i1
    rw [hJ, integral_sub hb' (i2.const_mul _), integral_sub ha i1, integral_sub hw (integrable_const _),
      integral_const_mul, e1, e2]
    have hS1 : ∑ i, (η • b w) i * partial1 f i w = η * ∑ i, b w i * partial1 f i w := by
      simp only [PiLp.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
    have hS2 : ∑ i, ∑ j, ((η • b w) i * (η • b w) j + Real.sqrt η ^ 2 * (σ * Matrix.transpose σ) i j)
        * partial2 f i j w = η ^ 2 * ∑ i, ∑ j, b w i * b w j * partial2 f i j w
          + η * ∑ i, ∑ j, (σ * Matrix.transpose σ) i j * partial2 f i j w := by
      rw [Real.sq_sqrt hη]
      simp only [PiLp.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      ring
    have hgen : generator b σ f w = ∑ i, b w i * partial1 f i w
        + (1 / 2) * ∑ i, ∑ j, (σ * Matrix.transpose σ) i j * partial2 f i j w := by
      rw [generator, grad_inner]
    rw [hS1, hS2, hgen]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    ring
  rw [integral_congr_ae hpt]
  have h1 : Integrable (fun w => (∫ z, f (T (w, z)) ∂(stdGaussian (EthierKurtz.SDEState d))) - f w) μt := hG.sub hfint
  have h2 : Integrable (fun w => (∫ z, f (T (w, z)) ∂(stdGaussian (EthierKurtz.SDEState d))) - f w - η * generator b σ f w) μt :=
    h1.sub (hA.const_mul _)
  rw [integral_sub h2 (hD.const_mul _), integral_sub h1 (hA.const_mul _), integral_sub hG hfint,
    hGeq, integral_const_mul, integral_const_mul]
  ring


lemma coord_le (x : EthierKurtz.SDEState d) (i : Fin d) : |x i| ≤ ‖x‖ := by
  simpa [Real.norm_eq_abs] using PiLp.norm_apply_le x i

lemma drift_bound (M : Model d) :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ (w : EthierKurtz.SDEState d) (i : Fin d), |M.drift w i| ≤ G * (1 + ‖w‖) := by
  set v := Matrix.mulVec (M.R - M.α • (1 : Matrix (Fin d) (Fin d) ℝ)) M.p with hv
  let Gi : Fin d → ℝ := fun i => |M.β| * |M.p i| + ∑ j, |M.R i j| + (d : ℝ) * |v i|
  have hGi : ∀ i, 0 ≤ Gi i := fun i => by positivity
  refine ⟨∑ i, Gi i, Finset.sum_nonneg (fun i _ => hGi i), fun w i => ?_⟩
  have hle : Gi i ≤ ∑ i, Gi i := Finset.single_le_sum (fun i _ => hGi i) (Finset.mem_univ i)
  have hw0 : 0 ≤ ‖w‖ := norm_nonneg _
  have hcoord : M.drift w i = -(M.β * M.p i) - ∑ j, M.R i j * w j
      + max 0 (∑ k, w k) * v i := by
    simp [Model.drift, hv, Matrix.mulVec, dotProduct]
  have h1 : |∑ j, M.R i j * w j| ≤ (∑ j, |M.R i j|) * ‖w‖ := by
    calc |∑ j, M.R i j * w j| ≤ ∑ j, |M.R i j * w j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, |M.R i j| * ‖w‖ := Finset.sum_le_sum (fun j _ => by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left (coord_le w j) (abs_nonneg _))
      _ = (∑ j, |M.R i j|) * ‖w‖ := by rw [Finset.sum_mul]
  have h2 : |max 0 (∑ k, w k)| ≤ (d : ℝ) * ‖w‖ := by
    have : |∑ k, w k| ≤ (d : ℝ) * ‖w‖ := by
      calc |∑ k, w k| ≤ ∑ k, |w k| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _k : Fin d, ‖w‖ := Finset.sum_le_sum (fun k _ => coord_le w k)
        _ = (d : ℝ) * ‖w‖ := by simp
    rw [abs_of_nonneg (le_max_left _ _)]
    exact max_le (by positivity) (le_trans (le_abs_self _) this)
  have h3 : |max 0 (∑ k, w k) * v i| ≤ (d : ℝ) * ‖w‖ * |v i| := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
  have h4 : |M.β * M.p i| = |M.β| * |M.p i| := abs_mul _ _
  have key : |M.drift w i| ≤ Gi i * (1 + ‖w‖) := by
    rw [hcoord]
    have t1 := abs_add_le (-(M.β * M.p i) - ∑ j, M.R i j * w j) (max 0 (∑ k, w k) * v i)
    have t2 := abs_sub (-(M.β * M.p i)) (∑ j, M.R i j * w j)
    rw [abs_neg] at t2
    have e1 : 0 ≤ |M.β| * |M.p i| * ‖w‖ := by positivity
    have e2 : 0 ≤ ∑ j, |M.R i j| := Finset.sum_nonneg (fun j _ => abs_nonneg _)
    have e3 : 0 ≤ (d : ℝ) * |v i| := by positivity
    simp only [Gi]
    nlinarith
  calc |M.drift w i| ≤ Gi i * (1 + ‖w‖) := key
    _ ≤ (∑ i, Gi i) * (1 + ‖w‖) := mul_le_mul_of_nonneg_right hle (by positivity)

lemma pow_le_one_add_pow5 (t : ℝ) (ht : 0 ≤ t) (k : ℕ) (hk : k ≤ 5) : t ^ k ≤ 1 + t ^ 5 := by
  rcases le_total t 1 with h | h
  · have : t ^ k ≤ 1 := pow_le_one₀ ht h
    have : 0 ≤ t ^ 5 := by positivity
    linarith
  · have : t ^ k ≤ t ^ 5 := pow_le_pow_right₀ h hk
    linarith

lemma poly_bound (t : ℝ) (ht : 0 ≤ t) : (1 + t) ^ 2 * (1 + t ^ 3) ≤ 8 * (1 + t ^ 5) := by
  have e : (1 + t) ^ 2 * (1 + t ^ 3) = 1 + 2 * t + t ^ 2 + t ^ 3 + 2 * t ^ 4 + t ^ 5 := by ring
  have h1 := pow_le_one_add_pow5 t ht 1 (by norm_num)
  have h2 := pow_le_one_add_pow5 t ht 2 (by norm_num)
  have h3 := pow_le_one_add_pow5 t ht 3 (by norm_num)
  have h4 := pow_le_one_add_pow5 t ht 4 (by norm_num)
  rw [pow_one] at h1
  rw [e]; linarith

lemma integrable_of_poly (μt : Measure (EthierKurtz.SDEState d)) [IsProbabilityMeasure μt]
    (h5 : Integrable (fun x => ‖x‖ ^ 5) μt) (F : EthierKurtz.SDEState d → ℝ)
    (hF : Continuous F) (A : ℝ) (hb : ∀ x, |F x| ≤ A * (1 + ‖x‖ ^ 5)) : Integrable F μt :=
  Integrable.mono' (((integrable_const 1).add h5).const_mul A) hF.aestronglyMeasurable
    (ae_of_all _ (fun x => by simpa [Real.norm_eq_abs] using hb x))


lemma partial1_cont (f : EthierKurtz.SDEState d → ℝ) (hf : ContDiff ℝ 2 f) (i : Fin d) :
    Continuous (partial1 f i) := by
  have : Continuous (fderiv ℝ f) := hf.continuous_fderiv two_ne_zero
  exact this.clm_apply continuous_const

lemma partial2_cont (f : EthierKurtz.SDEState d → ℝ) (hf : ContDiff ℝ 2 f) (i j : Fin d) :
    Continuous (partial2 f i j) := by
  have hc1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have : Continuous (fderiv ℝ (fderiv ℝ f)) := hc1.continuous_fderiv one_ne_zero
  have e : partial2 f i j = fun y => fderiv ℝ (fderiv ℝ f) y (EuclideanSpace.single i 1)
      (EuclideanSpace.single j 1) := funext (partial2_eq f i j)
  rw [e]
  exact (this.clm_apply continuous_const).clm_apply continuous_const

lemma Jf_cont (f : EthierKurtz.SDEState d → ℝ) (hf : ContDiff ℝ 2 f) :
    Continuous (fun q : EthierKurtz.SDEState d × EthierKurtz.SDEState d => Jf f q.1 q.2) := by
  have e : (fun q : EthierKurtz.SDEState d × EthierKurtz.SDEState d => Jf f q.1 q.2) = fun q =>
      f (q.1 + q.2) - f q.1 - ∑ i, q.2 i * partial1 f i q.1
        - (1 / 2) * ∑ i, ∑ j, q.2 i * q.2 j * partial2 f i j q.1 := by
    funext q; have := taylor f hf q.1 q.2; linarith
  rw [e]
  have hfc := hf.continuous
  have h1 := partial1_cont f hf
  have h2 := partial2_cont f hf
  refine ((((hfc.comp (continuous_fst.add continuous_snd)).sub (hfc.comp continuous_fst)).sub
    (continuous_finsetSum _ (fun i _ => ?_))).sub (continuous_const.mul
      (continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ => ?_)))))
  · exact ((PiLp.continuous_apply 2 _ i).comp continuous_snd).mul ((h1 i).comp continuous_fst)
  · exact (((PiLp.continuous_apply 2 _ i).comp continuous_snd).mul
      ((PiLp.continuous_apply 2 _ j).comp continuous_snd)).mul ((h2 i j).comp continuous_fst)

lemma J_split (μt : Measure (EthierKurtz.SDEState d)) [SFinite μt]
    (F : EthierKurtz.SDEState d × EthierKurtz.SDEState d → ℝ) (hF : Continuous F)
    (δ : EthierKurtz.SDEState d × EthierKurtz.SDEState d → EthierKurtz.SDEState d)
    (hδ : Continuous δ) (X Y : ℝ)
    (hX : ∫⁻ w, ∫⁻ z, (if ‖δ (w, z)‖ < 1 then ENNReal.ofReal |F (w, z)| else 0) ∂(stdGaussian (EthierKurtz.SDEState d)) ∂μt
      ≤ ENNReal.ofReal X)
    (hY : ∫⁻ w, ∫⁻ z, (if 1 ≤ ‖δ (w, z)‖ then ENNReal.ofReal |F (w, z)| else 0) ∂(stdGaussian (EthierKurtz.SDEState d)) ∂μt
      ≤ ENNReal.ofReal Y) :
    ∫⁻ w, ∫⁻ z, ‖F (w, z)‖ₑ ∂(stdGaussian (EthierKurtz.SDEState d)) ∂μt ≤ ENNReal.ofReal X + ENNReal.ofReal Y := by
  set A : EthierKurtz.SDEState d × EthierKurtz.SDEState d → ℝ≥0∞ :=
    fun q => if ‖δ q‖ < 1 then ENNReal.ofReal |F q| else 0 with hAdef
  set B : EthierKurtz.SDEState d × EthierKurtz.SDEState d → ℝ≥0∞ :=
    fun q => if 1 ≤ ‖δ q‖ then ENNReal.ofReal |F q| else 0 with hBdef
  have hAm : Measurable A := by
    refine Measurable.ite (measurableSet_lt (hδ.norm.measurable) measurable_const) ?_ measurable_const
    exact ENNReal.measurable_ofReal.comp (hF.abs.measurable)
  have hsplit : ∀ q, ‖F q‖ₑ = A q + B q := by
    intro q
    rw [Real.enorm_eq_ofReal_abs]
    by_cases h : ‖δ q‖ < 1
    · simp [hAdef, hBdef, h, not_le.mpr h]
    · simp [hAdef, hBdef, h, le_of_not_gt h]
  have hinner : ∀ w, ∫⁻ z, ‖F (w, z)‖ₑ ∂(stdGaussian (EthierKurtz.SDEState d)) = ∫⁻ z, A (w, z) ∂(stdGaussian (EthierKurtz.SDEState d)) + ∫⁻ z, B (w, z) ∂(stdGaussian (EthierKurtz.SDEState d)) := by
    intro w
    simp_rw [hsplit]
    exact lintegral_add_left (hAm.comp measurable_prodMk_left) _
  simp_rw [hinner]
  rw [lintegral_add_left hAm.lintegral_prod_right']
  exact add_le_add hX hY

lemma abs_iint_le (μt : Measure (EthierKurtz.SDEState d))
    (F : EthierKurtz.SDEState d × EthierKurtz.SDEState d → ℝ) (X : ℝ) (hX : 0 ≤ X)
    (h : ∫⁻ w, ∫⁻ z, ‖F (w, z)‖ₑ ∂(stdGaussian (EthierKurtz.SDEState d)) ∂μt ≤ ENNReal.ofReal X) :
    |∫ w, ∫ z, F (w, z) ∂(stdGaussian (EthierKurtz.SDEState d)) ∂μt| ≤ X := by
  have h1 : ‖∫ w, ∫ z, F (w, z) ∂(stdGaussian (EthierKurtz.SDEState d)) ∂μt‖ₑ ≤ ENNReal.ofReal X := by
    refine (enorm_integral_le_lintegral_enorm _).trans (le_trans ?_ h)
    exact lintegral_mono (fun w => enorm_integral_le_lintegral_enorm _)
  rw [Real.enorm_eq_ofReal_abs] at h1
  exact (ENNReal.ofReal_le_ofReal_iff hX).1 h1


lemma lip_cont (h : EthierKurtz.SDEState d → ℝ) (hh : IsLip1 h) : Continuous h := by
  have : LipschitzWith 1 h := LipschitzWith.of_dist_le_mul (fun x y => by
    rw [Real.dist_eq, dist_eq_norm]; simpa using hh x y)
  exact this.continuous

lemma kl (b : EthierKurtz.SDEState d → EthierKurtz.SDEState d) (hb : Continuous b)
    (G : ℝ) (hG0 : 0 ≤ G) (hG : ∀ w i, |b w i| ≤ G * (1 + ‖w‖))
    (σ : Matrix (Fin d) (Fin d) ℝ) (η : ℝ) (hη : 0 < η)
    (μt : Measure (EthierKurtz.SDEState d)) [IsProbabilityMeasure μt]
    (hinv : μt.bind (emStep b σ η) = μt)
    (K5 : ℝ) (h5 : Integrable (fun x => ‖x‖ ^ 5) μt) (hK5 : ∫ x, ‖x‖ ^ 5 ∂μt ≤ K5)
    (f : EthierKurtz.SDEState d → ℝ) (hf : ContDiff ℝ 2 f) (C2 : ℝ) (hC2 : 0 < C2)
    (hfb : ∀ x, |f x| ≤ C2 * (1 + ‖x‖))
    (hQb : ∀ x i j, |partial2 f i j x| ≤ C2 * (1 + ‖x‖ ^ 3))
    (h : EthierKurtz.SDEState d → ℝ) (hh : IsLip1Zero h) (c : ℝ)
    (hgen : ∀ x, generator b σ f x = h x - c)
    (X : ℝ) (hX0 : 0 ≤ X)
    (hJ : ∫⁻ w, ∫⁻ z, ‖Jf f w (η • b w + Real.sqrt η • mv σ z)‖ₑ ∂(stdGaussian (EthierKurtz.SDEState d)) ∂μt ≤ ENNReal.ofReal X) :
    |∫ x, h x ∂μt - c| ≤ X / η + η / 2 * ((d : ℝ) * d * G ^ 2 * C2 * 8 * (1 + K5)) := by
  have hhc : Continuous h := lip_cont h hh.1
  have hhb : ∀ x, |h x| ≤ ‖x‖ := fun x => by simpa [hh.2] using hh.1 x 0
  have hhint : Integrable h μt := integrable_of_poly μt h5 h hhc 1 (fun x => by
    have := pow_le_one_add_pow5 ‖x‖ (norm_nonneg _) 1 (by norm_num)
    rw [pow_one] at this; linarith [hhb x])
  have hfint : Integrable f μt := integrable_of_poly μt h5 f hf.continuous (2 * C2) (fun x => by
    have := pow_le_one_add_pow5 ‖x‖ (norm_nonneg _) 1 (by norm_num)
    rw [pow_one] at this
    calc |f x| ≤ C2 * (1 + ‖x‖) := hfb x
      _ ≤ C2 * (2 * (1 + ‖x‖ ^ 5)) := mul_le_mul_of_nonneg_left
          (by have : 0 ≤ ‖x‖ ^ 5 := by positivity
              linarith) hC2.le
      _ = 2 * C2 * (1 + ‖x‖ ^ 5) := by ring)
  have hA : Integrable (generator b σ f) μt := by
    rw [show generator b σ f = fun x => h x - c from funext hgen]
    exact hhint.sub (integrable_const c)
  set K1 : ℝ := (d : ℝ) * d * G ^ 2 * C2 * 8 with hK1
  have hK1nn : 0 ≤ K1 := by positivity
  have hDc : Continuous (fun w => ∑ i, ∑ j, b w i * b w j * partial2 f i j w) := by
    refine continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ => ?_))
    exact (((PiLp.continuous_apply 2 _ i).comp hb).mul ((PiLp.continuous_apply 2 _ j).comp hb)).mul
      (partial2_cont f hf i j)
  have hDb : ∀ w, |∑ i, ∑ j, b w i * b w j * partial2 f i j w| ≤ K1 * (1 + ‖w‖ ^ 5) := by
    intro w
    have ht := norm_nonneg w
    have hterm : ∀ i j, |b w i * b w j * partial2 f i j w|
        ≤ G ^ 2 * C2 * ((1 + ‖w‖) ^ 2 * (1 + ‖w‖ ^ 3)) := by
      intro i j
      rw [abs_mul, abs_mul]
      have h1 := hG w i
      have h2 := hG w j
      have h3 := hQb w i j
      calc |b w i| * |b w j| * |partial2 f i j w|
          ≤ (G * (1 + ‖w‖)) * (G * (1 + ‖w‖)) * (C2 * (1 + ‖w‖ ^ 3)) := by
            gcongr
        _ = G ^ 2 * C2 * ((1 + ‖w‖) ^ 2 * (1 + ‖w‖ ^ 3)) := by ring
    calc |∑ i, ∑ j, b w i * b w j * partial2 f i j w|
        ≤ ∑ i, |∑ j, b w i * b w j * partial2 f i j w| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |b w i * b w j * partial2 f i j w| :=
          Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ _i : Fin d, ∑ _j : Fin d, G ^ 2 * C2 * ((1 + ‖w‖) ^ 2 * (1 + ‖w‖ ^ 3)) :=
          Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hterm i j))
      _ = (d : ℝ) * d * (G ^ 2 * C2 * ((1 + ‖w‖) ^ 2 * (1 + ‖w‖ ^ 3))) := by
          simp [Finset.sum_const, Finset.card_univ]; ring
      _ ≤ (d : ℝ) * d * (G ^ 2 * C2 * (8 * (1 + ‖w‖ ^ 5))) := by
          have := mul_le_mul_of_nonneg_left (poly_bound _ ht)
            (by positivity : (0:ℝ) ≤ (d : ℝ) * d * (G ^ 2 * C2))
          nlinarith [this]
      _ = K1 * (1 + ‖w‖ ^ 5) := by rw [hK1]; ring
  have hD : Integrable (fun w => ∑ i, ∑ j, b w i * b w j * partial2 f i j w) μt :=
    integrable_of_poly μt h5 _ hDc K1 hDb
  have hDint : |∫ w, ∑ i, ∑ j, b w i * b w j * partial2 f i j w ∂μt| ≤ K1 * (1 + K5) := by
    refine (abs_integral_le_integral_abs).trans ?_
    have hP : Integrable (fun w : EthierKurtz.SDEState d => K1 * (1 + ‖w‖ ^ 5)) μt :=
      ((integrable_const 1).add h5).const_mul K1
    calc ∫ w, |∑ i, ∑ j, b w i * b w j * partial2 f i j w| ∂μt
        ≤ ∫ w, K1 * (1 + ‖w‖ ^ 5) ∂μt := integral_mono hD.abs hP hDb
      _ = K1 * (1 + ∫ w, ‖w‖ ^ 5 ∂μt) := by
          rw [integral_const_mul, integral_add (integrable_const 1) h5]; simp
      _ ≤ K1 * (1 + K5) := by gcongr
  have hcore := core b hb σ η hη.le μt hinv f hf hfint hA hD
  have hJabs : |∫ w, ∫ z, Jf f w (η • b w + Real.sqrt η • mv σ z) ∂(stdGaussian (EthierKurtz.SDEState d)) ∂μt| ≤ X :=
    abs_iint_le μt (fun q => Jf f q.1 (η • b q.1 + Real.sqrt η • mv σ q.2)) X hX0 hJ
  have hAeq : ∫ w, generator b σ f w ∂μt = ∫ x, h x ∂μt - c := by
    rw [show generator b σ f = fun x => h x - c from funext hgen,
      integral_sub hhint (integrable_const c)]
    simp
  rw [hcore, hAeq] at hJabs
  set I := ∫ x, h x ∂μt - c
  set D := ∫ w, ∑ i, ∑ j, b w i * b w j * partial2 f i j w ∂μt
  have key : η * |I| ≤ η * (X / η + η / 2 * (K1 * (1 + K5))) := by
    have e : η * (X / η + η / 2 * (K1 * (1 + K5))) = X + η ^ 2 / 2 * (K1 * (1 + K5)) := by
      field_simp
    rw [e]
    have e2 : η * |I| = |-(η * I) - η ^ 2 / 2 * D + η ^ 2 / 2 * D| := by
      rw [show -(η * I) - η ^ 2 / 2 * D + η ^ 2 / 2 * D = -(η * I) by ring, abs_neg, abs_mul,
        abs_of_pos hη]
    rw [e2]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ η ^ 2 / 2)]
    have : η ^ 2 / 2 * |D| ≤ η ^ 2 / 2 * (K1 * (1 + K5)) :=
      mul_le_mul_of_nonneg_left hDint (by positivity)
    linarith
  exact le_of_mul_le_mul_left key hη


end EMErrAux

open GPhNGIDiffusion.EMError EMErrAux in
theorem solution {d : ℕ} (M : Model d)
    (P : ℝ≥0 → EthierKurtz.SDEState d → Measure (EthierKurtz.SDEState d))
    (hP : IsTransitionFunction M.drift M.σ P)
    (μ : Measure (EthierKurtz.SDEState d)) (hμ : IsInvariantMeasure P μ) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ ς : ℝ, 0 < ς → ς < 1 → ∃ Cς : ℝ, 0 < Cς ∧
      ∀ η : ℝ, 0 < η → η ≤ η₀ →
        (∃! μt : Measure (EthierKurtz.SDEState d), IsEMInvariant M.drift M.σ η μt) ∧
        ∀ μt : Measure (EthierKurtz.SDEState d), IsEMInvariant M.drift M.σ η μt →
          dW μ μt ≤ ENNReal.ofReal (Cς * η ^ ((1 - ς) / 2)) := by
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with rfl | h
    · have := M.hp_sum; simp at this
    · exact h
  let i0 : Fin d := ⟨0, hd⟩
  obtain ⟨η₁0, hη₁0, huniq0, hmom⟩ := proposition_2_1_unique_moments M
  obtain ⟨ηL, hηL, C5, hC5'⟩ := hmom 5 (by norm_num)
  set η₁ : ℝ := min η₁0 ηL
  have hη₁ : 0 < η₁ := lt_min hη₁0 hηL
  have hC5 : ∀ η : ℝ, 0 < η → η ≤ η₁ → ∀ μt : Measure (EthierKurtz.SDEState d),
      IsEMInvariant M.drift M.σ η μt → ∫⁻ x, ‖x‖ₑ ^ 5 ∂μt ≤ ENNReal.ofReal C5 :=
    fun η h hl => hC5' η h (hl.trans (min_le_right _ _))
  have huniq : ∀ η : ℝ, 0 < η → η ≤ η₁ → ∃! μt : Measure (EthierKurtz.SDEState d),
      IsEMInvariant M.drift M.σ η μt :=
    fun η h hl => huniq0 η h (hl.trans (min_le_left _ _))
  obtain ⟨⟨C2, hC2, hstein⟩, -⟩ := lemma_2_2 M P hP μ hμ
  obtain ⟨η₂, hη₂, hη₂1, hcl1, C', hC', hcl2⟩ := claims_2_7_2_8 M P hP μ hμ
  obtain ⟨G, hG0, hG⟩ := drift_bound M
  have hbc : Continuous M.drift := by unfold Model.drift; fun_prop
  haveI : IsProbabilityMeasure μ := hμ.1
  refine ⟨min η₁ η₂, lt_min hη₁ hη₂, fun ς hς0 hς1 => ?_⟩
  obtain ⟨Cς, hCς, hcl1'⟩ := hcl1 ς hς0 hς1
  set K5 : ℝ := max C5 0 with hK5def
  set K1 : ℝ := (d : ℝ) * d * G ^ 2 * C2 * 8 * (1 + K5) with hK1def
  have hK1 : 0 ≤ K1 := by positivity
  refine ⟨Cς + C' + K1 / 2 + 1, by positivity, fun η hη hηle =>
    ⟨huniq η hη (hηle.trans (min_le_left _ _)), fun μt hμt => ?_⟩⟩
  have hη1 : η ≤ η₁ := hηle.trans (min_le_left _ _)
  have hη2 : η ≤ η₂ := hηle.trans (min_le_right _ _)
  have hηlt1 : η < 1 := lt_of_le_of_lt hη2 hη₂1
  haveI : IsProbabilityMeasure μt := hμt.1
  -- moments of μt
  have hl5 := hC5 η hη hη1 μt hμt
  have h5 : Integrable (fun x : EthierKurtz.SDEState d => ‖x‖ ^ 5) μt := by
    refine ⟨(continuous_norm.pow 5).aestronglyMeasurable, ?_⟩
    simp only [HasFiniteIntegral, enorm_pow, enorm_norm]
    exact lt_of_le_of_lt hl5 ENNReal.ofReal_lt_top
  have hK5 : ∫ x, ‖x‖ ^ 5 ∂μt ≤ K5 := by
    rw [integral_eq_lintegral_of_nonneg_ae (f := fun x : EthierKurtz.SDEState d => ‖x‖ ^ 5)
      (ae_of_all _ (fun x => pow_nonneg (norm_nonneg x) 5))
      (continuous_norm.pow 5).aestronglyMeasurable]
    refine ENNReal.toReal_le_of_le_ofReal (le_max_right _ _) ?_
    have e : ∀ x : EthierKurtz.SDEState d, ENNReal.ofReal (‖x‖ ^ 5) = ‖x‖ₑ ^ 5 := fun x => by
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    simp_rw [e]
    exact hl5.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hnt : Integrable (fun x : EthierKurtz.SDEState d => ‖x‖) μt :=
    integrable_of_poly μt h5 _ continuous_norm 1 (fun x => by
      have := pow_le_one_add_pow5 ‖x‖ (norm_nonneg _) 1 (by norm_num)
      rw [pow_one] at this; rw [abs_of_nonneg (norm_nonneg _)]; linarith)
  -- the key estimate for h ∈ Lip₀(1)
  set X : ℝ := Cς * η ^ ((3 - ς) / 2) + C' * η ^ (3 / 2 : ℝ) with hXdef
  have hX0 : 0 ≤ X := by positivity
  have KL : ∀ h : EthierKurtz.SDEState d → ℝ, IsLip1Zero h →
      |∫ x, h x ∂μt - ∫ x, h x ∂μ| ≤ X / η + η / 2 * K1 := by
    intro h hh
    obtain ⟨hfC2, hgen, hbds⟩ := hstein h hh
    have hδc : Continuous (fun q : EthierKurtz.SDEState d × EthierKurtz.SDEState d =>
        η • M.drift q.1 + Real.sqrt η • mv M.σ q.2) := by unfold mv; fun_prop
    have hFc : Continuous (fun q : EthierKurtz.SDEState d × EthierKurtz.SDEState d =>
        Jf (steinSolution P μ h) q.1 (η • M.drift q.1 + Real.sqrt η • mv M.σ q.2)) :=
      Continuous.comp (g := fun q : EthierKurtz.SDEState d × EthierKurtz.SDEState d =>
          Jf (steinSolution P μ h) q.1 q.2)
        (f := fun q : EthierKurtz.SDEState d × EthierKurtz.SDEState d =>
          (q.1, η • M.drift q.1 + Real.sqrt η • mv M.σ q.2))
        (Jf_cont (steinSolution P μ h) hfC2) (continuous_fst.prodMk hδc)
    have hJ := J_split μt _ hFc _ hδc _ _ (hcl1' η hη hη2 μt hμt h hh) (hcl2 η hη hη2 μt hμt h hh)
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)] at hJ
    exact kl M.drift hbc G hG0 hG M.σ η hη μt hμt.2 K5 h5 hK5 _ hfC2 C2 hC2
      (fun x => (hbds x i0 i0).1) (fun x i j => (hbds x i j).2.2) h hh _ hgen X hX0 hJ
  -- the bound in terms of η^{(1-ς)/2}
  set e : ℝ := η ^ ((1 - ς) / 2) with hedef
  have he0 : 0 < e := Real.rpow_pos_of_pos hη _
  have hbound : X / η + η / 2 * K1 ≤ (Cς + C' + K1 / 2 + 1) * e := by
    have r1 : η ^ ((3 - ς) / 2) = η * e := by
      rw [hedef, ← Real.rpow_one_add' hη.le (by linarith)]; congr 1; ring
    have r2 : η ^ (3 / 2 : ℝ) = η * η ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_one_add' hη.le (by norm_num)]; norm_num
    have r3 : η ^ (1 / 2 : ℝ) ≤ e :=
      Real.rpow_le_rpow_of_exponent_ge hη hηlt1.le (by linarith)
    have r4 : η ≤ e := by
      have := Real.rpow_le_rpow_of_exponent_ge hη hηlt1.le
        (show (1 - ς) / 2 ≤ (1 : ℝ) by linarith)
      rwa [Real.rpow_one] at this
    have hXe : X / η = Cς * e + C' * η ^ (1 / 2 : ℝ) := by
      rw [hXdef, r1, r2]; field_simp
    rw [hXe]
    have : C' * η ^ (1 / 2 : ℝ) ≤ C' * e := mul_le_mul_of_nonneg_left r3 hC'.le
    have : η / 2 * K1 ≤ K1 / 2 * e := by nlinarith
    nlinarith
  -- first moment of μ
  have hfin : ∫⁻ x, ‖x‖ₑ ∂μ < ⊤ := by
    have hbnd : ∀ n : ℕ, ∫⁻ x, ENNReal.ofReal (min ‖x‖ (n : ℝ)) ∂μ
        ≤ ENNReal.ofReal (∫ x, ‖x‖ ∂μt + (X / η + η / 2 * K1)) := by
      intro n
      have hn : IsLip1Zero (fun x : EthierKurtz.SDEState d => min ‖x‖ (n : ℝ)) := by
        refine ⟨fun x y => ?_, by simp⟩
        refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
        simp only [sub_self, abs_zero]
        exact max_le (abs_norm_sub_norm_le x y) (norm_nonneg _)
      have hmc : Continuous (fun x : EthierKurtz.SDEState d => min ‖x‖ (n : ℝ)) := by fun_prop
      have hmb : ∀ x : EthierKurtz.SDEState d, ‖min ‖x‖ (n : ℝ)‖ ≤ n := fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min (norm_nonneg _) (Nat.cast_nonneg _))]
        exact min_le_right _ _
      have hiμ : Integrable (fun x : EthierKurtz.SDEState d => min ‖x‖ (n : ℝ)) μ :=
        Integrable.mono' (integrable_const (n : ℝ)) hmc.aestronglyMeasurable (ae_of_all _ hmb)
      have hiμt : Integrable (fun x : EthierKurtz.SDEState d => min ‖x‖ (n : ℝ)) μt :=
        Integrable.mono' (integrable_const (n : ℝ)) hmc.aestronglyMeasurable (ae_of_all _ hmb)
      have hk := KL _ hn
      have hmono : ∫ x, min ‖x‖ (n : ℝ) ∂μt ≤ ∫ x, ‖x‖ ∂μt :=
        integral_mono hiμt hnt (fun x => min_le_left _ _)
      rw [← ofReal_integral_eq_lintegral_ofReal hiμ
        (ae_of_all _ (fun x => le_min (norm_nonneg _) (Nat.cast_nonneg _)))]
      apply ENNReal.ofReal_le_ofReal
      have := (abs_le.1 hk).1
      linarith
    have hpt : ∀ x : EthierKurtz.SDEState d,
        ‖x‖ₑ = ⨆ n : ℕ, ENNReal.ofReal (min ‖x‖ (n : ℝ)) := by
      intro x
      refine le_antisymm ?_ (iSup_le (fun n => ?_))
      · obtain ⟨n, hn⟩ := exists_nat_ge ‖x‖
        refine le_iSup_of_le n ?_
        rw [min_eq_left hn, ofReal_norm]
      · rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (min_le_left _ _)
    rw [lintegral_congr hpt, lintegral_iSup (fun n => (by fun_prop : Measurable
      (fun x : EthierKurtz.SDEState d => ENNReal.ofReal (min ‖x‖ (n : ℝ)))))
      (fun n m hnm x => ENNReal.ofReal_le_ofReal (min_le_min_left _ (Nat.cast_le.mpr hnm)))]
    exact lt_of_le_of_lt (iSup_le hbnd) ENNReal.ofReal_lt_top
  have hfint : ∫⁻ x, ‖x‖ₑ ∂μt < ⊤ := by
    have := hnt.hasFiniteIntegral
    simpa [HasFiniteIntegral, enorm_norm] using this
  have hnμ : Integrable (fun x : EthierKurtz.SDEState d => ‖x‖) μ :=
    ⟨continuous_norm.aestronglyMeasurable, by simpa [HasFiniteIntegral, enorm_norm] using hfin⟩
  rw [dW, if_pos ⟨measure_lt_top _ _, measure_lt_top _ _, hfin, hfint⟩]
  refine iSup₂_le (fun h hh => ENNReal.ofReal_le_ofReal ?_)
  have hhc := lip_cont h hh
  have hhb : ∀ x, ‖h x‖ ≤ |h 0| + ‖x‖ := fun x => by
    have := hh x 0
    rw [sub_zero] at this
    rw [Real.norm_eq_abs]
    have := abs_sub_abs_le_abs_sub (h x) (h 0)
    linarith
  have hiμ : Integrable h μ :=
    Integrable.mono' ((integrable_const _).add hnμ) hhc.aestronglyMeasurable (ae_of_all _ hhb)
  have hiμt : Integrable h μt :=
    Integrable.mono' ((integrable_const _).add hnt) hhc.aestronglyMeasurable (ae_of_all _ hhb)
  have hh0 : IsLip1Zero (fun x => h x - h 0) :=
    ⟨fun x y => by simpa using hh x y, by simp⟩
  have hk := KL _ hh0
  rw [integral_sub hiμt (integrable_const _), integral_sub hiμ (integrable_const _)] at hk
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hk
  rw [abs_sub_comm]
  calc |∫ x, h x ∂μt - ∫ x, h x ∂μ| = |∫ x, h x ∂μt - h 0 - (∫ x, h x ∂μ - h 0)| := by ring_nf
    _ ≤ X / η + η / 2 * K1 := hk
    _ ≤ (Cς + C' + K1 / 2 + 1) * e := hbound
