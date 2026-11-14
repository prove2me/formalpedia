-- Prove2me | solution 1 for BosonicLearn.gaussian_bilinear_exp_bound
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-14T02:26:55.276882+00:00
-- url     : https://prove2.me/submissions/a2f6bc7d-c29b-454c-901a-b8cb056ce4b5

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped Matrix

/-!
# A Gaussian chaos bound: `𝔼 exp(gᵀ M g′) ≤ 1 + Tr M²` when `Tr M² ≤ ½`

Solution of `BosonicLearn.gaussian_bilinear_exp_bound`.

* `gauss_exp`: the moment generating function of the standard Gaussian on `ℝ^ι` (with integrability);
  integrating out `g′` gives `exp(½ ∑ⱼ ⟨cⱼ, g⟩²)`, `cⱼ` the columns of `M`.
* `gauss_one_dim`: `𝔼 exp(b ζ²/2) = (1 - b)^{-1/2}` for a standard real Gaussian `ζ`, `b < 1`.
* `gauss_sq_exp`: `𝔼 exp(½⟨d, g⟩²) = (1 - |d|²)^{-1/2}` for `|d|² < 1`, by linearizing the square with an
  auxiliary Gaussian `ζ` (`exp(s²/2) = 𝔼 exp(s ζ)`) and Fubini.
* `exp_sum_le`: Jensen for `exp` with weights of total mass `≤ 1`.
* `outer_bound`: with `tⱼ = |cⱼ|²`, `dⱼ = cⱼ/√(2tⱼ)` and weights `2tⱼ` (total mass `2T ≤ 1`), Jensen gives
  `exp(½ ∑ⱼ ⟨cⱼ, g⟩²) ≤ ∑ⱼ 2tⱼ exp(½⟨dⱼ, g⟩²) + (1 - 2T)`, whose expectation is at most
  `2T·(3/2) + 1 - 2T = 1 + T` (each `𝔼 exp(½⟨dⱼ, g⟩²) ≤ (1 - ½)^{-1/2} = √2 ≤ 3/2`).
-/

noncomputable section

/-- The complex Gaussian integral `∫ exp(a·z) dγ(z) = exp(a·a/2)` for the standard Gaussian. -/
private lemma gauss_cexp {ι : Type} [Fintype ι] (a : ι → ℂ) :
    ∫ z : EuclideanSpace ℝ ι, Complex.exp (∑ i, a i * (z i : ℂ))
      ∂(stdGaussian (EuclideanSpace ℝ ι)) = Complex.exp (∑ i, a i ^ 2 / 2) := by
  rw [← map_pi_eq_stdGaussian, integral_map (by fun_prop) (by fun_prop)]
  simp only [Complex.exp_sum]
  rw [integral_fintype_prod_eq_prod (f := fun i (x : ℝ) => Complex.exp (a i * (x : ℂ)))]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h := complexMGF_id_gaussianReal (μ := 0) (v := 1) (a i)
  simpa [complexMGF] using h

/-- The moment generating function of the standard Gaussian. -/
private lemma gauss_exp {ι : Type} [Fintype ι] (h : ι → ℝ) :
    Integrable (fun z : EuclideanSpace ℝ ι => Real.exp (∑ i, h i * z i))
      (stdGaussian (EuclideanSpace ℝ ι)) ∧
    ∫ z : EuclideanSpace ℝ ι, Real.exp (∑ i, h i * z i) ∂(stdGaussian (EuclideanSpace ℝ ι)) =
      Real.exp ((∑ i, h i ^ 2) / 2) := by
  have h1 := gauss_cexp (fun i => (h i : ℂ))
  have h2 : ∀ z : EuclideanSpace ℝ ι, Complex.exp (∑ i, (h i : ℂ) * (z i : ℂ)) =
      ((Real.exp (∑ i, h i * z i) : ℝ) : ℂ) := by
    intro z
    push_cast
    rfl
  have h3 : Complex.exp (∑ i, (h i : ℂ) ^ 2 / 2) = ((Real.exp ((∑ i, h i ^ 2) / 2) : ℝ) : ℂ) := by
    push_cast
    rw [Finset.sum_div]
  rw [integral_congr_ae (Filter.Eventually.of_forall h2), integral_complex_ofReal, h3] at h1
  have h4 := Complex.ofReal_injective h1
  refine ⟨?_, h4⟩
  by_contra hni
  rw [integral_undef hni] at h4
  exact (Real.exp_pos _).ne h4

/-- Fubini for non-negative functions with explicit inner integrals. -/
private lemma prod_integrable_of_nonneg {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν] (f : α × β → ℝ) (hf : Measurable f)
    (h0 : ∀ p, 0 ≤ f p) (g : α → ℝ) (h1 : ∀ x, Integrable (fun y => f (x, y)) ν)
    (h2 : ∀ x, ∫ y, f (x, y) ∂ν = g x) (hg : Integrable g μ) :
    Integrable f (μ.prod ν) ∧ ∫ p, f p ∂(μ.prod ν) = ∫ x, g x ∂μ := by
  have hint : Integrable f (μ.prod ν) := by
    rw [integrable_prod_iff hf.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall h1, ?_⟩
    have h3 : (fun x => ∫ y, ‖f (x, y)‖ ∂ν) = g := by
      funext x
      rw [← h2 x]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only [Real.norm_eq_abs, abs_of_nonneg (h0 (x, y))]
    rwa [h3]
  refine ⟨hint, ?_⟩
  rw [integral_prod f hint]
  exact integral_congr_ae (Filter.Eventually.of_forall h2)

/-- `(2π)^{-1/2} · (2π/(1-b))^{1/2} = (1-b)^{-1/2}`. -/
private lemma sqrt_scalar (b : ℝ) (hb : b < 1) :
    (Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (Real.pi / ((1 - b) / 2)) = (Real.sqrt (1 - b))⁻¹ := by
  have h1 : (0 : ℝ) < 1 - b := by linarith
  have h2 : Real.pi / ((1 - b) / 2) = (2 * Real.pi) * (1 - b)⁻¹ := by
    field_simp
  rw [h2, Real.sqrt_mul (x := 2 * Real.pi) (by positivity) (1 - b)⁻¹, Real.sqrt_inv, ← mul_assoc,
    inv_mul_cancel₀ (by positivity), one_mul]

/-- The one-dimensional Gaussian integral `𝔼 exp(b ζ²/2) = (1-b)^{-1/2}` for `b < 1`. -/
private lemma gauss_one_dim (b : ℝ) (hb : b < 1) :
    Integrable (fun x : ℝ => Real.exp (b * x ^ 2 / 2)) (gaussianReal 0 1) ∧
    ∫ x : ℝ, Real.exp (b * x ^ 2 / 2) ∂(gaussianReal 0 1) = (Real.sqrt (1 - b))⁻¹ := by
  have h1 : (0 : ℝ) < 1 - b := by linarith
  have key : ∫ x : ℝ, Real.exp (b * x ^ 2 / 2) ∂(gaussianReal 0 1) = (Real.sqrt (1 - b))⁻¹ := by
    rw [integral_gaussianReal_eq_integral_smul (by norm_num)]
    have e : ∀ x : ℝ, gaussianPDFReal 0 1 x • Real.exp (b * x ^ 2 / 2) =
        (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-((1 - b) / 2) * x ^ 2) := by
      intro x
      simp only [gaussianPDFReal, smul_eq_mul, NNReal.coe_one, mul_one, sub_zero]
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    simp_rw [e]
    rw [integral_const_mul, integral_gaussian, sqrt_scalar b hb]
  refine ⟨?_, key⟩
  by_contra hni
  rw [integral_undef hni] at key
  have : (0 : ℝ) < (Real.sqrt (1 - b))⁻¹ := by positivity
  linarith

/-- Jensen's inequality for `exp` with sub-probability weights (the missing mass sits at `0`). -/
private lemma exp_sum_le {ι : Type} [Fintype ι] (w y : ι → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hw1 : ∑ j, w j ≤ 1) :
    Real.exp (∑ j, w j * y j) ≤ ∑ j, w j * Real.exp (y j) + (1 - ∑ j, w j) := by
  have h := convexOn_exp.map_sum_le (t := (Finset.univ : Finset (Option ι)))
    (w := fun o => o.elim (1 - ∑ j, w j) w) (p := fun o => o.elim 0 y)
    (by
      intro o _
      cases o with
      | none => simpa using hw1
      | some j => simpa using hw j)
    (by simp [Fintype.sum_option])
    (by simp)
  simp only [Fintype.sum_option, Option.elim_none, Option.elim_some, smul_eq_mul, mul_zero,
    zero_add, Real.exp_zero, mul_one] at h
  linarith


/-- For a vector `d` with `|d|² < 1`: `𝔼 exp(⟨d, g⟩²/2) = (1 - |d|²)^{-1/2}` under the standard Gaussian. -/
private lemma gauss_sq_exp {ι : Type} [Fintype ι] (d : ι → ℝ) (hd : ∑ i, d i ^ 2 < 1) :
    Integrable (fun g : EuclideanSpace ℝ ι => Real.exp ((∑ i, d i * g i) ^ 2 / 2))
      (stdGaussian (EuclideanSpace ℝ ι)) ∧
    ∫ g : EuclideanSpace ℝ ι, Real.exp ((∑ i, d i * g i) ^ 2 / 2)
      ∂(stdGaussian (EuclideanSpace ℝ ι)) = (Real.sqrt (1 - ∑ i, d i ^ 2))⁻¹ := by
  let f : ℝ × EuclideanSpace ℝ ι → ℝ := fun p => Real.exp (∑ i, (p.1 * d i) * p.2 i)
  have hfm : Measurable f := by
    refine Real.measurable_exp.comp ?_
    refine Finset.measurable_sum _ fun i _ => ?_
    fun_prop
  obtain ⟨h1, h2⟩ := gauss_one_dim (∑ i, d i ^ 2) hd
  obtain ⟨hi, hv⟩ := prod_integrable_of_nonneg (gaussianReal 0 1)
    (stdGaussian (EuclideanSpace ℝ ι)) f hfm
    (fun p => (Real.exp_pos _).le) (fun x => Real.exp ((∑ i, d i ^ 2) * x ^ 2 / 2))
    (fun x => (gauss_exp (fun i => x * d i)).1)
    (fun x => by
      rw [(gauss_exp (fun i => x * d i)).2]
      congr 2
      simp only [mul_pow, ← Finset.mul_sum]
      ring)
    h1
  have hinner : ∀ g : EuclideanSpace ℝ ι, ∫ x : ℝ, f (x, g) ∂(gaussianReal 0 1) =
      Real.exp ((∑ i, d i * g i) ^ 2 / 2) := by
    intro g
    have h := congrFun (mgf_id_gaussianReal (μ := 0) (v := 1)) (∑ i, d i * g i)
    simp only [mgf, id, zero_mul, zero_add, NNReal.coe_one, one_mul] at h
    rw [← h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show Real.exp (∑ i, (x * d i) * g i) = _
    congr 1
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  refine ⟨?_, ?_⟩
  · have h := hi.swap.integral_prod_left
    simpa only [Function.comp, Prod.swap_prod_mk, hinner] using h
  · rw [← h2, ← hv, integral_prod_symm f hi]
    exact integral_congr_ae (Filter.Eventually.of_forall fun g => (hinner g).symm)


private lemma inv_sqrt_le (b : ℝ) (hb : b ≤ 1 / 2) : (Real.sqrt (1 - b))⁻¹ ≤ 3 / 2 := by
  have h1 : (2 : ℝ) / 3 ≤ Real.sqrt (1 - b) := Real.le_sqrt_of_sq_le (by nlinarith)
  calc (Real.sqrt (1 - b))⁻¹ ≤ ((2 : ℝ) / 3)⁻¹ := inv_anti₀ (by norm_num) h1
    _ = 3 / 2 := by norm_num

/-- `𝔼 exp(|Mᵀ g|²/2) ≤ 1 + ‖M‖_F²` when `‖M‖_F² ≤ 1/2`. -/
private lemma outer_bound {ι : Type} [Fintype ι] (M : Matrix ι ι ℝ)
    (hT : ∑ j, ∑ i, M i j ^ 2 ≤ 1 / 2) :
    Integrable (fun g : EuclideanSpace ℝ ι => Real.exp ((∑ j, (∑ i, g i * M i j) ^ 2) / 2))
      (stdGaussian (EuclideanSpace ℝ ι)) ∧
    ∫ g : EuclideanSpace ℝ ι, Real.exp ((∑ j, (∑ i, g i * M i j) ^ 2) / 2)
      ∂(stdGaussian (EuclideanSpace ℝ ι)) ≤ 1 + ∑ j, ∑ i, M i j ^ 2 := by
  set t : ι → ℝ := fun j => ∑ i, M i j ^ 2 with ht
  have ht0 : ∀ j, 0 ≤ t j := fun j => Finset.sum_nonneg fun i _ => sq_nonneg _
  have ht2 : ∀ j, 0 ≤ 2 * t j := fun j => by have := ht0 j; positivity
  let d : ι → ι → ℝ := fun j i => (Real.sqrt (2 * t j))⁻¹ * M i j
  have hd : ∀ j, ∑ i, d j i ^ 2 ≤ 1 / 2 := by
    intro j
    have e : ∑ i, d j i ^ 2 = ((Real.sqrt (2 * t j))⁻¹) ^ 2 * t j := by
      simp only [d, mul_pow, ← Finset.mul_sum, ht]
    rw [e, inv_pow, Real.sq_sqrt (ht2 j)]
    by_cases h : t j = 0
    · simp [h]
    · have : (2 * t j)⁻¹ * t j = 1 / 2 := by field_simp
      rw [this]
  let φ : ι → EuclideanSpace ℝ ι → ℝ := fun j g => Real.exp ((∑ i, d j i * g i) ^ 2 / 2)
  have hφ1 : ∀ j, Integrable (φ j) (stdGaussian (EuclideanSpace ℝ ι)) := fun j =>
    (gauss_sq_exp (d j) (lt_of_le_of_lt (hd j) (by norm_num))).1
  have hφ2 : ∀ j, ∫ g, φ j g ∂(stdGaussian (EuclideanSpace ℝ ι)) ≤ 3 / 2 := fun j => by
    show ∫ g : EuclideanSpace ℝ ι, Real.exp ((∑ i, d j i * g i) ^ 2 / 2)
      ∂(stdGaussian (EuclideanSpace ℝ ι)) ≤ 3 / 2
    rw [(gauss_sq_exp (d j) (lt_of_le_of_lt (hd j) (by norm_num))).2]
    exact inv_sqrt_le _ (hd j)
  have hpt : ∀ g : EuclideanSpace ℝ ι, Real.exp ((∑ j, (∑ i, g i * M i j) ^ 2) / 2) ≤
      ∑ j, (2 * t j) * φ j g + (1 - ∑ j, 2 * t j) := by
    intro g
    have e : (∑ j, (∑ i, g i * M i j) ^ 2) / 2 =
        ∑ j, (2 * t j) * ((∑ i, d j i * g i) ^ 2 / 2) := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases h : t j = 0
      · have hM : ∀ i, M i j = 0 := by
          intro i
          have h' := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (M i j))).mp h i
            (Finset.mem_univ i)
          exact pow_eq_zero_iff two_ne_zero |>.mp h'
        simp [hM, h]
      · have e2 : ∑ i, d j i * g i = (Real.sqrt (2 * t j))⁻¹ * ∑ i, g i * M i j := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by simp only [d]; ring
        rw [e2, mul_pow, inv_pow, Real.sq_sqrt (ht2 j)]
        field_simp
    rw [e]
    exact exp_sum_le (fun j => 2 * t j) _ ht2 (by rw [← Finset.mul_sum]; linarith)
  have hD : Integrable (fun g : EuclideanSpace ℝ ι => ∑ j, (2 * t j) * φ j g + (1 - ∑ j, 2 * t j))
      (stdGaussian (EuclideanSpace ℝ ι)) :=
    (integrable_finsetSum _ fun j _ => (hφ1 j).const_mul _).add (integrable_const _)
  have hmeas : Measurable (fun g : EuclideanSpace ℝ ι =>
      Real.exp ((∑ j, (∑ i, g i * M i j) ^ 2) / 2)) := by
    refine Real.measurable_exp.comp ?_
    refine Measurable.div_const ?_ 2
    refine Finset.measurable_sum _ fun j _ => ?_
    refine Measurable.pow_const ?_ 2
    refine Finset.measurable_sum _ fun i _ => ?_
    fun_prop
  have hint : Integrable (fun g : EuclideanSpace ℝ ι =>
      Real.exp ((∑ j, (∑ i, g i * M i j) ^ 2) / 2)) (stdGaussian (EuclideanSpace ℝ ι)) := by
    refine hD.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun g => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hpt g
  refine ⟨hint, ?_⟩
  calc ∫ g : EuclideanSpace ℝ ι, Real.exp ((∑ j, (∑ i, g i * M i j) ^ 2) / 2)
        ∂(stdGaussian (EuclideanSpace ℝ ι))
      ≤ ∫ g : EuclideanSpace ℝ ι, (∑ j, (2 * t j) * φ j g + (1 - ∑ j, 2 * t j))
        ∂(stdGaussian (EuclideanSpace ℝ ι)) := integral_mono hint hD hpt
    _ = ∑ j, (2 * t j) * ∫ g, φ j g ∂(stdGaussian (EuclideanSpace ℝ ι)) + (1 - ∑ j, 2 * t j) := by
        rw [integral_add (integrable_finsetSum _ fun j _ => (hφ1 j).const_mul _)
          (integrable_const _), integral_finsetSum _ fun j _ => (hφ1 j).const_mul _]
        simp only [integral_const_mul, integral_const, probReal_univ, one_smul]
    _ ≤ ∑ j, (2 * t j) * (3 / 2) + (1 - ∑ j, 2 * t j) := by
        gcongr with j _
        exact hφ2 j
    _ = 1 + ∑ j, t j := by
        simp only [← Finset.mul_sum, ← Finset.sum_mul]
        ring

theorem solution {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ)
    (hM : M.IsSymm) (hT : (M * M).trace ≤ 1 / 2) :
    Integrable (fun q : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι =>
        Real.exp (∑ i, ∑ j, q.1 i * M i j * q.2 j))
      ((stdGaussian (EuclideanSpace ℝ ι)).prod (stdGaussian (EuclideanSpace ℝ ι))) ∧
    ∫ q : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι, Real.exp (∑ i, ∑ j, q.1 i * M i j * q.2 j)
        ∂((stdGaussian (EuclideanSpace ℝ ι)).prod (stdGaussian (EuclideanSpace ℝ ι))) ≤
      1 + (M * M).trace := by
  have htr : (M * M).trace = ∑ j, ∑ i, M i j ^ 2 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [hM.apply i j]
    ring
  rw [htr] at hT ⊢
  obtain ⟨ho1, ho2⟩ := outer_bound M hT
  have hFm : Measurable (fun q : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι =>
      Real.exp (∑ i, ∑ j, q.1 i * M i j * q.2 j)) := by
    refine Real.measurable_exp.comp ?_
    refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
    fun_prop
  have hF : ∀ x z : EuclideanSpace ℝ ι, Real.exp (∑ i, ∑ j, x i * M i j * z j) =
      Real.exp (∑ j, (∑ i, x i * M i j) * z j) := by
    intro x z
    rw [Finset.sum_comm]
    simp only [Finset.sum_mul]
  obtain ⟨hi, hv⟩ := prod_integrable_of_nonneg (stdGaussian (EuclideanSpace ℝ ι))
    (stdGaussian (EuclideanSpace ℝ ι))
    (fun q : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι =>
      Real.exp (∑ i, ∑ j, q.1 i * M i j * q.2 j)) hFm
    (fun p => (Real.exp_pos _).le)
    (fun g => Real.exp ((∑ j, (∑ i, g i * M i j) ^ 2) / 2))
    (fun x => by
      simp only [hF]
      exact (gauss_exp (fun j => ∑ i, x i * M i j)).1)
    (fun x => by
      simp only [hF]
      exact (gauss_exp (fun j => ∑ i, x i * M i j)).2)
    ho1
  exact ⟨hi, hv ▸ ho2⟩

end
