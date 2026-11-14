-- Prove2me | solution 1 for BosonicLearn.gaussian_shift_overlap
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-13T21:28:28.88679+00:00
-- url     : https://prove2.me/submissions/d520f593-38c2-46bc-a2bc-2bb15e8aea16

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

noncomputable section

/-! ### Step 1: one dimension

For `a ≥ 0` the measures `N(0,1)` and `N(a,1)` have a common part
`κ₁ = N(a,1)|_{(-∞, a/2]} + N(0,1)|_{(a/2, ∞)}` of mass at least `1 - a/√(2π)`. -/

private lemma pdf_le_of_le {a x : ℝ} (ha : 0 ≤ a) (hx : x ≤ a / 2) :
    gaussianPDF a 1 x ≤ gaussianPDF 0 1 x := by
  unfold gaussianPDF gaussianPDFReal
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  simp only [NNReal.coe_one, mul_one, sub_zero]
  have : x ^ 2 ≤ (x - a) ^ 2 := by nlinarith
  linarith

private lemma pdf_le_of_ge {a x : ℝ} (ha : 0 ≤ a) (hx : a / 2 < x) :
    gaussianPDF 0 1 x ≤ gaussianPDF a 1 x := by
  unfold gaussianPDF gaussianPDFReal
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  simp only [NNReal.coe_one, mul_one, sub_zero]
  have : (x - a) ^ 2 ≤ x ^ 2 := by nlinarith
  linarith

private lemma pdf_le_const (x : ℝ) :
    gaussianPDF 0 1 x ≤ ENNReal.ofReal (Real.sqrt (2 * Real.pi))⁻¹ := by
  unfold gaussianPDF gaussianPDFReal
  apply ENNReal.ofReal_le_ofReal
  simp only [NNReal.coe_one, mul_one, sub_zero]
  have h1 : Real.exp (-x ^ 2 / 2) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have := sq_nonneg x
    linarith
  have h2 : (0 : ℝ) ≤ (Real.sqrt (2 * Real.pi))⁻¹ := by positivity
  nlinarith

/-- Comparison of two measures with densities on a set where the densities are ordered. -/
private lemma restrict_le_of_pdf (f g : ℝ → ℝ≥0∞) (s : Set ℝ) (hs : MeasurableSet s)
    (h : ∀ x ∈ s, f x ≤ g x) :
    ((volume : Measure ℝ).withDensity f).restrict s ≤
      ((volume : Measure ℝ).withDensity g).restrict s := by
  rw [restrict_withDensity hs, restrict_withDensity hs]
  exact withDensity_mono (ae_restrict_of_forall_mem hs h)

/-- One-dimensional overlap of `N(0,1)` and `N(a,1)`. -/
private lemma oneD_overlap (a : ℝ) (ha : 0 ≤ a) :
    ∃ κ : Measure ℝ, κ ≤ gaussianReal 0 1 ∧ κ ≤ gaussianReal a 1 ∧
      ENNReal.ofReal (1 - a / Real.sqrt (2 * Real.pi)) ≤ κ Set.univ := by
  have h1 : (1 : NNReal) ≠ 0 := one_ne_zero
  set c : ℝ := a / 2 with hc
  refine ⟨(gaussianReal a 1).restrict (Set.Iic c) + (gaussianReal 0 1).restrict (Set.Ioi c),
    ?_, ?_, ?_⟩
  · have hle : (gaussianReal a 1).restrict (Set.Iic c) ≤
        (gaussianReal 0 1).restrict (Set.Iic c) := by
      rw [gaussianReal_of_var_ne_zero _ h1, gaussianReal_of_var_ne_zero _ h1]
      exact restrict_le_of_pdf _ _ _ measurableSet_Iic (fun x hx => pdf_le_of_le ha hx)
    calc (gaussianReal a 1).restrict (Set.Iic c) + (gaussianReal 0 1).restrict (Set.Ioi c)
        ≤ (gaussianReal 0 1).restrict (Set.Iic c) + (gaussianReal 0 1).restrict (Set.Ioi c) :=
          add_le_add_left hle _
      _ = gaussianReal 0 1 := by
          rw [← Set.compl_Iic]
          exact Measure.restrict_add_restrict_compl measurableSet_Iic
  · have hle : (gaussianReal 0 1).restrict (Set.Ioi c) ≤
        (gaussianReal a 1).restrict (Set.Ioi c) := by
      rw [gaussianReal_of_var_ne_zero _ h1, gaussianReal_of_var_ne_zero _ h1]
      exact restrict_le_of_pdf _ _ _ measurableSet_Ioi (fun x hx => pdf_le_of_ge ha hx)
    calc (gaussianReal a 1).restrict (Set.Iic c) + (gaussianReal 0 1).restrict (Set.Ioi c)
        ≤ (gaussianReal a 1).restrict (Set.Iic c) + (gaussianReal a 1).restrict (Set.Ioi c) :=
          add_le_add_right hle _
      _ = gaussianReal a 1 := by
          rw [← Set.compl_Iic]
          exact Measure.restrict_add_restrict_compl measurableSet_Iic
  · rw [Measure.add_apply, Measure.restrict_apply MeasurableSet.univ,
      Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Set.univ_inter]
    -- `N(a,1) (-∞, a/2] = N(0,1) (-∞, -a/2]`
    have hshift : gaussianReal a 1 (Set.Iic c) = gaussianReal 0 1 (Set.Iic (-c)) := by
      have := gaussianReal_map_add_const (μ := 0) (v := 1) a
      rw [zero_add] at this
      rw [← this, Measure.map_apply (measurable_add_const a) measurableSet_Iic]
      congr 1
      ext x
      simp only [Set.mem_preimage, Set.mem_Iic, hc]
      constructor <;> intro h <;> linarith
    rw [hshift]
    -- the middle interval has mass at most `a / √(2π)`
    have hmid : gaussianReal 0 1 (Set.Ioc (-c) c) ≤
        ENNReal.ofReal (a / Real.sqrt (2 * Real.pi)) := by
      rw [gaussianReal_apply _ h1]
      calc ∫⁻ x in Set.Ioc (-c) c, gaussianPDF 0 1 x
          ≤ ∫⁻ x in Set.Ioc (-c) c, ENNReal.ofReal (Real.sqrt (2 * Real.pi))⁻¹ :=
            lintegral_mono (fun x => pdf_le_const x)
        _ = ENNReal.ofReal (Real.sqrt (2 * Real.pi))⁻¹ * ENNReal.ofReal (c - -c) := by
            rw [setLIntegral_const, Real.volume_Ioc]
        _ = ENNReal.ofReal (a / Real.sqrt (2 * Real.pi)) := by
            rw [← ENNReal.ofReal_mul (by positivity)]
            congr 1
            rw [hc]; ring
    have htot : gaussianReal 0 1 (Set.Iic (-c)) + gaussianReal 0 1 (Set.Ioc (-c) c)
        + gaussianReal 0 1 (Set.Ioi c) = 1 := by
      have hcc : -c ≤ c := by rw [hc]; linarith
      rw [← measure_union (Set.Iic_disjoint_Ioc le_rfl) measurableSet_Ioc,
        Set.Iic_union_Ioc_eq_Iic hcc, ← Set.compl_Iic,
        measure_add_measure_compl measurableSet_Iic, measure_univ]
    have : (1 : ℝ≥0∞) ≤ gaussianReal 0 1 (Set.Iic (-c)) + gaussianReal 0 1 (Set.Ioi c)
        + ENNReal.ofReal (a / Real.sqrt (2 * Real.pi)) := by
      rw [← htot]
      calc gaussianReal 0 1 (Set.Iic (-c)) + gaussianReal 0 1 (Set.Ioc (-c) c)
            + gaussianReal 0 1 (Set.Ioi c)
          = gaussianReal 0 1 (Set.Iic (-c)) + gaussianReal 0 1 (Set.Ioi c)
            + gaussianReal 0 1 (Set.Ioc (-c) c) := by ring
        _ ≤ _ := add_le_add_right hmid _
    rw [ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one]
    exact tsub_le_iff_right.mpr this

/-! ### Step 2a: a finite product measure is monotone in one factor -/

/-- Product of the masses of a box for a family of measures updated in one coordinate. -/
private lemma prod_update_meas {ι : Type} [Fintype ι] [DecidableEq ι]
    (ν : ι → Measure ℝ) (i₀ : ι) (ρ : Measure ℝ) (s : ι → Set ℝ) :
    ∏ i, (Function.update ν i₀ ρ i) (s i) =
      ρ (s i₀) * ∏ i ∈ Finset.univ.erase i₀, ν i (s i) := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i₀), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

private lemma finite_update {ι : Type} [DecidableEq ι]
    (ν : ι → Measure ℝ) [∀ i, IsFiniteMeasure (ν i)] (i₀ : ι) (ρ : Measure ℝ)
    [IsFiniteMeasure ρ] :
    ∀ i, IsFiniteMeasure (Function.update ν i₀ ρ i) := by
  intro i
  by_cases h : i = i₀
  · subst h; rw [Function.update_self]; infer_instance
  · rw [Function.update_of_ne h]; infer_instance

/-- Replacing one factor of a finite product of finite measures by a smaller measure gives a
smaller product measure. -/
private lemma pi_update_le {ι : Type} [Fintype ι] [DecidableEq ι]
    (ν : ι → Measure ℝ) [∀ i, IsFiniteMeasure (ν i)] (i₀ : ι) (ρ : Measure ℝ)
    (hρ : ρ ≤ ν i₀) :
    Measure.pi (Function.update ν i₀ ρ) ≤ Measure.pi ν := by
  have : IsFiniteMeasure ρ := isFiniteMeasure_of_le _ hρ
  have h1 := finite_update ν i₀ ρ
  have h2 := finite_update ν i₀ (ν i₀ - ρ)
  have hsum : ν i₀ - ρ + ρ = ν i₀ := Measure.sub_add_cancel_of_le hρ
  have key : Measure.pi ν =
      Measure.pi (Function.update ν i₀ (ν i₀ - ρ)) + Measure.pi (Function.update ν i₀ ρ) := by
    refine Measure.pi_eq fun s hs => ?_
    rw [Measure.add_apply, Measure.pi_pi, Measure.pi_pi, prod_update_meas, prod_update_meas,
      ← add_mul, ← Measure.add_apply, hsum,
      Finset.mul_prod_erase _ (fun i => ν i (s i)) (Finset.mem_univ i₀)]
  rw [key]
  exact Measure.le_add_left le_rfl

/-! ### Step 2b: the standard Gaussian and a shift of it -/

/-- Overlap of the standard Gaussian on `EuclideanSpace ℝ ι` with its translate by `h`. -/
private lemma std_shift_overlap {ι : Type} [Fintype ι] [DecidableEq ι] (h : EuclideanSpace ℝ ι) :
    ∃ κ : Measure (EuclideanSpace ℝ ι),
      κ ≤ stdGaussian (EuclideanSpace ℝ ι) ∧
      κ ≤ (stdGaussian (EuclideanSpace ℝ ι)).map (fun x => x + h) ∧
      ENNReal.ofReal (1 - ‖h‖ / Real.sqrt (2 * Real.pi)) ≤ κ Set.univ := by
  by_cases hh : h = 0
  · refine ⟨stdGaussian (EuclideanSpace ℝ ι), le_rfl, ?_, ?_⟩
    · subst hh
      simp
    · subst hh
      simp
  · have ha : 0 < ‖h‖ := norm_pos_iff.mpr hh
    set a : ℝ := ‖h‖ with ha_def
    have hne : Nonempty ι := by
      by_contra hι
      rw [not_nonempty_iff] at hι
      exact hh (Subsingleton.elim _ _)
    obtain ⟨i₀⟩ := hne
    -- unit vector in the direction of `h`, completed to an orthonormal basis
    set u : EuclideanSpace ℝ ι := a⁻¹ • h with hu_def
    have hu : ‖u‖ = 1 := by
      rw [hu_def, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha)]
      exact inv_mul_cancel₀ ha.ne'
    have hau : a • u = h := by
      rw [hu_def, smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
    have hv : Orthonormal ℝ (Set.domRestrict ({i₀} : Set ι) (fun _ => u)) := by
      rw [orthonormal_iff_ite]
      rintro ⟨i, hi⟩ ⟨j, hj⟩
      have hi' : i = i₀ := hi
      have hj' : j = i₀ := hj
      subst hi' hj'
      simp [hu]
    obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq
      (finrank_euclideanSpace (𝕜 := ℝ) (ι := ι))
    have hb0 : b i₀ = u := hb i₀ rfl
    set Φ : (ι → ℝ) → EuclideanSpace ℝ ι := fun x => ∑ i, x i • b i with hΦ_def
    have hΦ : Measurable Φ := by fun_prop
    have hstd : stdGaussian (EuclideanSpace ℝ ι) =
        (Measure.pi fun _ : ι => gaussianReal 0 1).map Φ :=
      stdGaussian_eq_map_pi_orthonormalBasis b
    set G : ι → Measure ℝ := fun _ => gaussianReal 0 1 with hG
    set c : ι → ℝ := Pi.single i₀ a with hc
    set G' : ι → Measure ℝ := fun i => gaussianReal (c i) 1 with hG'
    -- the shifted standard Gaussian is the image of a product with one shifted factor
    have hshift : (stdGaussian (EuclideanSpace ℝ ι)).map (fun x => x + h) =
        (Measure.pi G').map Φ := by
      have h1 : (Measure.pi G).map (fun x i => x i + c i) = Measure.pi G' := by
        rw [Measure.pi_map_pi (μ := G) (f := fun i x => x + c i)
          (fun i => (measurable_add_const _).aemeasurable)]
        congr 1
        funext i
        rw [hG, hG']
        simp only
        rw [gaussianReal_map_add_const, zero_add]
      have h2 : (fun x => x + h) ∘ Φ = Φ ∘ (fun x i => x i + c i) := by
        funext x
        simp only [Function.comp_apply, hΦ_def, add_smul, Finset.sum_add_distrib]
        congr 1
        rw [hc, ← hau, ← hb0]
        simp [Pi.single_apply, ite_smul]
      rw [hstd, Measure.map_map (measurable_add_const h) hΦ, h2, ← h1,
        Measure.map_map hΦ (by fun_prop)]
    obtain ⟨κ₁, hκ0, hκa, hmass⟩ := oneD_overlap a ha.le
    have : IsFiniteMeasure κ₁ := isFiniteMeasure_of_le _ hκ0
    refine ⟨(Measure.pi (Function.update G i₀ κ₁)).map Φ, ?_, ?_, ?_⟩
    · rw [hstd]
      exact Measure.map_mono (pi_update_le G i₀ κ₁ hκ0) hΦ
    · rw [hshift]
      have hupd : Function.update G i₀ κ₁ = Function.update G' i₀ κ₁ := by
        funext i
        by_cases hi : i = i₀
        · subst hi; simp
        · simp [hG, hG', hc, Pi.single_apply, hi]
      rw [hupd]
      refine Measure.map_mono (pi_update_le G' i₀ κ₁ ?_) hΦ
      simpa [hG', hc] using hκa
    · have := finite_update G i₀ κ₁
      rw [Measure.map_apply hΦ MeasurableSet.univ, Set.preimage_univ, Measure.pi_univ,
        prod_update_meas]
      simpa [hG] using hmass

/-! ### Step 3: general covariance -/

open scoped MatrixOrder in
private lemma sqrt_facts {ι : Type} [Fintype ι] [DecidableEq ι]
    (T : Matrix ι ι ℝ) (hT : T.PosSemidef) (w : ι → ℝ) :
    (CFC.sqrt T) *ᵥ ((CFC.sqrt T) *ᵥ w) = T *ᵥ w ∧
    ((CFC.sqrt T) *ᵥ w) ⬝ᵥ ((CFC.sqrt T) *ᵥ w) = w ⬝ᵥ (T *ᵥ w) := by
  have hmul : CFC.sqrt T * CFC.sqrt T = T := CFC.sqrt_mul_sqrt_self _ hT.nonneg
  have hpsd : (CFC.sqrt T).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg T)
  have hsym : (CFC.sqrt T)ᵀ = CFC.sqrt T := by
    have := hpsd.isHermitian.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have h1 : (CFC.sqrt T) *ᵥ ((CFC.sqrt T) *ᵥ w) = T *ᵥ w := by
    rw [Matrix.mulVec_mulVec, hmul]
  refine ⟨h1, ?_⟩
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsym, h1, dotProduct_comm]

open scoped MatrixOrder in
/-- The two Gaussians as images of the standard Gaussian and of a translate of it under the
same affine map `x ↦ μ + R x`, with `‖h‖ = √(wᵀ T w)`. -/
private lemma mvg_facts {ι : Type} [Fintype ι] [DecidableEq ι] (μ : EuclideanSpace ℝ ι)
    (T : Matrix ι ι ℝ) (hT : T.PosSemidef) (w : ι → ℝ) :
    ∃ (R : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) (h : EuclideanSpace ℝ ι),
      multivariateGaussian μ T = (stdGaussian (EuclideanSpace ℝ ι)).map (fun x => μ + R x) ∧
      multivariateGaussian (μ + WithLp.toLp 2 (T *ᵥ w)) T =
        ((stdGaussian (EuclideanSpace ℝ ι)).map (fun x => x + h)).map (fun x => μ + R x) ∧
      ‖h‖ = Real.sqrt (w ⬝ᵥ (T *ᵥ w)) := by
  obtain ⟨hRR, hnorm⟩ := sqrt_facts T hT w
  refine ⟨Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt T), WithLp.toLp 2 ((CFC.sqrt T) *ᵥ w),
    rfl, ?_, ?_⟩
  · have hf : Measurable (fun x : EuclideanSpace ℝ ι =>
        μ + Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt T) x) := by fun_prop
    rw [Measure.map_map hf (measurable_add_const _)]
    unfold multivariateGaussian
    congr 1
    funext x
    simp only [Function.comp_apply, map_add, Matrix.toEuclideanCLM_toLp, hRR]
    abel
  · rw [← hnorm, EuclideanSpace.norm_eq]
    congr 1
    simp [dotProduct, sq]

theorem solution {ι : Type} [Fintype ι] [DecidableEq ι] (μ : EuclideanSpace ℝ ι)
    (T : Matrix ι ι ℝ) (hT : T.PosSemidef) (w : ι → ℝ) :
    ∃ κ : Measure (EuclideanSpace ℝ ι),
      κ ≤ multivariateGaussian μ T ∧
      κ ≤ multivariateGaussian (μ + WithLp.toLp 2 (T *ᵥ w)) T ∧
      1 - Real.sqrt (w ⬝ᵥ (T *ᵥ w)) / Real.sqrt (2 * Real.pi) ≤ (κ Set.univ).toReal := by
  obtain ⟨R, h, hG0, hG1, hnorm⟩ := mvg_facts μ T hT w
  have hf : Measurable (fun x : EuclideanSpace ℝ ι => μ + R x) := by fun_prop
  obtain ⟨κ, hκ0, hκ1, hmass⟩ := std_shift_overlap h
  refine ⟨κ.map (fun x => μ + R x), ?_, ?_, ?_⟩
  · rw [hG0]
    exact Measure.map_mono hκ0 hf
  · rw [hG1]
    exact Measure.map_mono hκ1 hf
  · have hfin : (κ.map (fun x => μ + R x)) Set.univ ≠ ⊤ := by
      have hle : (κ.map (fun x => μ + R x)) Set.univ ≤ multivariateGaussian μ T Set.univ := by
        rw [hG0]
        exact Measure.map_mono hκ0 hf Set.univ
      exact ne_top_of_le_ne_top (measure_ne_top _ _) hle
    rw [← ENNReal.ofReal_le_iff_le_toReal hfin, Measure.map_apply hf MeasurableSet.univ,
      Set.preimage_univ, ← hnorm]
    exact hmass
