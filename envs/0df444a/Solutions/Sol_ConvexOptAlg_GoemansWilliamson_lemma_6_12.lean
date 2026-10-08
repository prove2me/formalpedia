-- Prove2me | solution 1 for ConvexOptAlg.GoemansWilliamson.lemma_6_12
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T18:51:49.879404+00:00
-- url     : https://prove2.me/submissions/c72fa8c6-1441-4463-bc97-fefd2c0c3773

import Mathlib
import Definitions.Def_ConvexOptAlg_GoemansWilliamson_Defs



namespace ConvexOptAlg.GoemansWilliamson

open MeasureTheory ProbabilityTheory Real Set

lemma gw_radial : ∫ r in Ioi (0:ℝ), r * exp (-r^2/2) = 1 := by
  have h := integral_mul_cexp_neg_mul_sq (b := (1/2 : ℂ)) (by norm_num)
  have e : (fun r : ℝ => (r:ℂ) * Complex.exp (-(1/2:ℂ) * (r:ℂ)^2)) =
      fun r => ((r * exp (-r^2/2) : ℝ) : ℂ) := by
    ext r; push_cast; ring_nf
  rw [e, integral_complex_ofReal] at h
  norm_num at h
  exact_mod_cast h

lemma gw_angle (θ : ℝ) (h0 : 0 ≤ θ) (hπ : θ ≤ π) :
    ∫ φ in Ioo (-π) π, (if 0 ≤ cos φ ∧ 0 ≤ cos (φ - θ) then (1:ℝ) else 0) = π - θ := by
  have hpi := pi_pos
  have hae : ∀ᵐ φ ∂(volume.restrict (Ioo (-π) π)),
      (if 0 ≤ cos φ ∧ 0 ≤ cos (φ - θ) then (1:ℝ) else 0) =
        (Icc (θ - π/2) (π/2)).indicator 1 φ := by
    have h1 : ∀ᵐ φ ∂(volume : Measure ℝ), φ ∉ ({-(π/2)} : Set ℝ) :=
      (Set.countable_singleton (-(π/2))).ae_notMem volume
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [h1] with φ hne hφ
    simp only [mem_singleton_iff] at hne
    by_cases hc : θ - π/2 ≤ φ ∧ φ ≤ π/2
    · rw [indicator_of_mem (show φ ∈ Icc (θ - π/2) (π/2) from hc), if_pos]
      · simp
      constructor
      · apply cos_nonneg_of_mem_Icc; constructor <;> linarith [hc.1, hc.2]
      · apply cos_nonneg_of_mem_Icc; constructor <;> linarith [hc.1, hc.2]
    · rw [indicator_of_notMem (show φ ∉ Icc (θ - π/2) (π/2) from hc), if_neg]
      rintro ⟨c1, c2⟩
      apply hc
      have hφ1 : φ ≤ π/2 := by
        by_contra H; push_neg at H
        linarith [cos_neg_of_pi_div_two_lt_of_lt H (by linarith [hφ.2])]
      have hφ2 : -(π/2) < φ := by
        by_contra H; push_neg at H
        have H' : φ < -(π/2) := lt_of_le_of_ne H hne
        have := cos_neg_of_pi_div_two_lt_of_lt (x := -φ) (by linarith) (by linarith [hφ.1])
        rw [cos_neg] at this; linarith
      refine ⟨?_, hφ1⟩
      by_contra H; push_neg at H
      have := cos_neg_of_pi_div_two_lt_of_lt (x := θ - φ) (by linarith) (by linarith)
      rw [← cos_neg, neg_sub] at this; linarith
  rw [integral_congr_ae hae, integral_indicator measurableSet_Icc,
    Measure.restrict_restrict measurableSet_Icc]
  have : Icc (θ - π/2) (π/2) ∩ Ioo (-π) π = Icc (θ - π/2) (π/2) := by
    apply inter_eq_left.2; intro x hx; constructor <;> linarith [hx.1, hx.2]
  rw [this]
  simp only [Pi.one_apply, integral_const, smul_eq_mul, mul_one]
  rw [Measure.real, Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith)]
  ring

lemma gw_wedge_vol (ρ : ℝ) (h1 : -1 ≤ ρ) (h2 : ρ ≤ 1) :
    ∫ p : ℝ × ℝ, (2*π)⁻¹ * exp (-(p.1^2 + p.2^2)/2) *
      (if 0 ≤ p.1 ∧ 0 ≤ ρ * p.1 + √(1-ρ^2) * p.2 then (1:ℝ) else 0) =
      (π - arccos ρ) / (2*π) := by
  have hpi := pi_pos
  set θ := arccos ρ with hθ
  have hc : cos θ = ρ := cos_arccos h1 h2
  have hs : sin θ = √(1-ρ^2) := sin_arccos ρ
  rw [← integral_comp_polarCoord_symm]
  have hT : polarCoord.target = Ioi (0:ℝ) ×ˢ Ioo (-π) π := rfl
  rw [hT]
  have hcongr : ∀ p ∈ Ioi (0:ℝ) ×ˢ Ioo (-π) π,
      p.1 • ((2*π)⁻¹ * exp (-((polarCoord.symm p).1^2 + (polarCoord.symm p).2^2)/2) *
        (if 0 ≤ (polarCoord.symm p).1 ∧
          0 ≤ ρ * (polarCoord.symm p).1 + √(1-ρ^2) * (polarCoord.symm p).2 then (1:ℝ) else 0)) =
      (p.1 * exp (-p.1^2/2) * (2*π)⁻¹) *
        (if 0 ≤ cos p.2 ∧ 0 ≤ cos (p.2 - θ) then (1:ℝ) else 0) := by
    rintro ⟨r, φ⟩ ⟨hr, _⟩
    simp only [mem_Ioi] at hr
    have hsym : polarCoord.symm (r, φ) = (r * cos φ, r * sin φ) := rfl
    rw [hsym, smul_eq_mul]
    have e1 : (r * cos φ)^2 + (r * sin φ)^2 = r^2 := by
      have := sin_sq_add_cos_sq φ; nlinarith
    have e2 : ρ * (r * cos φ) + √(1-ρ^2) * (r * sin φ) = r * cos (φ - θ) := by
      rw [cos_sub, hc, hs]; ring
    simp only [e1, e2]
    have i1 : (0 ≤ r * cos φ) ↔ 0 ≤ cos φ := by
      constructor
      · intro h; by_contra H; push_neg at H; nlinarith [mul_neg_of_pos_of_neg hr H]
      · intro h; positivity
    have i2 : (0 ≤ r * cos (φ - θ)) ↔ 0 ≤ cos (φ - θ) := by
      constructor
      · intro h; by_contra H; push_neg at H; nlinarith [mul_neg_of_pos_of_neg hr H]
      · intro h; positivity
    simp only [i1, i2]
    ring
  rw [setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) hcongr]
  rw [Measure.volume_eq_prod, setIntegral_prod_mul (fun r => r * exp (-r^2/2) * (2*π)⁻¹)
    (fun φ => if 0 ≤ cos φ ∧ 0 ≤ cos (φ - θ) then (1:ℝ) else 0)]
  rw [integral_mul_const, gw_radial, gw_angle θ (arccos_nonneg ρ) (arccos_le_pi ρ)]
  field_simp


/-- quadrant indicator -/
noncomputable def gwF (a b : ℝ) : ℝ := if 0 ≤ a ∧ 0 ≤ b then 1 else 0

lemma gwF_measurable : Measurable (fun p : ℝ × ℝ => gwF p.1 p.2) := by
  unfold gwF
  refine Measurable.ite ?_ measurable_const measurable_const
  exact (measurableSet_le measurable_const measurable_fst).inter
    (measurableSet_le measurable_const measurable_snd)

lemma gw_wedge_gauss (ρ : ℝ) (h1 : -1 ≤ ρ) (h2 : ρ ≤ 1) :
    ∫ p : ℝ × ℝ, gwF p.1 (ρ * p.1 + √(1-ρ^2) * p.2)
      ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) = (π - arccos ρ) / (2*π) := by
  rw [← gw_wedge_vol ρ h1 h2]
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
    prod_withDensity (measurable_gaussianPDF 0 1) (measurable_gaussianPDF 0 1),
    integral_withDensity_eq_integral_toReal_smul
      (f := fun z : ℝ × ℝ => gaussianPDF 0 1 z.1 * gaussianPDF 0 1 z.2)
      (by have := measurable_gaussianPDF 0 1; fun_prop)
      (Filter.Eventually.of_forall (fun p => ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        ENNReal.ofReal_lt_top)),
    ← Measure.volume_eq_prod]
  congr 1
  ext p
  have hpi := pi_pos
  have key : ∀ x, gaussianPDFReal 0 1 x = (√(2*π))⁻¹ * exp (-x^2/2) := by
    intro x; simp [gaussianPDFReal]
  simp only [gaussianPDF, ENNReal.toReal_mul, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _),
    smul_eq_mul, gwF]
  rw [key, key]
  have hs : (√(2*π))⁻¹ * (√(2*π))⁻¹ = (2*π)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (by positivity)]
  have he : exp (-p.1^2/2) * exp (-p.2^2/2) = exp (-(p.1^2 + p.2^2)/2) := by
    rw [← Real.exp_add]; ring_nf
  calc (√(2*π))⁻¹ * exp (-p.1^2/2) * ((√(2*π))⁻¹ * exp (-p.2^2/2)) *
        (if 0 ≤ p.1 ∧ 0 ≤ ρ * p.1 + √(1-ρ^2) * p.2 then (1:ℝ) else 0)
      = ((√(2*π))⁻¹ * (√(2*π))⁻¹) * (exp (-p.1^2/2) * exp (-p.2^2/2)) *
        (if 0 ≤ p.1 ∧ 0 ≤ ρ * p.1 + √(1-ρ^2) * p.2 then (1:ℝ) else 0) := by ring
    _ = _ := by rw [hs, he]

lemma gw_std2_integral (ρ s : ℝ) :
    ∫ g : EuclideanSpace ℝ (Fin 2), gwF (g 0) (ρ * g 0 + s * g 1) ∂(stdGaussian _) =
      ∫ p : ℝ × ℝ, gwF p.1 (ρ * p.1 + s * p.2) ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  rw [← map_pi_eq_stdGaussian]
  rw [show (WithLp.toLp 2 : (Fin 2 → ℝ) → EuclideanSpace ℝ (Fin 2)) =
    MeasurableEquiv.toLp 2 (Fin 2 → ℝ) from rfl, integral_map_equiv]
  exact (measurePreserving_finTwoArrow (gaussianReal 0 1)).integral_comp'
    (fun p => gwF p.1 (ρ * p.1 + s * p.2))

noncomputable def gwT {n : ℕ} (i j : Fin n) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun ξ => WithLp.toLp 2 ![ξ i, ξ j]
      map_add' := by intro x y; ext k; fin_cases k <;> simp
      map_smul' := by intro c x; ext k; fin_cases k <;> simp }

noncomputable def gwM (ρ s : ℝ) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun g => WithLp.toLp 2 ![g 0, ρ * g 0 + s * g 1]
      map_add' := by intro x y; ext k; fin_cases k <;> simp <;> ring
      map_smul' := by intro c x; ext k; fin_cases k <;> simp <;> ring }

lemma gwT_apply {n : ℕ} (i j : Fin n) (ξ : EuclideanSpace ℝ (Fin n)) :
    gwT i j ξ = WithLp.toLp 2 ![ξ i, ξ j] := rfl

lemma gwM_apply (ρ s : ℝ) (g : EuclideanSpace ℝ (Fin 2)) :
    gwM ρ s g = WithLp.toLp 2 ![g 0, ρ * g 0 + s * g 1] := rfl

lemma gw_cov_ext {ν₁ ν₂ : Measure (EuclideanSpace ℝ (Fin 2))} [IsGaussian ν₁] [IsGaussian ν₂]
    (h : ∀ a b : Fin 2, cov[fun u => u a, fun u => u b; ν₁] = cov[fun u => u a, fun u => u b; ν₂]) :
    covarianceBilin ν₁ = covarianceBilin ν₂ := by
  rw [← ContinuousLinearMap.toBilinForm_inj]
  refine LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis fun a b ↦ ?_
  rw [ContinuousLinearMap.toBilinForm_apply, ContinuousLinearMap.toBilinForm_apply,
    covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
    covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id]
  have e : ∀ c : Fin 2, (fun u : EuclideanSpace ℝ (Fin 2) =>
      inner ℝ ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis c) u) = fun u => u c := by
    intro c; ext u; simp [PiLp.inner_apply]
  rw [e, e]
  exact h a b

lemma gw_law {n : ℕ} (Sig : Matrix (Fin n) (Fin n) ℝ) (hpsd : Sig.PosSemidef)
    (hdiag : ∀ i, Sig i i = 1) (i j : Fin n) (h1 : -1 ≤ Sig i j) (h2 : Sig i j ≤ 1) :
    (multivariateGaussian 0 Sig).map (gwT i j) =
      (stdGaussian (EuclideanSpace ℝ (Fin 2))).map (gwM (Sig i j) √(1 - Sig i j ^ 2)) := by
  set ρ := Sig i j with hρ
  set s := √(1 - ρ ^ 2) with hs
  have hss : s * s = 1 - ρ ^ 2 := Real.mul_self_sqrt (by nlinarith)
  have hsym : Sig j i = ρ := by
    have := hpsd.1.apply i j
    simpa using this
  apply IsGaussian.ext
  · simp only [id]
    rw [ContinuousLinearMap.integral_id_map IsGaussian.integrable_id,
      ContinuousLinearMap.integral_id_map IsGaussian.integrable_id,
      integral_id_multivariateGaussian, integral_id_stdGaussian, map_zero, map_zero]
  apply gw_cov_ext
  intro a b
  rw [covariance_map (by fun_prop) (by fun_prop) (by fun_prop),
    covariance_map (by fun_prop) (by fun_prop) (by fun_prop)]
  -- left side
  have L : ∀ c : Fin 2, (fun u : EuclideanSpace ℝ (Fin 2) => u c) ∘ gwT i j =
      fun ξ => ξ (![i, j] c) := by
    intro c; ext ξ; fin_cases c <;> rfl
  -- right side as inner products
  let m : Fin 2 → EuclideanSpace ℝ (Fin 2) := fun c => WithLp.toLp 2 (![![1, 0], ![ρ, s]] c)
  have R : ∀ c : Fin 2, (fun u : EuclideanSpace ℝ (Fin 2) => u c) ∘ gwM ρ s =
      fun g => inner ℝ (m c) g := by
    intro c; ext g; fin_cases c <;> simp [m, gwM_apply, PiLp.inner_apply, Fin.sum_univ_two] <;> ring
  rw [L, L, R, R, covariance_eval_multivariateGaussian hpsd,
    ← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id, covarianceBilin_stdGaussian,
    innerSL_apply_apply]
  fin_cases a <;> fin_cases b <;>
    simp [m, PiLp.inner_apply, Fin.sum_univ_two, hdiag, hsym, ← hρ, EuclideanSpace.real_norm_sq_eq] <;> nlinarith


lemma gw_entry_bound {n : ℕ} (Sig : Matrix (Fin n) (Fin n) ℝ) (hpsd : Sig.PosSemidef)
    (hdiag : ∀ i, Sig i i = 1) (i j : Fin n) : -1 ≤ Sig i j ∧ Sig i j ≤ 1 := by
  by_cases hij : i = j
  · subst hij; simp [hdiag]
  have hsym : Sig j i = Sig i j := by
    have := hpsd.1.apply i j
    simpa using this
  have key : ∀ c : ℝ, 0 ≤ 1 + 2 * c * Sig i j + c ^ 2 := by
    intro c
    have := hpsd.dotProduct_mulVec_nonneg (Pi.single i 1 + c • Pi.single j 1)
    simp [dotProduct_add, add_dotProduct, Matrix.mulVec_add, Matrix.mulVec_smul,
      Pi.single_apply, hij, Ne.symm hij, hdiag, hsym] at this
    nlinarith
  constructor
  · nlinarith [key 1]
  · nlinarith [key (-1)]

lemma gwF_measurable2 : Measurable (fun y : EuclideanSpace ℝ (Fin 2) => gwF (y 0) (y 1)) :=
  gwF_measurable.comp (Measurable.prodMk (by fun_prop) (by fun_prop))

lemma gw_quadrant {n : ℕ} (Sig : Matrix (Fin n) (Fin n) ℝ) (hpsd : Sig.PosSemidef)
    (hdiag : ∀ i, Sig i i = 1) (i j : Fin n) :
    ∫ ξ, gwF (ξ i) (ξ j) ∂(multivariateGaussian 0 Sig) = (π - arccos (Sig i j)) / (2 * π) := by
  obtain ⟨h1, h2⟩ := gw_entry_bound Sig hpsd hdiag i j
  have hm := gwF_measurable2
  calc ∫ ξ, gwF (ξ i) (ξ j) ∂(multivariateGaussian 0 Sig)
      = ∫ y, gwF (y 0) (y 1) ∂((multivariateGaussian 0 Sig).map (gwT i j)) := by
        rw [integral_map (gwT i j).measurable.aemeasurable hm.aestronglyMeasurable]; rfl
    _ = ∫ y, gwF (y 0) (y 1) ∂((stdGaussian (EuclideanSpace ℝ (Fin 2))).map
          (gwM (Sig i j) √(1 - Sig i j ^ 2))) := by rw [gw_law Sig hpsd hdiag i j h1 h2]
    _ = ∫ g : EuclideanSpace ℝ (Fin 2), gwF (g 0) (Sig i j * g 0 + √(1 - Sig i j ^ 2) * g 1)
          ∂(stdGaussian _) := by
        rw [integral_map (gwM _ _).measurable.aemeasurable hm.aestronglyMeasurable]; rfl
    _ = _ := by rw [gw_std2_integral, gw_wedge_gauss _ h1 h2]

lemma sgn_measurable : Measurable sgn := by
  unfold sgn
  exact Measurable.ite (measurableSet_le measurable_const measurable_id) measurable_const
    measurable_const

lemma gw_int_bdd {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {f : α → ℝ} (hf : Measurable f) (hb : ∀ x, |f x| ≤ 4) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable 4 (ae_of_all _ (by simpa [Real.norm_eq_abs] using hb))

lemma gwF_abs (a b : ℝ) : |gwF a b| ≤ 4 := by unfold gwF; split_ifs <;> norm_num

lemma sgn_mul_eq (a b : ℝ) : sgn a * sgn b = 4 * gwF a b - 2 * gwF a a - 2 * gwF b b + 1 := by
  unfold sgn gwF; split_ifs <;> simp_all <;> linarith

theorem lemma_6_12_core {n : ℕ} (Sig : Matrix (Fin n) (Fin n) ℝ) (hpsd : Sig.PosSemidef)
    (hdiag : ∀ i, Sig i i = 1) (i j : Fin n) :
    Integrable (fun ξ : EuclideanSpace ℝ (Fin n) => sgn (ξ i) * sgn (ξ j))
        (multivariateGaussian 0 Sig) ∧
      ∫ ξ, sgn (ξ i) * sgn (ξ j) ∂(multivariateGaussian 0 Sig) =
        2 / Real.pi * Real.arcsin (Sig i j) := by
  have mi : Measurable (fun ξ : EuclideanSpace ℝ (Fin n) => ξ i) := by fun_prop
  have mj : Measurable (fun ξ : EuclideanSpace ℝ (Fin n) => ξ j) := by fun_prop
  have mF : ∀ (f g : EuclideanSpace ℝ (Fin n) → ℝ), Measurable f → Measurable g →
      Integrable (fun ξ => gwF (f ξ) (g ξ)) (multivariateGaussian 0 Sig) := by
    intro f g hf hg
    exact gw_int_bdd (gwF_measurable.comp (hf.prodMk hg)) (fun x => gwF_abs _ _)
  constructor
  · exact gw_int_bdd ((sgn_measurable.comp mi).mul (sgn_measurable.comp mj))
      (fun x => by unfold sgn; split_ifs <;> norm_num)
  simp_rw [sgn_mul_eq]
  rw [integral_add, integral_sub, integral_sub, integral_const_mul, integral_const_mul,
    integral_const_mul, gw_quadrant Sig hpsd hdiag i j, gw_quadrant Sig hpsd hdiag i i,
    gw_quadrant Sig hpsd hdiag j j, hdiag, hdiag, arccos_one, arcsin_eq_pi_div_two_sub_arccos]
  · simp
    have := pi_pos
    field_simp
    ring
  all_goals first
    | exact integrable_const _
    | exact (mF _ _ mi mj).const_mul _
    | exact (mF _ _ mi mi).const_mul _
    | exact (mF _ _ mj mj).const_mul _
    | exact ((mF _ _ mi mj).const_mul _).sub ((mF _ _ mi mi).const_mul _)
    | exact (((mF _ _ mi mj).const_mul _).sub ((mF _ _ mi mi).const_mul _)).sub
        ((mF _ _ mj mj).const_mul _)

end ConvexOptAlg.GoemansWilliamson

open ConvexOptAlg.GoemansWilliamson
open MeasureTheory ProbabilityTheory

theorem solution {n : ℕ} (Sig : Matrix (Fin n) (Fin n) ℝ) (hpsd : Sig.PosSemidef)
    (hdiag : ∀ i, Sig i i = 1) (i j : Fin n) :
    Integrable (fun ξ : EuclideanSpace ℝ (Fin n) => sgn (ξ i) * sgn (ξ j))
        (multivariateGaussian 0 Sig) ∧
      ∫ ξ, sgn (ξ i) * sgn (ξ j) ∂(multivariateGaussian 0 Sig) =
        2 / Real.pi * Real.arcsin (Sig i j) := by
  exact lemma_6_12_core Sig hpsd hdiag i j
