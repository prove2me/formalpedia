-- Prove2me | solution 1 for ChanceStateCtrl.General.eq_14_spherical_radial
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-25T01:35:28.320935+00:00
-- url     : https://prove2.me/submissions/c03ca744-9fda-4b67-8d09-e1c58fcc86b9

import Mathlib
import Definitions.Def_ChanceStateCtrl_General_Setting
import Definitions.Def_ChanceStateCtrl_General_Radial
open MeasureTheory ProbabilityTheory Filter Topology
open scoped MatrixOrder Pointwise

open ChanceStateCtrl.General

/-- The product of standard Gaussians has the product density. -/
lemma pi_gaussian_eq_withDensity (m : ℕ) :
    Measure.pi (fun _ : Fin m => gaussianReal 0 1) =
      (volume : Measure (Fin m → ℝ)).withDensity
        (fun x => ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (x i))) := by
  refine Measure.pi_eq fun s hs => ?_
  have hbox : MeasurableSet (Set.pi Set.univ s) := MeasurableSet.univ_pi hs
  rw [withDensity_apply _ hbox, ← lintegral_indicator hbox]
  set ψ : Fin m → ℝ → ℝ := fun i => (s i).indicator (gaussianPDFReal 0 1) with hψ
  have hpt : (Set.pi Set.univ s).indicator
      (fun x : Fin m → ℝ => ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (x i))) =
      fun x => ENNReal.ofReal (∏ i, ψ i (x i)) := by
    funext x
    by_cases hx : x ∈ Set.pi Set.univ s
    · rw [Set.indicator_of_mem hx]
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hψ]; simp only; rw [Set.indicator_of_mem (hx i (Set.mem_univ i))]
    · rw [Set.indicator_of_notMem hx]
      simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hx
      obtain ⟨i, hi⟩ := hx
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hψ, hi]), ENNReal.ofReal_zero]
  rw [hpt]
  have hψint : ∀ i, Integrable (ψ i) volume := fun i =>
    (integrable_gaussianPDFReal 0 1).indicator (hs i)
  have hψnn : ∀ i y, 0 ≤ ψ i y := fun i y =>
    Set.indicator_nonneg (fun y _ => gaussianPDFReal_nonneg 0 1 y) y
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [volume_pi, integral_fintype_prod_eq_prod, ENNReal.ofReal_prod_of_nonneg]
    · refine Finset.prod_congr rfl fun i _ => ?_
      rw [gaussianReal_apply_eq_integral 0 one_ne_zero, hψ, integral_indicator (hs i)]
    · exact fun i _ => integral_nonneg (hψnn i)
  · rw [volume_pi]; exact Integrable.fintype_prod hψint
  · exact Filter.Eventually.of_forall fun x => Finset.prod_nonneg fun i _ => hψnn i (x i)

/-- Pushing a measure with density forward along a measurable equivalence. -/
lemma map_withDensity_equiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (e : α ≃ᵐ β) (f : α → ENNReal) (hf : Measurable f) :
    (μ.withDensity f).map e = (μ.map e).withDensity (f ∘ e.symm) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs, setLIntegral_map hs (hf.comp e.symm.measurable) e.measurable]
  simp


/-- Polar coordinates for the Lebesgue integral on `ℝᵐ`. -/
lemma lintegral_polar {m : ℕ} (hm : 0 < m) (H : EuclideanSpace ℝ (Fin m) → ENNReal)
    (hH : Measurable H) :
    ∫⁻ x, H x ∂(volume : Measure (EuclideanSpace ℝ (Fin m))) =
      ∫⁻ v, (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (r ^ (m - 1)) *
        H (r • (v : EuclideanSpace ℝ (Fin m)))) ∂(volume : Measure (EuclideanSpace ℝ (Fin m))).toSphere := by
  haveI : Nontrivial (EuclideanSpace ℝ (Fin m)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; exact hm)
  have hmp := (volume : Measure (EuclideanSpace ℝ (Fin m))).measurePreserving_homeomorphUnitSphereProd
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) = m := finrank_euclideanSpace_fin
  have hL : ∫⁻ x : ({0}ᶜ : Set (EuclideanSpace ℝ (Fin m))), H x
      ∂((volume : Measure (EuclideanSpace ℝ (Fin m))).comap Subtype.val) =
      ∫⁻ x, H x ∂(volume : Measure (EuclideanSpace ℝ (Fin m))) := by
    rw [lintegral_subtype_comap (measurableSet_singleton (0 : EuclideanSpace ℝ (Fin m))).compl,
      restrict_compl_singleton]
  rw [← hL]
  have h1 := hmp.lintegral_comp_emb (homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin m))).measurableEmbedding (fun p => H ((homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin m))).symm p))
  simp only [Homeomorph.symm_apply_apply] at h1
  rw [h1]
  have hm : Measurable fun p : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 × Set.Ioi (0 : ℝ) => H ((homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin m))).symm p) :=
    hH.comp (continuous_subtype_val.comp (homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin m))).symm.continuous).measurable
  rw [lintegral_prod _ hm.aemeasurable]
  refine lintegral_congr fun v => ?_
  rw [Measure.volumeIoiPow, lintegral_withDensity_eq_lintegral_mul _ (by fun_prop)
    (g := fun y => H ((homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin m))).symm (v, y)))
    (hm.comp measurable_prodMk_left)]
  rw [hdim]
  have := lintegral_subtype_comap (μ := (volume : Measure ℝ)) (measurableSet_Ioi (a := (0:ℝ)))
    (fun r : ℝ => ENNReal.ofReal (r ^ (m - 1)) * H (r • (v : EuclideanSpace ℝ (Fin m))))
  simp only [Pi.mul_apply] at this ⊢
  rw [← this]
  rfl

/-- The standard Gaussian on `ℝᵐ` has the radial density `(2π)^{-m/2} e^{-‖x‖²/2}`. -/
lemma stdGaussian_eq_withDensity_radial (m : ℕ) :
    stdGaussian (EuclideanSpace ℝ (Fin m)) =
      (volume : Measure (EuclideanSpace ℝ (Fin m))).withDensity
        (fun x => ENNReal.ofReal (((√(2 * Real.pi))⁻¹) ^ m * Real.exp (-‖x‖ ^ 2 / 2))) := by
  rw [← map_pi_eq_stdGaussian, pi_gaussian_eq_withDensity]
  have hF : Measurable (fun x : Fin m → ℝ => ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (x i))) :=
    ENNReal.measurable_ofReal.comp
      (Finset.measurable_prod _ fun i _ => (measurable_gaussianPDFReal 0 1).comp
        (measurable_pi_apply i))
  have he : (WithLp.toLp 2 : (Fin m → ℝ) → EuclideanSpace ℝ (Fin m)) =
      ⇑(MeasurableEquiv.toLp 2 (Fin m → ℝ)) := rfl
  have hv : (volume : Measure (Fin m → ℝ)).map (MeasurableEquiv.toLp 2 (Fin m → ℝ)) = volume :=
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin m)).symm.map_eq
  rw [he, map_withDensity_equiv _ _ _ hF, hv]
  congr 1
  funext x
  simp only [Function.comp]
  congr 1
  simp only [gaussianPDFReal, sub_zero, NNReal.coe_one, mul_one, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← Real.exp_sum]
  congr 2
  have hn := EuclideanSpace.real_norm_sq_eq (x : EuclideanSpace ℝ (Fin m))
  rw [hn, neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [neg_div]; rfl

/-- The radial profile `J_D(v) = ∫_0^∞ 1_D(r v) r^{m-1} e^{-r²/2} dr`. -/
noncomputable def radJ {m : ℕ} (D : Set (EuclideanSpace ℝ (Fin m)))
    (v : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1) : ENNReal :=
  ∫⁻ r in Set.Ioi (0 : ℝ), D.indicator 1 (r • (v : EuclideanSpace ℝ (Fin m))) *
    ENNReal.ofReal (r ^ (m - 1) * Real.exp (-r ^ 2 / 2))

lemma stdGaussian_polar {m : ℕ} (hm : 0 < m) (D : Set (EuclideanSpace ℝ (Fin m)))
    (hD : MeasurableSet D) :
    stdGaussian (EuclideanSpace ℝ (Fin m)) D =
      ENNReal.ofReal (((√(2 * Real.pi))⁻¹) ^ m) *
        ∫⁻ v, radJ D v ∂(volume : Measure (EuclideanSpace ℝ (Fin m))).toSphere := by
  set c0 : ℝ := ((√(2 * Real.pi))⁻¹) ^ m with hc0
  set ρ : EuclideanSpace ℝ (Fin m) → ENNReal :=
    fun x => ENNReal.ofReal (c0 * Real.exp (-‖x‖ ^ 2 / 2)) with hρ
  have hρm : Measurable ρ := by
    simp only [hρ]
    fun_prop
  rw [stdGaussian_eq_withDensity_radial, withDensity_apply _ hD, ← lintegral_indicator hD,
    lintegral_polar hm _ (hρm.indicator hD), ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun v => ?_
  rw [radJ, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
  have hnorm : ‖r • (v : EuclideanSpace ℝ (Fin m))‖ = r := by
    rw [norm_smul, Real.norm_of_nonneg (le_of_lt hr), norm_eq_of_mem_sphere v, mul_one]
  have hc0nn : 0 ≤ c0 := by positivity
  by_cases hx : r • (v : EuclideanSpace ℝ (Fin m)) ∈ D
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    simp only [hρ, hnorm, Pi.one_apply, one_mul]
    rw [ENNReal.ofReal_mul hc0nn, ENNReal.ofReal_mul (pow_nonneg (le_of_lt hr) _)]
    ring
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
    simp

set_option maxHeartbeats 1000000 in
theorem solution {Ω U : Type*} [MeasurableSpace Ω] [NormedAddCommGroup U] [NormedSpace ℝ U] {m : ℕ}
    (P : Measure Ω) (ξ : Ω → EuclideanSpace ℝ (Fin m)) (Sigma : Matrix (Fin m) (Fin m) ℝ)
    (g : U → EuclideanSpace ℝ (Fin m) → ℝ) (hA : Assumption21 P ξ Sigma g) :
    ∀ u : U, probFn P ξ g u = ∫ v, radialProb Sigma g u v ∂(sphereLaw m) := by
  classical
  intro u
  haveI := hA.isProb
  have hm := hA.dim_pos
  set σ := (volume : Measure (EuclideanSpace ℝ (Fin m))).toSphere with hσ
  set c0 : ℝ := ((√(2 * Real.pi))⁻¹) ^ m with hc0
  have hgu : Continuous (g u) :=
    hA.locLip.continuous.comp (Continuous.prodMk continuous_const continuous_id)
  set D' : Set (EuclideanSpace ℝ (Fin m)) := {z | g u z ≤ 0} with hD'
  have hD'm : MeasurableSet D' := (isClosed_le hgu continuous_const).measurableSet
  set D : Set (EuclideanSpace ℝ (Fin m)) := (sqrtCov Sigma) ⁻¹' D' with hD
  have hDm : MeasurableSet D := (sqrtCov Sigma).continuous.measurable hD'm
  -- `φ(u) = γ(D)` for the standard Gaussian `γ`
  have h1 : P {ω | g u (ξ ω) ≤ 0} = stdGaussian (EuclideanSpace ℝ (Fin m)) D := by
    have e1 : {ω | g u (ξ ω) ≤ 0} = ξ ⁻¹' D' := rfl
    rw [e1, ← Measure.map_apply hA.measurable_xi hD'm, hA.law, multivariateGaussian,
      Measure.map_apply (by fun_prop) hD'm]
    congr 1
    ext x
    simp [hD, sqrtCov]
  -- normalization
  have hnorm := stdGaussian_polar hm Set.univ MeasurableSet.univ
  rw [measure_univ] at hnorm
  set I : ENNReal := ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (r ^ (m - 1) * Real.exp (-r ^ 2 / 2))
    with hI
  have hJuniv : ∀ v, radJ (Set.univ : Set (EuclideanSpace ℝ (Fin m))) v = I := by
    intro v; simp [radJ, hI]
  simp only [hJuniv, lintegral_const] at hnorm
  have hσ0 : σ Set.univ ≠ 0 := by
    intro h
    have := (Measure.toSphere_eq_zero_iff_finrank (μ := (volume : Measure (EuclideanSpace ℝ (Fin m))))).1
      (Measure.measure_univ_eq_zero.1 h)
    rw [finrank_euclideanSpace_fin] at this
    exact hm.ne' this
  have hσtop : σ Set.univ ≠ ⊤ := measure_ne_top _ _
  have hc0pos : 0 < c0 := by positivity
  have hI0 : I ≠ 0 := by
    intro h; rw [h, zero_mul, mul_zero] at hnorm; exact zero_ne_one hnorm.symm
  have hItop : I ≠ ⊤ := by
    intro h
    rw [h, ENNReal.top_mul hσ0, ENNReal.mul_top (ENNReal.ofReal_pos.2 hc0pos).ne'] at hnorm
    exact ENNReal.top_ne_one hnorm.symm
  have hc0eq : ENNReal.ofReal c0 = I⁻¹ * (σ Set.univ)⁻¹ := by
    rw [← ENNReal.mul_inv (Or.inl hI0) (Or.inl hItop)]
    exact ENNReal.eq_inv_of_mul_eq_one_left hnorm.symm
  -- the chi normalizing constant
  have hint : IntegrableOn (fun r : ℝ => r ^ (m - 1) * Real.exp (-r ^ 2 / 2)) (Set.Ioi 0) := by
    have h1 : IntegrableOn (fun x : ℝ => x ^ ((m - 1 : ℕ) : ℝ) * Real.exp (-(1 / 2) * x ^ 2))
        (Set.Ioi 0) :=
      integrableOn_rpow_mul_exp_neg_mul_sq (by norm_num) (by
        have : (0 : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
        linarith)
    refine IntegrableOn.congr_fun h1 (fun x hx => ?_) measurableSet_Ioi
    rw [Real.rpow_natCast]
    congr 2; ring
  have hIreal : ENNReal.ofReal (∫ r in Set.Ioi (0 : ℝ), r ^ (m - 1) * Real.exp (-r ^ 2 / 2)) = I :=
    ofReal_integral_eq_lintegral_ofReal hint
      (ae_restrict_of_forall_mem measurableSet_Ioi fun r hr =>
        mul_nonneg (pow_nonneg (le_of_lt hr) _) (Real.exp_pos _).le)
  set Ir : ℝ := ∫ r in Set.Ioi (0 : ℝ), r ^ (m - 1) * Real.exp (-r ^ 2 / 2) with hIr
  have hIrpos : 0 < Ir := by
    by_contra hle
    push_neg at hle
    rw [ENNReal.ofReal_of_nonpos hle] at hIreal
    exact hI0 hIreal.symm
  have hchiConst : ENNReal.ofReal (chiConst m) = I⁻¹ := by
    rw [chiConst, ← hIr, ENNReal.ofReal_inv_of_pos hIrpos, hIreal]
  have hchiConst_nn : 0 ≤ chiConst m := by
    rw [chiConst]; exact inv_nonneg.2 hIrpos.le
  -- each radial probability in terms of `radJ`
  have hchi : ∀ v : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
      chiLaw m {r : ℝ | 0 ≤ r ∧ g u (r • sqrtCov Sigma (v : EuclideanSpace ℝ (Fin m))) ≤ 0} =
        I⁻¹ * radJ D v := by
    intro v
    have hS : MeasurableSet {r : ℝ | 0 ≤ r ∧ g u (r • sqrtCov Sigma (v : EuclideanSpace ℝ (Fin m))) ≤ 0} :=
      (IsClosed.inter (isClosed_le continuous_const continuous_id)
        (isClosed_le (hgu.comp (continuous_id.smul continuous_const)) continuous_const)).measurableSet
    rw [chiLaw, withDensity_apply _ hS, ← lintegral_indicator hS, ← hchiConst, radJ,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← setLIntegral_congr (Ioi_ae_eq_Ici (a := (0 : ℝ))).symm, ← lintegral_indicator measurableSet_Ici]
    refine lintegral_congr fun r => ?_
    by_cases hr : 0 ≤ r
    · rw [Set.indicator_of_mem (Set.mem_Ici.2 hr)]
      have hmem : r ∈ {r : ℝ | 0 ≤ r ∧ g u (r • sqrtCov Sigma (v : EuclideanSpace ℝ (Fin m))) ≤ 0} ↔
          r • (v : EuclideanSpace ℝ (Fin m)) ∈ D := by
        simp only [Set.mem_setOf_eq, hD, Set.mem_preimage, hD', map_smul, and_iff_right hr]
      by_cases hx : r • (v : EuclideanSpace ℝ (Fin m)) ∈ D
      · rw [Set.indicator_of_mem (hmem.2 hx), Set.indicator_of_mem hx]
        simp only [chiDensity, if_pos hr, Pi.one_apply, one_mul]
        rw [mul_assoc, ENNReal.ofReal_mul hchiConst_nn]
      · rw [Set.indicator_of_notMem (fun h => hx (hmem.1 h)), Set.indicator_of_notMem hx]
        simp
    · rw [Set.indicator_of_notMem (fun h => hr (Set.mem_Ici.1 h)),
        Set.indicator_of_notMem (fun h => hr h.1)]
  -- measurability and finiteness
  have hmeas : Measurable fun v : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
      chiLaw m {r : ℝ | 0 ≤ r ∧ g u (r • sqrtCov Sigma (v : EuclideanSpace ℝ (Fin m))) ≤ 0} := by
    set S : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 × ℝ) :=
      {q | 0 ≤ q.2 ∧ g u (q.2 • sqrtCov Sigma (q.1 : EuclideanSpace ℝ (Fin m))) ≤ 0} with hSdef
    have hS : MeasurableSet S := by
      apply IsClosed.measurableSet
      apply IsClosed.inter (isClosed_le continuous_const continuous_snd)
      exact isClosed_le (hgu.comp (continuous_snd.smul
        ((sqrtCov Sigma).continuous.comp (continuous_subtype_val.comp continuous_fst)))) continuous_const
    haveI : SFinite (chiLaw m) := by unfold chiLaw; infer_instance
    exact measurable_measure_prodMk_left (ν := chiLaw m) hS
  have hJle : ∀ v, radJ D v ≤ I := by
    intro v
    refine lintegral_mono fun r => ?_
    by_cases hx : r • (v : EuclideanSpace ℝ (Fin m)) ∈ D
    · rw [Set.indicator_of_mem hx]; simp
    · rw [Set.indicator_of_notMem hx]; simp
  have hfin : ∀ v : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
      chiLaw m {r : ℝ | 0 ≤ r ∧ g u (r • sqrtCov Sigma (v : EuclideanSpace ℝ (Fin m))) ≤ 0} < ⊤ := by
    intro v
    rw [hchi v]
    exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (pos_iff_ne_zero.2 hI0))
      (lt_of_le_of_lt (hJle v) (lt_top_iff_ne_top.2 hItop))
  -- conclusion
  have hRHS : ∫ v, radialProb Sigma g u v ∂(sphereLaw m) =
      (∫⁻ v, chiLaw m {r : ℝ | 0 ≤ r ∧ g u (r • sqrtCov Sigma (v : EuclideanSpace ℝ (Fin m))) ≤ 0}
        ∂(sphereLaw m)).toReal := by
    rw [← integral_toReal hmeas.aemeasurable (Eventually.of_forall hfin)]
    rfl
  rw [hRHS, probFn, h1, stdGaussian_polar hm D hDm, sphereLaw, lintegral_smul_measure]
  simp only [hchi]
  rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hI0), ← hc0, hc0eq]
  congr 1
  ring
