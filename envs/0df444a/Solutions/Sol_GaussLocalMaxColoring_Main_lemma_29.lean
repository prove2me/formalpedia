-- Prove2me | solution 1 for GaussLocalMaxColoring.Main.lemma_29
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-17T17:08:28.055074+00:00
-- url     : https://prove2.me/submissions/f1dcf982-46b4-4e47-8a1f-e1d3dc6418da

import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_HairerSPDE_CameronMartin
import Definitions.Def_OAIQWGP000
import Definitions.Def_RecGaussColoring_Main_Gaussian


set_option autoImplicit false


open MeasureTheory ProbabilityTheory Filter

namespace SlepianProof

/-- The standard Gaussian density has derivative `-x ρ(x)`. -/
lemma gaussianPDF_hasDerivAt (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  have h := ((((hasDerivAt_id x).pow 2).neg.div_const 2).exp).const_mul
    (Real.sqrt (2 * Real.pi))⁻¹
  have heq : gaussianPDFReal 0 1 = fun y : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ *
      Real.exp (-(y ^ 2) / 2) := by
    ext y
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [heq]
  convert h using 1 <;> (try simp only [id_eq, Pi.pow_apply, Pi.neg_apply,
    Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]) <;> (first | ring | rfl)


/-- Transfer absolute integrability to the density-weighted Lebesgue integral. -/
lemma gaussian_weight_integrable {f : ℝ → ℝ}
    (hf : Integrable f (gaussianReal 0 1)) :
    Integrable (fun x => gaussianPDFReal 0 1 x * f x) := by
  rw [gaussianReal_of_var_ne_zero _ (one_ne_zero : (1 : NNReal) ≠ 0)] at hf
  have := (integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF 0 1) (ae_of_all _ fun _ => gaussianPDF_lt_top)).mp hf
  simpa only [toReal_gaussianPDF, smul_eq_mul] using this

/-- Gaussian integration by parts, under explicit absolute integrability assumptions.
No unproved boundary-decay hypothesis is used. -/
lemma gaussian_integration_by_parts {f f' : ℝ → ℝ}
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hf : Integrable f (gaussianReal 0 1))
    (hf' : Integrable f' (gaussianReal 0 1))
    (hxf : Integrable (fun x => x * f x) (gaussianReal 0 1)) :
    (∫ x, f' x ∂gaussianReal 0 1) =
      ∫ x, x * f x ∂gaussianReal 0 1 := by
  have hi1 : Integrable (fun x => f x * (-x * gaussianPDFReal 0 1 x)) := by
    convert (gaussian_weight_integrable hxf).neg using 1
    ext x
    simp only [Pi.neg_apply]
    ring
  have hi2 : Integrable (fun x => f' x * gaussianPDFReal 0 1 x) := by
    simpa only [mul_comm] using gaussian_weight_integrable hf'
  have hi0 : Integrable (fun x => f x * gaussianPDFReal 0 1 x) := by
    simpa only [mul_comm] using gaussian_weight_integrable hf
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun x _ => hderiv x) (fun x _ => gaussianPDF_hasDerivAt x) hi1 hi2 hi0
  rw [integral_gaussianReal_eq_integral_smul (one_ne_zero : (1 : NNReal) ≠ 0),
    integral_gaussianReal_eq_integral_smul (one_ne_zero : (1 : NNReal) ≠ 0)]
  simp only [smul_eq_mul]
  have h1 : (∫ x : ℝ, f x * (-x * gaussianPDFReal 0 1 x)) =
      -(∫ x : ℝ, gaussianPDFReal 0 1 x * (x * f x)) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  rw [h1] at h
  have h2 : (∫ x : ℝ, f' x * gaussianPDFReal 0 1 x) =
      ∫ x : ℝ, gaussianPDFReal 0 1 x * f' x := by
    simp only [mul_comm]
  rw [h2] at h
  linarith

/-- A bounded differentiable function with bounded derivative satisfies Stein's identity. -/
lemma gaussian_integration_by_parts_bounded {f f' : ℝ → ℝ} {C D : ℝ}
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hf' : AEStronglyMeasurable f' (gaussianReal 0 1))
    (hf_bound : ∀ x, ‖f x‖ ≤ C) (hf'_bound : ∀ x, ‖f' x‖ ≤ D) :
    (∫ x, f' x ∂gaussianReal 0 1) =
      ∫ x, x * f x ∂gaussianReal 0 1 := by
  have hf : Continuous f := continuous_iff_continuousAt.mpr fun x => (hderiv x).continuousAt
  have hi : Integrable f (gaussianReal 0 1) := by
    simpa using (integrable_const (1 : ℝ)).bdd_mul hf.aestronglyMeasurable
      (ae_of_all _ hf_bound)
  have hi' : Integrable f' (gaussianReal 0 1) := by
    simpa using (integrable_const (1 : ℝ)).bdd_mul hf'
      (ae_of_all _ hf'_bound)
  exact gaussian_integration_by_parts hderiv hi hi'
    (IsGaussian.integrable_id.mul_bdd hf.aestronglyMeasurable (ae_of_all _ hf_bound))

end SlepianProof


open MeasureTheory ProbabilityTheory Filter

namespace SlepianProof

/-- Coordinatewise Gaussian integration by parts in a finite product. -/
lemma gaussian_pi_integration_by_parts {n : ℕ} (i : Fin (n + 1))
    {f df : (Fin (n + 1) → ℝ) → ℝ}
    (hderiv : ∀ (x : Fin (n + 1) → ℝ) (t : ℝ),
      HasDerivAt (fun y => f (Function.update x i y)) (df (Function.update x i t)) t)
    (hf : Integrable f (Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)))
    (hdf : Integrable df (Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)))
    (hxf : Integrable (fun x => x i * f x)
      (Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1))) :
    (∫ x, df x ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) =
      ∫ x, x i * f x ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1) := by
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm
  have hp : MeasurePreserving e
      ((gaussianReal 0 1).prod (Measure.pi (fun _ : Fin n => gaussianReal 0 1)))
      (Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) :=
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => gaussianReal 0 1) i).symm
  have hfi := (hp.integrable_comp_emb e.measurableEmbedding).mpr hf
  have hdfi := (hp.integrable_comp_emb e.measurableEmbedding).mpr hdf
  have hxfi := (hp.integrable_comp_emb e.measurableEmbedding).mpr hxf
  rw [← hp.integral_comp' df, ← hp.integral_comp' (fun x => x i * f x)]
  simp only [Function.comp_def] at hfi hdfi hxfi
  rw [integral_prod_symm _ hdfi, integral_prod_symm _ hxfi]
  apply integral_congr_ae
  filter_upwards [hfi.prod_left_ae, hdfi.prod_left_ae, hxfi.prod_left_ae]
    with y hy hyd hyx
  have he (t : ℝ) : e (t, y) = i.insertNth t y := rfl
  simp only [Function.comp_def, he, Fin.insertNth_apply_same] at hy hyd hyx ⊢
  apply gaussian_integration_by_parts (f := fun t => f (i.insertNth t y))
    (f' := fun t => df (i.insertNth t y)) _ hy hyd hyx
  intro t
  have h := hderiv (i.insertNth 0 y) t
  simpa only [Fin.update_insertNth] using h

end SlepianProof


open MeasureTheory ProbabilityTheory

namespace SlepianProof

/-- Stein's identity for a smooth bounded function of an arbitrary linear Gaussian image. -/
lemma gaussian_linear_integration_by_parts {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : (Fin (n + 1) → ℝ) →L[ℝ] E) (i : Fin (n + 1))
    (f : E → ℝ) (hf : ContDiff ℝ 1 f) {C D : ℝ}
    (hf_bound : ∀ x, ‖f x‖ ≤ C) (hdf_bound : ∀ x, ‖fderiv ℝ f x‖ ≤ D) :
    (∫ x, fderiv ℝ f (L x) (L (Pi.single i 1))
      ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) =
    ∫ x, x i * f (L x)
      ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1) := by
  have hfcont : Continuous fun x => f (L x) := hf.continuous.comp L.continuous
  have hdfcont : Continuous fun x => fderiv ℝ f (L x) (L (Pi.single i 1)) :=
    ((hf.continuous_fderiv one_ne_zero).comp L.continuous).clm_apply continuous_const
  have hb : ∀ x : Fin (n + 1) → ℝ,
      ‖fderiv ℝ f (L x) (L (Pi.single i 1))‖ ≤ D * ‖L (Pi.single i 1)‖ := by
    intro x
    exact le_trans ((fderiv ℝ f (L x)).le_opNorm _) <|
      mul_le_mul_of_nonneg_right (hdf_bound _) (norm_nonneg _)
  have hfi : Integrable (fun x => f (L x))
      (Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) := by
    simpa using (integrable_const (1 : ℝ)).bdd_mul hfcont.aestronglyMeasurable
      (ae_of_all _ fun x => hf_bound (L x))
  have hdfi : Integrable (fun x => fderiv ℝ f (L x) (L (Pi.single i 1)))
      (Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) := by
    simpa using (integrable_const (1 : ℝ)).bdd_mul hdfcont.aestronglyMeasurable
      (ae_of_all _ hb)
  have hxfi : Integrable (fun x => x i * f (L x))
      (Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) :=
    (integrable_eval (μ := fun _ : Fin (n + 1) => gaussianReal 0 1)
      IsGaussian.integrable_id).mul_bdd hfcont.aestronglyMeasurable
        (ae_of_all _ fun x => hf_bound (L x))
  apply gaussian_pi_integration_by_parts i _ hfi hdfi hxfi
  intro x t
  exact ((hf.differentiable_one (L (Function.update x i t))).hasFDerivAt).comp_hasDerivAt t
    ((L.hasFDerivAt).comp_hasDerivAt t (hasDerivAt_update x i t))

end SlepianProof

theorem HighDimProb.RandomProcesses.gaussian_linear_integration_by_parts {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : (Fin (n + 1) → ℝ) →L[ℝ] E) (i : Fin (n + 1))
    (f : E → ℝ) (hf : ContDiff ℝ 1 f) {C D : ℝ}
    (hf_bound : ∀ x, ‖f x‖ ≤ C) (hdf_bound : ∀ x, ‖fderiv ℝ f x‖ ≤ D) :
    (∫ x, fderiv ℝ f (L x) (L (Pi.single i 1))
      ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) =
    ∫ x, x i * f (L x)
      ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1) := by
  exact SlepianProof.gaussian_linear_integration_by_parts L i f hf hf_bound hdf_bound


set_option autoImplicit false

section
-- module Solutions.OAIQW_GaussianPropeller.Translation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uX uY uι

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace

namespace GaussianPropeller.Translation

lemma map_density_comp {X : Type uX} {Y : Type uY} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (g : X → Y) (hg : Measurable g)
    (f : Y → ℝ≥0∞) (hf : Measurable f) :
    (μ.withDensity (f ∘ g)).map g = (μ.map g).withDensity f := by
  apply Measure.ext_of_lintegral
  intro h hh
  rw [lintegral_map hh hg]
  change (∫⁻ a, (h ∘ g) a ∂μ.withDensity (f ∘ g)) = _
  rw [lintegral_withDensity_eq_lintegral_mul _ (hf.comp hg) (hh.comp hg),
    lintegral_withDensity_eq_lintegral_mul _ hf hh]
  exact (lintegral_map (hf.mul hh) hg).symm

lemma product_density {ι : Type uι} [Fintype ι]
    (f : ι → ℝ → ℝ) (hf : ∀ i, Integrable (f i))
    (hn : ∀ i x, 0 ≤ f i x) :
    Measure.pi (fun i => volume.withDensity (fun x => ENNReal.ofReal (f i x))) =
      volume.withDensity (fun x : ι → ℝ => ENNReal.ofReal (∏ i, f i (x i))) := by
  classical
  have hii (i : ι) : IsFiniteMeasure (volume.withDensity (fun x => ENNReal.ofReal (f i x))) := by
    apply isFiniteMeasure_withDensity
    rw [← ofReal_integral_eq_lintegral_ofReal (hf i) (ae_of_all _ (hn i))]
    exact ENNReal.ofReal_ne_top
  apply Measure.pi_eq
  intro s hs
  have hp : Integrable (fun x : ι → ℝ => ∏ i, f i (x i)) volume :=
    Integrable.fintype_prod hf
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← ofReal_integral_eq_lintegral_ofReal hp.restrict (ae_of_all _ (fun x =>
      Finset.prod_nonneg (fun i _ => hn i (x i))))]
  have heq : (univ.pi s).indicator (fun x : ι → ℝ => ∏ i, f i (x i)) =
      (fun x => ∏ i, (s i).indicator (f i) (x i)) := by
    funext x
    by_cases hx : x ∈ univ.pi s
    · simp only [Set.mem_univ_pi] at hx
      rw [Set.indicator_of_mem (show x ∈ univ.pi s by simpa only [Set.mem_univ_pi] using hx)]
      exact Finset.prod_congr rfl (fun i _ => (Set.indicator_of_mem (hx i) (f i)).symm)
    · rw [Set.indicator_of_notMem hx]
      simp only [Set.mem_univ_pi, not_forall] at hx
      obtain ⟨i, hi⟩ := hx
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi (f i))
  rw [← integral_indicator (MeasurableSet.univ_pi hs), heq,
    integral_fintype_prod_volume_eq_prod (fun i => (s i).indicator (f i)),
    ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (fun x =>
      Set.indicator_nonneg (fun x _ => hn i x) x))]
  apply Finset.prod_congr rfl
  intro i _
  rw [integral_indicator (hs i), withDensity_apply _ (hs i),
    ofReal_integral_eq_lintegral_ofReal (hf i).restrict (ae_of_all _ (hn i))]

lemma pi_gaussian_density {ι : Type uι} [Fintype ι] (a : ι → ℝ) :
    Measure.pi (fun i => gaussianReal (a i) 1) =
      volume.withDensity (fun x : ι → ℝ =>
        ENNReal.ofReal (∏ i, gaussianPDFReal (a i) 1 (x i))) := by
  simp_rw [gaussianReal_of_var_ne_zero _ (by norm_num : (1 : NNReal) ≠ 0),
    gaussianPDF_def]
  exact product_density _ (fun i => integrable_gaussianPDFReal (a i) 1)
    (fun i => gaussianPDFReal_nonneg (a i) 1)

lemma measurable_stdDensity {ι : Type uι} [Fintype ι] :
    Measurable (stdDensity : EuclideanSpace ℝ ι → ℝ) := by
  unfold stdDensity
  fun_prop

lemma stdGaussian_density {ι : Type uι} [Fintype ι] :
    stdGaussian (EuclideanSpace ℝ ι) =
      volume.withDensity (fun x => ENNReal.ofReal (stdDensity x)) := by
  rw [← map_pi_eq_stdGaussian, pi_gaussian_density (fun _ => 0)]
  have hm := map_density_comp (volume : Measure (ι → ℝ)) (WithLp.toLp 2)
    (PiLp.volume_preserving_toLp ι).measurable
    (fun x => ENNReal.ofReal (stdDensity x))
    (measurable_stdDensity.ennreal_ofReal)
  rw [(PiLp.volume_preserving_toLp ι).map_eq] at hm
  exact hm

lemma stdDensity_pos {ι : Type uι} [Fintype ι] (x : EuclideanSpace ℝ ι) :
    0 < stdDensity x := by
  apply Finset.prod_pos
  intro i _
  exact gaussianPDFReal_pos _ _ _ (by norm_num)

end GaussianPropeller.Translation

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.Stein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uι

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace

open Filter
open scoped Topology
namespace GaussianPropeller.Stein
open GaussianPropeller.Translation

variable {ι : Type uι} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι
local notation "γ" => stdGaussian E

lemma integrable_bounded {H : E → ℝ} (hH : AEStronglyMeasurable H γ)
    {B : ℝ} (hB : ∀ x, ‖H x‖ ≤ B) : Integrable H γ :=
  Integrable.mono' (integrable_const B) hH (ae_of_all _ hB)

lemma integration_by_parts {H : E → ℝ} {D : E → E →L[ℝ] ℝ}
    (hD : ∀ x, HasFDerivAt H (D x) x) (hcD : Continuous D)
    {B C : ℝ} (hB : ∀ x, ‖H x‖ ≤ B) (hC : ∀ x, ‖D x‖ ≤ C) (v : E) :
    ∫ x, D x v ∂γ = ∫ x, H x*⟪v,x⟫ ∂γ := by
  -- coordinatewise from the published HighDimProb.RandomProcesses.gaussian_linear_integration_by_parts
  classical
  have hfd : fderiv ℝ H = D := funext fun x => (hD x).fderiv
  have hH1 : ContDiff ℝ 1 H :=
    contDiff_one_iff_fderiv.mpr ⟨fun x => (hD x).differentiableAt, hfd ▸ hcD⟩
  have hHc : Continuous H := hH1.continuous
  have hcoord (i : ι) :
      ∫ x, D x (EuclideanSpace.single i 1) ∂γ = ∫ x, H x * x i ∂γ := by
    have : Nonempty ι := ⟨i⟩
    have hne : Fintype.card ι ≠ 0 := Fintype.card_ne_zero
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hne
    let σ : ι ≃ Fin (n+1) := (Fintype.equivFin ι).trans (finCongr hn)
    let b : OrthonormalBasis (Fin (n+1)) ℝ E := (EuclideanSpace.basisFun ι ℝ).reindex σ
    let L : (Fin (n+1) → ℝ) →L[ℝ] E := LinearMap.toContinuousLinearMap
      { toFun := fun x => ∑ j, x j • b j
        map_add' := by intro x y; simp [add_smul, Finset.sum_add_distrib]
        map_smul' := by intro c x; simp [Finset.smul_sum, smul_smul] }
    have hL (x : Fin (n+1) → ℝ) : L x = ∑ j, x j • b j := rfl
    have hmap : γ = (Measure.pi fun _ : Fin (n+1) => gaussianReal 0 1).map L :=
      stdGaussian_eq_map_pi_orthonormalBasis b
    have hb (j : Fin (n+1)) : b j = EuclideanSpace.single (σ.symm j) 1 := by
      simp [b]
    have hLi (x : Fin (n+1) → ℝ) : (L x) i = x (σ i) := by
      simp [hL, hb, WithLp.ofLp_sum, Pi.single_apply, Equiv.eq_symm_apply]
    have h := HighDimProb.RandomProcesses.gaussian_linear_integration_by_parts L (σ i) H hH1
      hB (fun x => (hfd ▸ hC) x)
    have hLs : L (Pi.single (σ i) 1) = EuclideanSpace.single i 1 := by
      rw [hL]; simp [Pi.single_apply, hb]
    rw [hLs, hfd] at h
    rw [hmap, integral_map L.continuous.aemeasurable
        (hcD.clm_apply continuous_const).aestronglyMeasurable,
      integral_map L.continuous.aemeasurable
        (show AEStronglyMeasurable (fun x : E => H x * x i) _ from
          (hHc.mul ((EuclideanSpace.proj i : E →L[ℝ] ℝ).continuous)).aestronglyMeasurable), h]
    congr 1
    funext x
    simp only [hLi, mul_comm]
  have hv : v = ∑ i, v i • EuclideanSpace.single i (1:ℝ) := by
    simpa using ((EuclideanSpace.basisFun ι ℝ).sum_repr v).symm
  have hint1 (i : ι) : Integrable (fun x => D x (EuclideanSpace.single i 1)) γ :=
    Integrable.mono' (integrable_const C) (hcD.clm_apply continuous_const).aestronglyMeasurable
      (ae_of_all _ fun x => ((D x).le_opNorm _).trans (by simpa using hC x))
  have hint2 (i : ι) : Integrable (fun x => H x * x i) γ := by
    have hi : Integrable (fun x : E => x i) γ :=
      (EuclideanSpace.proj i : E →L[ℝ] ℝ).integrable_comp IsGaussian.integrable_id
    exact hi.bdd_mul hHc.aestronglyMeasurable (ae_of_all _ hB)
  calc ∫ x, D x v ∂γ = ∫ x, ∑ i, v i * D x (EuclideanSpace.single i 1) ∂γ := by
        congr 1; funext x; conv_lhs => rw [hv]
        simp [map_sum, map_smul]
    _ = ∑ i, v i * ∫ x, H x * x i ∂γ := by
        rw [integral_finsetSum _ fun i _ => (hint1 i).const_mul _]
        simp_rw [integral_const_mul, hcoord]
    _ = ∫ x, H x * ⟪v,x⟫ ∂γ := by
        rw [show (∑ i, v i * ∫ x, H x * x i ∂γ) = ∫ x, ∑ i, v i * (H x * x i) ∂γ by
          rw [integral_finsetSum _ fun i _ => (hint2 i).const_mul _]; simp_rw [integral_const_mul]]
        congr 1; funext x
        simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro i _; ring

end GaussianPropeller.Stein

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.HeatConvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uV uι

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology

namespace GaussianPropeller.HeatConvolution
open GaussianPropeller.Stein
variable {ι : Type uι} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι
local notation "γ" => stdGaussian E

section General
variable {V : Type uV} [NormedAddCommGroup V]

lemma integrable_shift [NormedSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    {F : E → V} (hF : Continuous F) {B : ℝ}
    (hB : ∀ x, ‖F x‖ ≤ B) (t : ℝ) (x : E) :
    Integrable (fun z => F (x+Real.sqrt t • z)) γ :=
  Integrable.mono' (integrable_const B) (by fun_prop) (ae_of_all _ (fun z => hB _))

lemma continuous_heat [NormedSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    {F : E → V} (hF : Continuous F) {B : ℝ}
    (hB : ∀ x, ‖F x‖ ≤ B) : Continuous (fun p : ℝ × E => heat F p.1 p.2) := by
  apply continuous_of_dominated (bound := fun _ : E => B)
  · intro p; fun_prop
  · intro p; exact ae_of_all _ (fun z => hB _)
  · exact integrable_const _
  · filter_upwards [] with z; fun_prop

variable [NormedSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

lemma fderiv_heat {F : E → V} {D : E → E →L[ℝ] V}
    (hD : ∀ x, HasFDerivAt F (D x) x) (hcD : Continuous D)
    {B C : ℝ} (hB : ∀ x, ‖F x‖ ≤ B) (hC : ∀ x, ‖D x‖ ≤ C)
    (t : ℝ) (x : E) : HasFDerivAt (heat F t) (heat D t x) x := by
  have hc : Continuous F := continuous_iff_continuousAt.mpr (fun x => (hD x).continuousAt)
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (s := univ)
    (bound := fun _ => C) (F' := fun x z => D (x+Real.sqrt t • z)) (by simp)
  · exact Filter.Eventually.of_forall (fun x => by fun_prop)
  · exact integrable_shift hc hB t x
  · fun_prop
  · exact ae_of_all _ (fun z x _ => hC _)
  · exact integrable_const _
  · filter_upwards [] with z x _
    simpa only [Function.comp_def, ContinuousLinearMap.comp_id, id_eq] using
      (hD (x+Real.sqrt t • z)).comp x ((hasFDerivAt_id x).add_const _)

lemma time_deriv_heat {F : E → V} {D : E → E →L[ℝ] V}
    (hD : ∀ x, HasFDerivAt F (D x) x) (hcD : Continuous D)
    {B C : ℝ} (hB : ∀ x, ‖F x‖ ≤ B) (hC : ∀ x, ‖D x‖ ≤ C)
    {t : ℝ} (ht : 0 < t) (x : E) :
    HasDerivAt (fun s => heat F s x)
      ((1/(2*Real.sqrt t)) • (∫ z, D (x+Real.sqrt t • z) z ∂γ)) t := by
  have hc : Continuous F := continuous_iff_continuousAt.mpr (fun x => (hD x).continuousAt)
  have hC0 : 0 ≤ C := (norm_nonneg (D 0)).trans (hC 0)
  have hp : 0 < Real.sqrt (t/2) := Real.sqrt_pos.mpr (by linarith)
  have hi : Integrable (fun z : E => ‖z‖) γ := (IsGaussian.integrable_id (μ := γ)).norm
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := γ) (x₀ := t) (F := fun s z => F (x+Real.sqrt s • z))
    (F' := fun s z => (1/(2*Real.sqrt s)) • D (x+Real.sqrt s • z) z)
    (s := Ioo (t/2) (2*t)) (bound := fun z => (1/(2*Real.sqrt (t/2)))*C*‖z‖)
    (Ioo_mem_nhds (by linarith) (by linarith))
    (Filter.Eventually.of_forall (fun s => by fun_prop))
    (integrable_shift hc hB t x) (by fun_prop) ?_ (hi.const_mul _) ?_
  · simpa only [integral_smul, heat] using hd.2
  · filter_upwards [] with z s hs
    have hs0 : 0 < s := by linarith only [hs.1, ht]
    have hsqrt : Real.sqrt (t/2) ≤ Real.sqrt s := Real.sqrt_le_sqrt hs.1.le
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr (by positivity))]
    calc
      (1/(2*Real.sqrt s))*‖D (x+Real.sqrt s • z) z‖ ≤
          (1/(2*Real.sqrt (t/2)))*(C*‖z‖) :=
        mul_le_mul (one_div_le_one_div_of_le (by positivity) (by linarith))
          ((D _).le_opNorm z |>.trans (mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)))
          (norm_nonneg _) (by positivity)
      _ = _ := by ring
  · filter_upwards [] with z s hs
    have hs0 : s ≠ 0 := ne_of_gt (by linarith only [hs.1, ht])
    simpa only [Function.comp_def, map_smul] using
      (hD (x+Real.sqrt s • z)).comp_hasDerivAt s
        ((Real.hasDerivAt_sqrt hs0).smul_const z |>.const_add x)

end General

lemma stein_trace {g : E → E} {K : E → E →L[ℝ] E}
    (hg : ∀ x, HasFDerivAt g (K x) x) (hcK : Continuous K)
    {C D : ℝ} (hC : ∀ x, ‖g x‖ ≤ C) (hD : ∀ x, ‖K x‖ ≤ D)
    (r : ℝ) (x : E) :
    (∫ z, ⟪g (x+r•z),z⟫ ∂γ) = r*(∫ z, ∑ i, ⟪K (x+r•z)
      (EuclideanSpace.basisFun ι ℝ i), EuclideanSpace.basisFun ι ℝ i⟫ ∂γ) := by
  let e := EuclideanSpace.basisFun ι ℝ
  have hc : Continuous g := continuous_iff_continuousAt.mpr (fun x => (hg x).continuousAt)
  have hC0 : 0 ≤ C := (norm_nonneg (g 0)).trans (hC 0)
  have hD0 : 0 ≤ D := (norm_nonneg (K 0)).trans (hD 0)
  have he (i : ι) : ‖e i‖ = 1 := e.orthonormal.norm_eq_one i
  have hi (i : ι) :
      r*(∫ z, ⟪e i,K (x+r•z) (e i)⟫ ∂γ) =
        ∫ z, ⟪e i,g (x+r•z)⟫*⟪e i,z⟫ ∂γ := by
    have hh := integration_by_parts (H := fun z => ⟪e i,g (x+r•z)⟫)
      (D := fun z => r • ((innerSL ℝ (e i)).comp (K (x+r•z))))
      (B := C) (C := |r| *D) ?_ (by fun_prop) ?_ ?_ (e i)
    · simpa only [smul_apply, ContinuousLinearMap.comp_apply,
        innerSL_apply_apply, smul_eq_mul, integral_const_mul] using hh
    · intro z
      have hh := ((innerSL ℝ (e i)).hasFDerivAt).comp z
        ((hg (x+r•z)).comp z ((hasFDerivAt_id z).const_smul r |>.const_add x))
      convert hh using 1 <;> (first | rfl | (ext v; simp))
    · intro z
      exact (norm_inner_le_norm _ _).trans (by rw [he, one_mul]; exact hC _)
    · intro z
      rw [norm_smul, Real.norm_eq_abs]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      calc
        ‖(innerSL ℝ (e i)).comp (K (x+r•z))‖ ≤ ‖innerSL ℝ (e i)‖*‖K (x+r•z)‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ D := by rw [innerSL_apply_norm, he, one_mul]; exact hD _
  have hleft (i : ι) : Integrable (fun z : E => ⟪e i,g (x+r•z)⟫*⟪e i,z⟫) γ := by
    apply Integrable.mono' ((IsGaussian.integrable_id (μ := γ)).norm.const_mul C) (by fun_prop)
    filter_upwards [] with z
    rw [norm_mul]
    have ha : ‖⟪e i,g (x+r•z)⟫‖ ≤ C :=
      (norm_inner_le_norm _ _).trans (by rw [he, one_mul]; exact hC _)
    have hb : ‖⟪e i,z⟫‖ ≤ ‖z‖ := by simpa only [he, one_mul] using norm_inner_le_norm (e i) z
    exact mul_le_mul ha hb (norm_nonneg _) hC0
  have hright (i : ι) : Integrable (fun z : E => ⟪e i,K (x+r•z) (e i)⟫) γ := by
    apply integrable_bounded (by fun_prop) (B := D)
    intro z
    calc
      ‖⟪e i,K (x+r•z) (e i)⟫‖ ≤ ‖e i‖*‖K (x+r•z) (e i)‖ := norm_inner_le_norm _ _
      _ ≤ D := by rw [he, one_mul]; simpa only [he, mul_one] using
        ((K _).le_opNorm (e i)).trans (mul_le_mul_of_nonneg_right (hD _) (norm_nonneg _))
  calc
    (∫ z, ⟪g (x+r•z),z⟫ ∂γ) = ∫ z, ∑ i, ⟪e i,g (x+r•z)⟫*⟪e i,z⟫ ∂γ := by
      apply integral_congr_ae
      filter_upwards [] with z
      simpa only [real_inner_comm (e _) (g _)] using (e.sum_inner_mul_inner (g (x+r•z)) z).symm
    _ = ∑ i, ∫ z, ⟪e i,g (x+r•z)⟫*⟪e i,z⟫ ∂γ := integral_finsetSum _ (fun i _ => hleft i)
    _ = ∑ i, r*(∫ z, ⟪e i,K (x+r•z) (e i)⟫ ∂γ) := by simp_rw [hi]
    _ = r*(∫ z, ∑ i, ⟪e i,K (x+r•z) (e i)⟫ ∂γ) := by
      rw [integral_finsetSum _ (fun i _ => hright i), Finset.mul_sum]
    _ = _ := by congr 1; apply integral_congr_ae; filter_upwards [] with z; congr 1; ext i; exact real_inner_comm _ _

lemma heat_gradient {F : E → ℝ} {g : E → E}
    (hF : ∀ x, HasFDerivAt F (innerSL ℝ (g x)) x) (hcg : Continuous g)
    {B C : ℝ} (hB : ∀ x, ‖F x‖ ≤ B) (hC : ∀ x, ‖g x‖ ≤ C)
    (t : ℝ) (x : E) :
    HasFDerivAt (heat F t) (innerSL ℝ (heat g t x)) x := by
  have hd := fderiv_heat hF (by fun_prop) hB (fun x => by
    rw [innerSL_apply_norm]; exact hC x) t x
  have heq : heat (fun y => innerSL ℝ (g y)) t x = innerSL ℝ (heat g t x) :=
    (innerSL ℝ).integral_comp_comm (integrable_shift hcg hC t x)
  rwa [heq] at hd

lemma heat_equation {F : E → ℝ} {g : E → E} {K : E → E →L[ℝ] E}
    (hF : ∀ x, HasFDerivAt F (innerSL ℝ (g x)) x)
    (hg : ∀ x, HasFDerivAt g (K x) x) (hcK : Continuous K)
    {B C D : ℝ} (hB : ∀ x, ‖F x‖ ≤ B) (hC : ∀ x, ‖g x‖ ≤ C)
    (hD : ∀ x, ‖K x‖ ≤ D) {t : ℝ} (ht : 0 < t) (x : E) :
    HasDerivAt (fun s => heat F s x)
      ((∑ i : ι, ⟪(heat K t x) (EuclideanSpace.basisFun ι ℝ i),
        EuclideanSpace.basisFun ι ℝ i⟫)/2) t := by
  have hcg : Continuous g := continuous_iff_continuousAt.mpr (fun x => (hg x).continuousAt)
  have hd := time_deriv_heat hF (by fun_prop) hB (fun x => by
    rw [innerSL_apply_norm]; exact hC x) ht x
  simp only [innerSL_apply_apply, smul_eq_mul] at hd
  rw [stein_trace hg hcK hC hD] at hd
  have hi : Integrable (fun z => K (x+Real.sqrt t • z)) γ :=
    Integrable.mono' (integrable_const D) (by fun_prop) (ae_of_all _ (fun z => hD _))
  have heq : (∫ z, ∑ i : ι, ⟪K (x+Real.sqrt t • z)
      (EuclideanSpace.basisFun ι ℝ i), EuclideanSpace.basisFun ι ℝ i⟫ ∂γ) =
      ∑ i : ι, ⟪(heat K t x) (EuclideanSpace.basisFun ι ℝ i),
        EuclideanSpace.basisFun ι ℝ i⟫ := by
    let e := EuclideanSpace.basisFun ι ℝ
    have hii (i : ι) : Integrable (fun z => ⟪K (x+Real.sqrt t • z) (e i),e i⟫) γ :=
      ((ContinuousLinearMap.apply ℝ E (e i)).integrable_comp hi).inner_const (e i)
    rw [integral_finsetSum _ (fun i _ => hii i)]
    apply Finset.sum_congr rfl
    intro i _
    change (∫ z, ⟪K (x+Real.sqrt t • z) (e i),e i⟫ ∂γ) = ⟪heat K t x (e i),e i⟫
    calc
      _ = ∫ z, ⟪e i,K (x+Real.sqrt t • z) (e i)⟫ ∂γ :=
        integral_congr_ae (ae_of_all _ (fun z => real_inner_comm _ _))
      _ = ⟪e i,∫ z, K (x+Real.sqrt t • z) (e i) ∂γ⟫ :=
        integral_inner ((ContinuousLinearMap.apply ℝ E (e i)).integrable_comp hi) _
      _ = _ := by
        rw [← ContinuousLinearMap.integral_apply hi]
        exact real_inner_comm _ _
  rw [heq] at hd
  convert hd using 1 <;> first | rfl | field_simp [ne_of_gt (Real.sqrt_pos.mpr ht)]

end GaussianPropeller.HeatConvolution

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.Quantile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace GaussianPropeller.Quantile

lemma cdfIso_coe (x : ℝ) : (cdfIso x : ℝ) = Φ x := rfl
lemma q_of_mem {p : ℝ} (hp : p ∈ Ioo (0:ℝ) 1) : q p = cdfIso.symm ⟨p,hp⟩ := by
  simp [q, hp]
lemma Φ_q {p : ℝ} (hp : p ∈ Ioo (0:ℝ) 1) : Φ (q p) = p := by
  rw [q_of_mem hp, ← cdfIso_coe]
  exact congrArg Subtype.val (cdfIso.apply_symm_apply ⟨p,hp⟩)
lemma q_Φ (x : ℝ) : q (Φ x) = x := by
  rw [q_of_mem (Φ_mem x)]
  exact cdfIso.symm_apply_apply x
lemma continuousOn_q : ContinuousOn q (Ioo (0:ℝ) 1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous (fun p : Ioo (0:ℝ) 1 => q p)
  have heq : (fun p : Ioo (0:ℝ) 1 => q p) = cdfIso.symm := by
    funext p
    exact q_of_mem p.2
  rw [heq]
  exact cdfIso.symm.continuous
lemma continuousAt_q {p : ℝ} (hp : p ∈ Ioo (0:ℝ) 1) : ContinuousAt q p :=
  continuousOn_q.continuousAt (isOpen_Ioo.mem_nhds hp)
lemma hasDerivAt_q {p : ℝ} (hp : p ∈ Ioo (0:ℝ) 1) :
    HasDerivAt q (φ (q p))⁻¹ p := by
  apply HasDerivAt.of_local_left_inverse (continuousAt_q hp) (hasDerivAt_Φ (q p))
    (ne_of_gt (φ_pos _))
  filter_upwards [isOpen_Ioo.mem_nhds hp] with y hy
  exact Φ_q hy
lemma strictMonoOn_q : StrictMonoOn q (Ioo (0:ℝ) 1) := by
  intro a ha b hb hab
  rw [q_of_mem ha, q_of_mem hb]
  exact cdfIso.symm.strictMono hab

lemma I_pos (p : ℝ) : 0 < I p := φ_pos _
lemma I_Φ (x : ℝ) : I (Φ x) = φ x := by simp [I, q_Φ]
lemma hasDerivAt_I {p : ℝ} (hp : p ∈ Ioo (0:ℝ) 1) : HasDerivAt I (-q p) p := by
  convert (hasDerivAt_φ (q p)).comp p (hasDerivAt_q hp) using 1 <;>
    first | rfl | field_simp [ne_of_gt (φ_pos (q p))]
lemma antitoneOn_I_deriv : AntitoneOn (fun p => -q p) (Ioo (0:ℝ) 1) := by
  intro a ha b hb hab
  exact neg_le_neg (strictMonoOn_q.monotoneOn ha hb hab)
lemma concaveOn_I : ConcaveOn ℝ (Ioo (0:ℝ) 1) I := by
  have hanti : AntitoneOn (deriv I) (Ioo (0:ℝ) 1) := by
    intro a ha b hb hab
    rw [(hasDerivAt_I ha).deriv, (hasDerivAt_I hb).deriv]
    exact antitoneOn_I_deriv ha hb hab
  apply (hanti.mono interior_subset).concaveOn_of_deriv (convex_Ioo 0 1)
  · exact fun p hp => (hasDerivAt_I hp).continuousAt.continuousWithinAt
  · exact fun p hp => (hasDerivAt_I (interior_subset hp)).differentiableAt.differentiableWithinAt

lemma concave_le_tangent {S : Set ℝ} {f : ℝ → ℝ} (hf : ConcaveOn ℝ S f)
    {x y d : ℝ} (hx : x ∈ S) (hy : y ∈ S) (hd : HasDerivAt f d x) :
    f y ≤ f x+d*(y-x) := by
  rcases lt_trichotomy x y with h | rfl | h
  · have hh := hf.slope_le_of_hasDerivAt hx hy h hd
    rw [slope_def_field] at hh
    have hh' := (div_le_iff₀ (sub_pos.mpr h)).mp hh
    linarith
  · simp
  · have hh := hf.le_slope_of_hasDerivAt hy hx h hd
    rw [slope_def_field] at hh
    have hh' := (le_div_iff₀ (sub_pos.mpr h)).mp hh
    nlinarith only [hh']

lemma I_le_tangent {p r : ℝ} (hp : p ∈ Ioo (0:ℝ) 1) (hr : r ∈ Ioo (0:ℝ) 1) :
    I r ≤ I p-q p*(r-p) := by
  simpa only [neg_mul, sub_eq_add_neg] using concave_le_tangent concaveOn_I hp hr (hasDerivAt_I hp)

lemma φ_le_zero (x : ℝ) : φ x ≤ φ 0 := by
  unfold φ
  simp only [zero_pow (by norm_num : 2 ≠ 0), neg_zero, zero_div, Real.exp_zero, mul_one]
  exact mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x]))

section Integration
variable {X : Type uX} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

lemma integrable_Φ_comp {f : X → ℝ} (hf : AEStronglyMeasurable f μ) :
    Integrable (fun x => Φ (f x)) μ := by
  apply Integrable.mono' (integrable_const (1:ℝ)) (continuous_Φ.comp_aestronglyMeasurable hf)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_pos (Φ_pos _)]
  exact (Φ_lt_one _).le
lemma integrable_φ_comp {f : X → ℝ} (hf : AEStronglyMeasurable f μ) :
    Integrable (fun x => φ (f x)) μ := by
  apply Integrable.mono' (integrable_const (φ 0)) (continuous_φ.comp_aestronglyMeasurable hf)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_pos (φ_pos _)]
  exact φ_le_zero _
lemma integral_Φ_mem {f : X → ℝ} (hf : AEStronglyMeasurable f μ) :
    (∫ x, Φ (f x) ∂μ) ∈ Ioo (0:ℝ) 1 := by
  have hpos {g : X → ℝ} (hg : Integrable g μ) (hh : ∀ x, 0 < g x) : 0 < ∫ x, g x ∂μ := by
    apply (integral_pos_iff_support_of_nonneg (fun x => (hh x).le) hg).mpr
    have heq : Function.support g = univ := by ext x; simp [Function.mem_support, ne_of_gt (hh x)]
    simp [heq]
  refine ⟨hpos (integrable_Φ_comp hf) (fun x => Φ_pos _), ?_⟩
  have hh := hpos ((integrable_const (1:ℝ)).sub (integrable_Φ_comp hf))
    (fun x => sub_pos.mpr (Φ_lt_one (f x)))
  simp only [Pi.sub_apply] at hh
  rw [integral_sub (integrable_const (1:ℝ)) (integrable_Φ_comp hf), integral_const] at hh
  simp only [probReal_univ, smul_eq_mul, one_mul] at hh
  linarith only [hh]

lemma integral_φ_le_I {f : X → ℝ} (hf : AEStronglyMeasurable f μ) :
    (∫ x, φ (f x) ∂μ) ≤ I (∫ x, Φ (f x) ∂μ) := by
  let p := ∫ x, Φ (f x) ∂μ
  have hp : p ∈ Ioo (0:ℝ) 1 := integral_Φ_mem hf
  have hi := integral_mono (integrable_φ_comp hf)
    ((integrable_const (I p)).sub (((integrable_Φ_comp hf).sub (integrable_const p)).const_mul (q p)))
    (fun x => by simpa only [I_Φ, Pi.sub_apply] using I_le_tangent hp (Φ_mem (f x)))
  simp only [Pi.sub_apply] at hi
  rw [integral_sub (integrable_const (I p)), integral_const, integral_const_mul,
    integral_sub (integrable_Φ_comp hf) (integrable_const p), integral_const] at hi
  · simpa only [probReal_univ, smul_eq_mul, one_mul, show (∫ x, Φ (f x) ∂μ) = p from rfl,
      sub_self, mul_zero, sub_zero] using hi
  · exact ((integrable_Φ_comp hf).sub (integrable_const p)).const_mul (q p)

lemma hasDerivAt_integral_shift {f : X → ℝ} (hf : AEStronglyMeasurable f μ) (a : ℝ) :
    HasDerivAt (fun s => ∫ x, Φ (f x+s) ∂μ) (∫ x, φ (f x+a) ∂μ) a := by
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := univ) (bound := fun _ => φ 0)
    (F' := fun s x => φ (f x+s)) (by simp) ?_ (integrable_Φ_comp (hf.add_const a))
    (continuous_φ.comp_aestronglyMeasurable (hf.add_const a)) ?_ (integrable_const (φ 0)) ?_).2
  · exact Filter.Eventually.of_forall fun s => continuous_Φ.comp_aestronglyMeasurable (hf.add_const s)
  · filter_upwards [] with x
    intro s _
    rw [Real.norm_eq_abs, abs_of_pos (φ_pos _)]
    exact φ_le_zero _
  · filter_upwards [] with x
    intro s _
    simpa only [mul_one, Function.comp_def, id_eq] using (hasDerivAt_Φ (f x+s)).comp s ((hasDerivAt_id s).const_add (f x))

lemma hasDerivAt_quantile_shift {f : X → ℝ} (hf : AEStronglyMeasurable f μ) (a : ℝ) :
    HasDerivAt (fun s => q (∫ x, Φ (f x+s) ∂μ))
      ((∫ x, φ (f x+a) ∂μ)/I (∫ x, Φ (f x+a) ∂μ)) a := by
  convert (hasDerivAt_q (integral_Φ_mem (hf.add_const a))).comp a
    (hasDerivAt_integral_shift hf a) using 1 <;> first | rfl | (simp only [I]; ring)

lemma quantile_shift_le {f : X → ℝ} (hf : AEStronglyMeasurable f μ) {a : ℝ} (ha : 0 ≤ a) :
    q (∫ x, Φ (f x+a) ∂μ) ≤ q (∫ x, Φ (f x) ∂μ)+a := by
  have hd (s : ℝ) := (hasDerivAt_quantile_shift hf s).sub (hasDerivAt_id s)
  have hm : Antitone (fun s => q (∫ x, Φ (f x+s) ∂μ)-s) := antitone_of_hasDerivAt_nonpos hd
    (fun s => by
      have hh := (div_le_one (I_pos _)).mpr (integral_φ_le_I (hf.add_const s))
      exact sub_nonpos.mpr hh)
  have hh := hm ha
  simp only [add_zero, sub_zero] at hh
  linarith only [hh]

end Integration
end GaussianPropeller.Quantile

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.QuantileCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uι

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

open scoped RealInnerProductSpace
namespace GaussianPropeller.QuantilePDE
open GaussianPropeller.Quantile

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma quantile_fderiv {u : E → ℝ} {g : E} {x : E}
    (hu : u x ∈ Ioo (0:ℝ) 1) (hd : HasFDerivAt u (innerSL ℝ g) x) :
    HasFDerivAt (fun y => q (u y)) (innerSL ℝ ((φ (q (u x)))⁻¹ • g)) x := by
  have hh := (hasDerivAt_q hu).comp_hasFDerivAt x hd
  convert hh using 1 <;> (first | rfl | (ext y; simp))

lemma quantile_gradient_line_derivative {u : E → ℝ} {g : E → E}
    {K : E → E →L[ℝ] E} (hu : ∀ x, u x ∈ Ioo (0:ℝ) 1)
    (hdu : ∀ x, HasFDerivAt u (innerSL ℝ (g x)) x)
    (hdg : ∀ x, HasFDerivAt g (K x) x) (x e : E) :
    HasDerivAt (fun s : ℝ => ⟪(φ (q (u (x+s•e))))⁻¹ • g (x+s•e), e⟫)
      ((φ (q (u x)))⁻¹*⟪K x e,e⟫ +
        q (u x)*(φ (q (u x)))⁻¹^2*⟪g x,e⟫^2) 0 := by
  have hdx : HasDerivAt (fun s : ℝ => x+s•e) e 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const e).const_add x
  have hdv : HasDerivAt (fun s : ℝ => q (u (x+s•e)))
      ((φ (q (u x)))⁻¹*⟪g x,e⟫) 0 := by
    simpa [Function.comp_def] using (quantile_fderiv (hu (x+0•e)) (hdu (x+0•e))).comp_hasDerivAt 0 hdx
  have hdφ := (hasDerivAt_φ (q (u (x+0•e)))).comp 0 hdv
  have hdi := hdφ.inv (ne_of_gt (φ_pos _))
  have hdg' : HasDerivAt (fun s : ℝ => g (x+s•e)) (K x e) 0 := by
    simpa only [Function.comp_def, zero_smul, add_zero] using (hdg (x+0•e)).comp_hasDerivAt 0 hdx
  have hi : HasDerivAt (fun s : ℝ => ⟪g (x+s•e), e⟫) ⟪K x e,e⟫ 0 := by
    simpa using hdg'.inner ℝ (hasDerivAt_const (0:ℝ) e)
  have hh := hdi.mul hi
  convert hh using 1 <;> try rfl
  · funext s; simp only [real_inner_smul_left, Function.comp_def, Pi.mul_apply, Pi.inv_apply]
  · simp only [Function.comp_def, zero_smul, add_zero, Pi.inv_apply]
    field_simp [ne_of_gt (φ_pos (q (u x)))]
    ring

lemma trace_quantile_hessian {ι : Type uι} [Fintype ι]
    (e : OrthonormalBasis ι ℝ E) (v a : ℝ) (g : E) (K : E →L[ℝ] E) :
    (∑ i : ι, (a*⟪K (e i),e i⟫ + v*a^2*⟪g,e i⟫^2)) - v*‖a • g‖^2 =
      a*(∑ i : ι, ⟪K (e i),e i⟫) := by
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    e.sum_sq_inner_left, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

end GaussianPropeller.QuantilePDE

namespace GaussianPropeller.SmoothCDF
open GaussianPropeller.Quantile
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma abs_mul_φ_le (a : ℝ) : |a| *φ a ≤ φ 0 := by
  have hsq : |a| ≤ 1+a^2/2 := by nlinarith [sq_nonneg (|a|-1), sq_abs a]
  have he : |a| ≤ Real.exp (a^2/2) := hsq.trans (by nlinarith [Real.add_one_le_exp (a^2/2)])
  have hh := mul_le_mul_of_nonneg_right he (Real.exp_pos (-a^2/2)).le
  rw [← Real.exp_add] at hh
  have heq : a^2/2 + -a^2/2 = 0 := by ring
  rw [heq, Real.exp_zero] at hh
  unfold φ
  simp only [zero_pow (by norm_num : 2 ≠ 0), neg_zero, zero_div, Real.exp_zero, mul_one]
  nlinarith [mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ (Real.sqrt (2*Real.pi))⁻¹)]

lemma fderiv {f : E → ℝ} {g : E → E}
    (hf : ∀ x, HasFDerivAt f (innerSL ℝ (g x)) x) (x : E) :
    HasFDerivAt (fun y => Φ (f y)) (innerSL ℝ (grad f g x)) x := by
  have h := (hasDerivAt_Φ (f x)).comp_hasFDerivAt x (hf x)
  convert h using 1 <;> (first | rfl | (ext e; simp [grad]))

lemma grad_fderiv {f : E → ℝ} {g : E → E} {K : E → E →L[ℝ] E}
    (hf : ∀ x, HasFDerivAt f (innerSL ℝ (g x)) x)
    (hg : ∀ x, HasFDerivAt g (K x) x) (x : E) :
    HasFDerivAt (grad f g) (hess f g K x) x := by
  have h := ((hasDerivAt_φ (f x)).comp_hasFDerivAt x (hf x)).smul (hg x)
  convert h using 1 <;> try rfl
  ext e
  simp only [hess, sub_apply, add_apply,
    smul_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_eq_mul, Function.comp_def]
  module

lemma continuous_hess {f : E → ℝ} {g : E → E} {K : E → E →L[ℝ] E}
    (hf : Continuous f) (hg : Continuous g) (hK : Continuous K) : Continuous (hess f g K) := by
  have hφ := continuous_φ.comp hf
  unfold hess
  fun_prop

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma cdf_bound [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (x : E) : ‖Φ (f x)‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_pos (Φ_pos _)]; exact (Φ_lt_one _).le

lemma grad_bound {f : E → ℝ} {g : E → E} {L : ℝ}
    (hL : ∀ x, ‖g x‖ ≤ L) (x : E) : ‖grad f g x‖ ≤ φ 0*L := by
  rw [grad, norm_smul, Real.norm_eq_abs, abs_of_pos (φ_pos _)]
  exact mul_le_mul (φ_le_zero _) (hL x) (norm_nonneg _) (φ_pos _).le

lemma hess_bound {f : E → ℝ} {g : E → E} {K : E → E →L[ℝ] E} {L D : ℝ}
    (hL0 : 0 ≤ L) (hL : ∀ x, ‖g x‖ ≤ L) (hD : ∀ x, ‖K x‖ ≤ D) (x : E) :
    ‖hess f g K x‖ ≤ φ 0*(D+L^2) := by
  have hD0 : 0 ≤ D := (norm_nonneg (K x)).trans (hD x)
  calc
    ‖hess f g K x‖ ≤ ‖φ (f x) • K x‖ +
        ‖(f x*φ (f x)) • ((innerSL ℝ (g x)).smulRight (g x))‖ := norm_sub_le _ _
    _ = φ (f x)*‖K x‖ + (|f x| *φ (f x))*‖g x‖^2 := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (φ_pos _), abs_mul, abs_of_pos (φ_pos _),
        ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]
      ring
    _ ≤ φ 0*D + φ 0*L^2 := add_le_add
      (mul_le_mul (φ_le_zero _) (hD x) (norm_nonneg _) (φ_pos _).le)
      (mul_le_mul (abs_mul_φ_le _) ((sq_le_sq₀ (norm_nonneg _) hL0).2 (hL x))
        (sq_nonneg _) (φ_pos _).le)
    _ = _ := by ring

end GaussianPropeller.SmoothCDF

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.HeatMaximum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uι

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace

open Set Filter
open scoped Topology RealInnerProductSpace

namespace GaussianPropeller.HeatMaximum

lemma second_deriv_nonneg_of_localMin {f g : ℝ → ℝ} {d : ℝ}
    (hf : ∀ s, HasDerivAt f (g s) s) (hg : HasDerivAt g d 0)
    (hm : IsLocalMin f 0) : 0 ≤ d := by
  by_contra hd
  have hd0 : d < 0 := lt_of_not_ge hd
  have hg0 : g 0 = 0 := hm.hasDerivAt_eq_zero (hf 0)
  have ht := hg.tendsto_slope.eventually (Iio_mem_nhds hd0)
  have hne : ∀ᶠ s in 𝓝[>] (0:ℝ), g s < 0 := by
    have ht' := ht.filter_mono (nhdsWithin_mono (0:ℝ) (by
      intro x hx; exact ne_of_gt hx))
    filter_upwards [ht', self_mem_nhdsWithin] with s hs hs0
    rw [slope_def_field, hg0, sub_zero, sub_zero] at hs
    simpa only [zero_mul] using (div_lt_iff₀ (show 0 < s from hs0)).mp hs
  obtain ⟨a, ha, hsub⟩ := Metric.mem_nhdsWithin_iff.mp hne
  obtain ⟨b, hb, hmin⟩ := Metric.mem_nhds_iff.mp hm
  let c := min a b / 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hca : c < a := by dsimp [c]; have := min_le_left a b; linarith
  have hcb : c < b := by dsimp [c]; have := min_le_right a b; linarith
  have hant : StrictAntiOn f (Icc 0 c) := strictAntiOn_of_deriv_neg (convex_Icc 0 c)
    (fun x _ => (hf x).continuousAt.continuousWithinAt)
    (fun x hx => by
      rw [interior_Icc] at hx
      rw [(hf x).deriv]
      apply hsub
      exact ⟨by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hx.1] using hx.2.trans hca,
        hx.1⟩)
  have hlt : f c < f 0 := hant (by simp [hc.le]) (by simp [hc.le]) hc
  have hge : f 0 ≤ f c := by
    apply hmin
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hc] using hcb
  exact (not_lt_of_ge hge) hlt

lemma deriv_nonpos_of_min_on_left {f : ℝ → ℝ} {a t d : ℝ} (hat : a < t)
    (hm : ∀ s ∈ Icc a t, f t ≤ f s) (hd : HasDerivAt f d t) : d ≤ 0 := by
  have ht := hd.tendsto_slope.mono_left (nhdsWithin_mono t (by
    intro s hs; exact ne_of_lt hs : Iio t ⊆ {t}ᶜ))
  apply le_of_tendsto ht
  filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (a := a) hat), self_mem_nhdsWithin] with s ha hs
  rw [slope_def_field]
  exact div_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (hm s ⟨ha.le,hs.le⟩))
    (sub_nonpos.mpr hs.le)

lemma square_norm_difference_bound {E : Type uE} [NormedAddCommGroup E]
    {p q : E} {L b r : ℝ} (_hL : 0 ≤ L) (hb : 0 ≤ b) (hr : 0 ≤ r)
    (hp : ‖p‖ ≤ L) (hq : ‖q‖ ≤ L) (hpq : ‖p-q‖ ≤ 2*b*r) :
    |‖p‖^2-‖q‖^2| ≤ 4*L*b*r := by
  have hn := abs_norm_sub_norm_le p q
  have heq : ‖p‖^2-‖q‖^2 = (‖p‖-‖q‖)*(‖p‖+‖q‖) := by ring
  rw [heq, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ‖p‖+‖q‖)]
  calc
    _ ≤ (2*b*r)*(2*L) := mul_le_mul (hn.trans hpq) (by linarith) (by positivity) (by positivity)
    _ = _ := by ring

lemma weighted_linear_le_quadratic {a b r s : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a+b=1) : a*r+b*s ≤ 1+a*r^2+b*s^2 := by
  have hr : r ≤ 1+r^2 := by nlinarith only [sq_nonneg (r-1/2)]
  have hs : s ≤ 1+s^2 := by nlinarith only [sq_nonneg (s-1/2)]
  nlinarith only [mul_le_mul_of_nonneg_left hr ha, mul_le_mul_of_nonneg_left hs hb, hab]

lemma reaction_bound {E : Type uE} [NormedAddCommGroup E]
    {p₀ p₁ p₂ : E} {a b σ L M r s v₀ v₁ v₂ : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) (hσ : 0 ≤ σ)
    (hL : 0 ≤ L) (hM : 0 ≤ M) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hp₀ : ‖p₀‖ ≤ L) (hp₁ : ‖p₁‖ ≤ L) (hp₂ : ‖p₂‖ ≤ L)
    (hv₁ : |v₁| ≤ M+L*r) (hv₂ : |v₂| ≤ M+L*s)
    (hp₁₀ : ‖p₀-p₁‖ ≤ 2*σ*r) (hp₂₀ : ‖p₀-p₂‖ ≤ 2*σ*s)
    (hdef : v₀-a*v₁-b*v₂+σ*(1+a*r^2+b*s^2) ≤ 0) :
    v₀*‖p₀‖^2-a*v₁*‖p₁‖^2-b*v₂*‖p₂‖^2 ≤
      4*L*σ*(M+L)*(1+a*r^2+b*s^2) := by
  have h1 := square_norm_difference_bound hL hσ hr hp₀ hp₁ hp₁₀
  have h2 := square_norm_difference_bound hL hσ hs hp₀ hp₂ hp₂₀
  have hv : v₀-a*v₁-b*v₂ ≤ 0 := by
    have : 0 ≤ σ*(1+a*r^2+b*s^2) := by positivity
    linarith only [hdef,this]
  have hh1 : v₁*(‖p₀‖^2-‖p₁‖^2) ≤ (M+L*r)*(4*L*σ*r) := by
    calc
      _ ≤ |v₁*(‖p₀‖^2-‖p₁‖^2)| := le_abs_self _
      _ = |v₁| * |‖p₀‖^2-‖p₁‖^2| := abs_mul _ _
      _ ≤ _ := mul_le_mul hv₁ h1 (abs_nonneg _) (by positivity)
  have hh2 : v₂*(‖p₀‖^2-‖p₂‖^2) ≤ (M+L*s)*(4*L*σ*s) := by
    calc
      _ ≤ |v₂*(‖p₀‖^2-‖p₂‖^2)| := le_abs_self _
      _ = |v₂| * |‖p₀‖^2-‖p₂‖^2| := abs_mul _ _
      _ ≤ _ := mul_le_mul hv₂ h2 (abs_nonneg _) (by positivity)
  have hb1 := mul_le_mul_of_nonneg_left hh1 ha
  have hb2 := mul_le_mul_of_nonneg_left hh2 hb
  have hb0 := mul_nonpos_of_nonpos_of_nonneg hv (sq_nonneg ‖p₀‖)
  have hc := weighted_linear_le_quadratic ha hb hab (r := r) (s := s)
  have hc' : M*(a*r+b*s)+L*(a*r^2+b*s^2) ≤ (M+L)*(1+a*r^2+b*s^2) := by
    nlinarith only [mul_le_mul_of_nonneg_left hc hM,hL]
  have hc'' := mul_le_mul_of_nonneg_left hc' (by positivity : 0 ≤ 4*L*σ)
  nlinarith only [hb0,hb1,hb2,hc'']

section Spatial
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma hasDerivAt_line {v : E → ℝ} {p : E → E}
    (hp : ∀ x, HasFDerivAt v (innerSL ℝ (p x)) x) (x e : E) (s : ℝ) :
    HasDerivAt (fun s : ℝ => v (x+s • e)) (⟪p (x+s • e),e⟫) s := by
  convert (hp (x+s • e)).comp_hasDerivAt s
    (((hasDerivAt_id s).smul_const e).const_add x) using 1 <;> first | rfl | simp

lemma min_gradient_left {v : E → ℝ} {p : E → E} {a b σ : ℝ} {x y : E}
    (hp : ∀ x, HasFDerivAt v (innerSL ℝ (p x)) x) (ha : 0 < a)
    (hm : ∀ x' y', deficit v a b σ x y ≤ deficit v a b σ x' y') :
    p (a • x+b • y)-p x = -(2*σ) • x := by
  let e := p (a • x+b • y)-p x+(2*σ) • x
  have hm' : IsLocalMin (fun s : ℝ => deficit v a b σ (x+s • e) y) 0 := by
    apply Filter.Eventually.of_forall
    intro s
    simpa only [zero_smul, add_zero] using hm (x+s • e) y
  have hz : HasDerivAt (fun s : ℝ => v (a • (x+s • e)+b • y))
      (a*⟪p (a • x+b • y),e⟫) 0 := by
    have hpath : HasDerivAt (fun s : ℝ => a • (x+s • e)+b • y) (a • e) 0 := by
      convert ((((hasDerivAt_id (0:ℝ)).smul_const e).const_add x).const_smul a).add_const (b • y) using 1 <;> simp
    convert (hp (a • (x+(0:ℝ) • e)+b • y)).comp_hasDerivAt 0 hpath using 1 <;>
      first | rfl | simp [innerSL_apply_apply]
  have hx := hasDerivAt_line hp x e 0
  have hn := (((hasDerivAt_id (0:ℝ)).smul_const e).const_add x).norm_sq
  have hd := ((hz.sub (hx.const_mul a)).sub_const (b*v y)).add
    (((hn.const_mul a).const_add 1 |>.add_const (b*‖y‖^2)).const_mul σ)
  have hzero := hm'.hasDerivAt_eq_zero hd
  have hei : ⟪e,e⟫ = ⟪p (a • x+b • y),e⟫-⟪p x,e⟫+(2*σ)*⟪x,e⟫ := by
    change ⟪p (a • x+b • y)-p x+(2*σ) • x,e⟫ = _
    simp only [inner_add_left, inner_sub_left, real_inner_smul_left]
  rw [real_inner_self_eq_norm_sq] at hei
  have he : a*‖e‖^2 = 0 := by
    simp only [zero_smul, add_zero, id_eq, one_smul] at hzero
    rw [hei]
    nlinarith only [hzero]
  have he0 : e = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp ((mul_eq_zero.mp he).resolve_left ha.ne'))
  dsimp only [e] at he0
  simpa only [neg_smul] using eq_neg_iff_add_eq_zero.mpr he0

lemma min_gradient_right {v : E → ℝ} {p : E → E} {a b σ : ℝ} {x y : E}
    (hp : ∀ x, HasFDerivAt v (innerSL ℝ (p x)) x) (hb : 0 < b)
    (hm : ∀ x' y', deficit v a b σ x y ≤ deficit v a b σ x' y') :
    p (a • x+b • y)-p y = -(2*σ) • y := by
  have hs (x y : E) : deficit v b a σ y x = deficit v a b σ x y := by
    unfold deficit
    rw [add_comm (b • y) (a • x)]
    ring
  have hh := min_gradient_left hp hb (x := y) (y := x) (a := b) (b := a)
    (fun y' x' => by rw [hs,hs]; exact hm x' y')
  simpa only [add_comm (b • y) (a • x)] using hh

lemma min_hessian_diagonal {v : E → ℝ} {p : E → E} {H : E → E → ℝ}
    {a b σ : ℝ} {x y : E} (hab : a+b=1)
    (hp : ∀ x, HasFDerivAt v (innerSL ℝ (p x)) x)
    (hH : ∀ x e, HasDerivAt (fun s : ℝ => ⟪p (x+s • e),e⟫) (H x e) 0)
    (hm : ∀ x' y', deficit v a b σ x y ≤ deficit v a b σ x' y') (e : E) :
    0 ≤ H (a • x+b • y) e-a*H x e-b*H y e+2*σ*‖e‖^2 := by
  let z := a • x+b • y
  have hz (s : ℝ) : a • (x+s • e)+b • (y+s • e) = z+s • e := by
    dsimp only [z]
    simp only [smul_add, smul_smul]
    rw [add_add_add_comm, ← add_smul, ← add_mul, hab, one_mul]
  let F (s : ℝ) := v (z+s • e)-a*v (x+s • e)-b*v (y+s • e)+
    σ*(1+a*‖x+s • e‖^2+b*‖y+s • e‖^2)
  let G (s : ℝ) := ⟪p (z+s • e),e⟫-a*⟪p (x+s • e),e⟫-b*⟪p (y+s • e),e⟫+
    σ*(a*(2*⟪x+s • e,e⟫)+b*(2*⟪y+s • e,e⟫))
  have hf (s : ℝ) : HasDerivAt F (G s) s := by
    have hx := (((hasDerivAt_id s).smul_const e).const_add x).norm_sq
    have hy := (((hasDerivAt_id s).smul_const e).const_add y).norm_sq
    convert (((hasDerivAt_line hp z e s).sub ((hasDerivAt_line hp x e s).const_mul a)).sub
      ((hasDerivAt_line hp y e s).const_mul b)).add
      ((((hx.const_mul a).const_add 1).add (hy.const_mul b)).const_mul σ) using 1 <;>
      first | rfl | simp [G]
  have hi (x : E) : HasDerivAt (fun s : ℝ => ⟪x+s • e,e⟫) (‖e‖^2) 0 := by
    convert ((((hasDerivAt_id (0:ℝ)).smul_const e).const_add x).inner (𝕜 := ℝ)
      (hasDerivAt_const (0:ℝ) e)) using 1 <;> first | rfl | simp
  have hg : HasDerivAt G (H z e-a*H x e-b*H y e+2*σ*‖e‖^2) 0 := by
    convert (((hH z e).sub ((hH x e).const_mul a)).sub ((hH y e).const_mul b)).add
      ((((hi x).const_mul 2 |>.const_mul a).add ((hi y).const_mul 2 |>.const_mul b)).const_mul σ) using 1
    all_goals first | rfl | (have hh := congrArg (fun u : ℝ => 2*σ*‖e‖^2*u) hab; nlinarith only [hh])
  have hmin : IsLocalMin F 0 := by
    apply Filter.Eventually.of_forall
    intro s
    simpa only [deficit,hz,zero_smul,add_zero,F,z] using hm (x+s • e) (y+s • e)
  exact second_deriv_nonneg_of_localMin hf hg hmin

lemma min_laplacian_bound {ι : Type uι} [Fintype ι] (basis : ι → E)
    (hbasis : ∀ i, ‖basis i‖ = 1)
    {v : E → ℝ} {p : E → E} {H : E → E → ℝ}
    {a b σ : ℝ} {x y : E} (hab : a+b=1)
    (hp : ∀ x, HasFDerivAt v (innerSL ℝ (p x)) x)
    (hH : ∀ x e, HasDerivAt (fun s : ℝ => ⟪p (x+s • e),e⟫) (H x e) 0)
    (hm : ∀ x' y', deficit v a b σ x y ≤ deficit v a b σ x' y') :
    -2*σ*(Fintype.card ι : ℝ) ≤
      (∑ i, H (a • x+b • y) (basis i))-a*(∑ i, H x (basis i))-b*(∑ i, H y (basis i)) := by
  have hh := Finset.sum_nonneg (fun (i : ι) (_ : i ∈ Finset.univ) =>
    min_hessian_diagonal hab hp hH hm (basis i))
  simp only [hbasis,one_pow,mul_one,Finset.sum_add_distrib,Finset.sum_sub_distrib,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hh
  linarith only [hh]

lemma no_forbidden_minimum {ι : Type uι} [Fintype ι] (basis : ι → E)
    (hbasis : ∀ i, ‖basis i‖ = 1)
    {v : ℝ → E → ℝ} {p : E → E} {H : E → E → ℝ} {σf : ℝ → ℝ}
    {a b L M t : ℝ} {x y : E} (ha : 0 < a) (hb : 0 < b) (hab : a+b=1)
    (hL : 0 ≤ L) (hM : 0 ≤ M) (ht : 0 < t) (hσ : 0 < σf t)
    (hp : ∀ x, HasFDerivAt (v t) (innerSL ℝ (p x)) x)
    (hH : ∀ x e, HasDerivAt (fun s : ℝ => ⟪p (x+s • e),e⟫) (H x e) 0)
    (hvt : ∀ x, HasDerivAt (fun s => v s x)
      (((∑ i, H x (basis i))-v t x*‖p x‖^2)/2) t)
    (hσt : HasDerivAt σf (((Fintype.card ι : ℝ)+2*L*(M+L)+1)*σf t) t)
    (hpbound : ∀ x, ‖p x‖ ≤ L) (hvbound : ∀ x, |v t x| ≤ M+L*‖x‖)
    (hm : ∀ x' y', deficit (v t) a b (σf t) x y ≤ deficit (v t) a b (σf t) x' y')
    (hmTime : ∀ s ∈ Icc 0 t, deficit (v t) a b (σf t) x y ≤ deficit (v s) a b (σf s) x y)
    (hneg : deficit (v t) a b (σf t) x y ≤ 0) : False := by
  let z := a • x+b • y
  have hx := min_gradient_left hp ha hm
  have hy := min_gradient_right hp hb hm
  have hxnorm : ‖p z-p x‖ ≤ 2*(σf t)*‖x‖ := by
    rw [hx,norm_smul,Real.norm_eq_abs,abs_neg,abs_of_pos (by positivity)]
  have hynorm : ‖p z-p y‖ ≤ 2*(σf t)*‖y‖ := by
    rw [hy,norm_smul,Real.norm_eq_abs,abs_neg,abs_of_pos (by positivity)]
  have hr := reaction_bound ha.le hb.le hab hσ.le hL hM (norm_nonneg x) (norm_nonneg y)
    (hpbound z) (hpbound x) (hpbound y) (hvbound x) (hvbound y) hxnorm hynorm hneg
  have hl := min_laplacian_bound basis hbasis hab hp hH hm
  have hd : HasDerivAt (fun s => deficit (v s) a b (σf s) x y)
      ((((∑ i, H z (basis i))-v t z*‖p z‖^2)/2) -
       a*(((∑ i, H x (basis i))-v t x*‖p x‖^2)/2) -
       b*(((∑ i, H y (basis i))-v t y*‖p y‖^2)/2) +
       (((Fintype.card ι : ℝ)+2*L*(M+L)+1)*σf t)*(1+a*‖x‖^2+b*‖y‖^2)) t := by
    exact (((hvt z).sub ((hvt x).const_mul a)).sub ((hvt y).const_mul b)).add
      (hσt.mul_const _)
  have hnonpos := deriv_nonpos_of_min_on_left ht hmTime hd
  have hQ : 0 ≤ a*‖x‖^2+b*‖y‖^2 := by positivity
  have hcard : 0 ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  have hσQ : 0 ≤ σf t*(a*‖x‖^2+b*‖y‖^2) := mul_nonneg hσ.le hQ
  have hcardQ : 0 ≤ (Fintype.card ι : ℝ)*(σf t*(a*‖x‖^2+b*‖y‖^2)) :=
    mul_nonneg hcard hσQ
  change -2*(σf t)*(Fintype.card ι : ℝ) ≤
    (∑ i, H z (basis i))-a*(∑ i, H x (basis i))-b*(∑ i, H y (basis i)) at hl
  nlinarith only [hr,hl,hnonpos,hσ,hσQ,hcardQ]

lemma deficit_lower {v : E → ℝ} {a b σ L M ε : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) (hL : 0 ≤ L)
    (hε : 0 < ε) (hσε : ε ≤ σ) (hv : ∀ x, |v x| ≤ M+L*‖x‖) (x y : E) :
    ε/2*(a*‖x‖^2+b*‖y‖^2)-2*M-2*L^2/ε ≤ deficit v a b σ x y := by
  have hnz : ‖a • x+b • y‖ ≤ a*‖x‖+b*‖y‖ := by
    simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg ha,abs_of_nonneg hb] using norm_add_le (a • x) (b • y)
  have hvz := (abs_le.mp (hv (a • x+b • y))).1
  have hvx := (abs_le.mp (hv x)).2
  have hvy := (abs_le.mp (hv y)).2
  have hvz' : -(M+L*(a*‖x‖+b*‖y‖)) ≤ v (a • x+b • y) := by
    nlinarith only [hvz,mul_le_mul_of_nonneg_left hnz hL]
  have hQ : 0 ≤ a*‖x‖^2+b*‖y‖^2 := by positivity
  have hbarr := mul_le_mul_of_nonneg_right hσε (by positivity : 0 ≤ 1+a*‖x‖^2+b*‖y‖^2)
  have hYoung (r : ℝ) : 2*L*r ≤ ε/2*r^2+2*L^2/ε := by
    have hid : ε/2*r^2+2*L^2/ε-2*L*r = (ε*r-2*L)^2/(2*ε) := by
      field_simp
      ring
    have hh := div_nonneg (sq_nonneg (ε*r-2*L)) (by positivity : 0 ≤ 2*ε)
    rw [← hid] at hh
    linarith only [hh]
  have hx := mul_le_mul_of_nonneg_left (hYoung ‖x‖) ha
  have hy := mul_le_mul_of_nonneg_left (hYoung ‖y‖) hb
  have hi : (a+b)*(2*L^2/ε) = 2*L^2/ε := by rw [hab,one_mul]
  have hMab := congrArg (fun u : ℝ => M*u) hab
  unfold deficit
  nlinarith only [hMab,hvz',mul_le_mul_of_nonneg_left hvx ha,mul_le_mul_of_nonneg_left hvy hb,
    hbarr,hx,hy,hi,hε]

omit [InnerProductSpace ℝ E] in
lemma exists_negative_minimum [InnerProductSpace ℝ E] [ProperSpace E]
    {F : ℝ → E → E → ℝ} {T R : ℝ} {x₀ y₀ : E}
    (hF : Continuous (fun q : ℝ × E × E => F q.1 q.2.1 q.2.2))
    (hT : 0 ≤ T) (hnegative : F T x₀ y₀ < 0)
    (hinitial : ∀ x y, 0 ≤ F 0 x y)
    (hcoercive : ∀ t ∈ Icc 0 T, ∀ x y,
      R ≤ ‖x‖ ∨ R ≤ ‖y‖ → 0 ≤ F t x y) :
    ∃ t ∈ Ioc 0 T, ∃ x y, F t x y < 0 ∧
      (∀ x' y', F t x y ≤ F t x' y') ∧
      (∀ s ∈ Icc 0 t, F t x y ≤ F s x y) := by
  let K := Icc 0 T ×ˢ (Metric.closedBall (0:E) R ×ˢ Metric.closedBall (0:E) R)
  have hx₀ : ‖x₀‖ ≤ R := by
    by_contra hh
    exact (not_lt_of_ge (hcoercive T ⟨hT,le_rfl⟩ x₀ y₀ (Or.inl (le_of_not_ge hh)))) hnegative
  have hy₀ : ‖y₀‖ ≤ R := by
    by_contra hh
    exact (not_lt_of_ge (hcoercive T ⟨hT,le_rfl⟩ x₀ y₀ (Or.inr (le_of_not_ge hh)))) hnegative
  have hmem : (T,x₀,y₀) ∈ K := by
    exact ⟨⟨hT,le_rfl⟩, by simpa using hx₀, by simpa using hy₀⟩
  have hK : IsCompact K := isCompact_Icc.prod ((isCompact_closedBall (0:E) R).prod (isCompact_closedBall (0:E) R))
  obtain ⟨w, hw, hmin⟩ := hK.exists_isMinOn ⟨_,hmem⟩ hF.continuousOn
  have hn : F w.1 w.2.1 w.2.2 < 0 := (hmin hmem).trans_lt hnegative
  have ht0 : 0 < w.1 := by
    have ht : 0 ≤ w.1 := hw.1.1
    rcases ht.eq_or_lt with ht' | ht'
    · have hh := hinitial w.2.1 w.2.2
      rw [← ht'] at hn
      exact (not_lt_of_ge hh hn).elim
    · exact ht'
  refine ⟨w.1,⟨ht0,hw.1.2⟩,w.2.1,w.2.2,hn,?_,?_⟩
  · intro x y
    by_cases hx : ‖x‖ ≤ R
    · by_cases hy : ‖y‖ ≤ R
      · apply hmin (a := (w.1,x,y))
        exact ⟨hw.1,by simpa using hx,by simpa using hy⟩
      · exact hn.le.trans (hcoercive w.1 hw.1 x y (Or.inr (le_of_not_ge hy)))
    · exact hn.le.trans (hcoercive w.1 hw.1 x y (Or.inl (le_of_not_ge hx)))
  · intro s hs
    apply hmin (a := (s,w.2.1,w.2.2))
    exact ⟨⟨hs.1,hs.2.trans hw.1.2⟩,hw.2⟩

lemma deficit_coercive_radius {a b ε L M : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a+b=1) (hε : 0 < ε) (hL : 0 ≤ L) (hM : 0 ≤ M) :
    ∃ R : ℝ, ∀ (v : E → ℝ) (σ : ℝ), ε ≤ σ →
      (∀ x, |v x| ≤ M+L*‖x‖) → ∀ x y,
      R ≤ ‖x‖ ∨ R ≤ ‖y‖ → 0 ≤ deficit v a b σ x y := by
  let δ := min a b
  have hδ : 0 < δ := lt_min ha hb
  let C := 2*M+2*L^2/ε+1
  have hC : 0 < C := by dsimp only [C]; positivity
  let R := Real.sqrt (2*C/(ε*δ))
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hR2 : R^2 = 2*C/(ε*δ) := Real.sq_sqrt (by positivity)
  have hid : ε/2*δ*R^2-2*M-2*L^2/ε = 1 := by
    rw [hR2]
    dsimp only [C]
    field_simp
    ring
  refine ⟨R,?_⟩
  intro v σ hσε hv x y hout
  have hQ : δ*R^2 ≤ a*‖x‖^2+b*‖y‖^2 := by
    rcases hout with hx | hy
    · have hsq : R^2 ≤ ‖x‖^2 := sq_le_sq₀ hR (norm_nonneg x) |>.mpr hx
      nlinarith only [mul_le_mul_of_nonneg_left hsq hδ.le,
        mul_le_mul_of_nonneg_right (min_le_left a b) (sq_nonneg ‖x‖),
        mul_nonneg hb.le (sq_nonneg ‖y‖)]
    · have hsq : R^2 ≤ ‖y‖^2 := sq_le_sq₀ hR (norm_nonneg y) |>.mpr hy
      nlinarith only [mul_le_mul_of_nonneg_left hsq hδ.le,
        mul_le_mul_of_nonneg_right (min_le_right a b) (sq_nonneg ‖y‖),
        mul_nonneg ha.le (sq_nonneg ‖x‖)]
  have hh := deficit_lower ha.le hb.le hab hL hε hσε hv x y
  have hh' := mul_le_mul_of_nonneg_left hQ (by positivity : 0 ≤ ε/2)
  nlinarith only [hh,hh',hid]

lemma heat_deficit_nonneg [ProperSpace E] {ι : Type uι} [Fintype ι] (basis : ι → E)
    (hbasis : ∀ i, ‖basis i‖ = 1)
    {v : ℝ → E → ℝ} {p : ℝ → E → E} {H : ℝ → E → E → ℝ}
    {T a b ε L M : ℝ} (hT : 0 ≤ T) (ha : 0 < a) (hb : 0 < b) (hab : a+b=1)
    (hε : 0 < ε) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hv : Continuous (fun q : ℝ × E => v q.1 q.2))
    (hinitial : ConcaveOn ℝ univ (v 0))
    (hp : ∀ t ∈ Ioc 0 T, ∀ x, HasFDerivAt (v t) (innerSL ℝ (p t x)) x)
    (hH : ∀ t ∈ Ioc 0 T, ∀ x e, HasDerivAt (fun s : ℝ => ⟪p t (x+s • e),e⟫) (H t x e) 0)
    (hvt : ∀ t ∈ Ioc 0 T, ∀ x, HasDerivAt (fun s => v s x)
      (((∑ i, H t x (basis i))-v t x*‖p t x‖^2)/2) t)
    (hpbound : ∀ t ∈ Ioc 0 T, ∀ x, ‖p t x‖ ≤ L)
    (hvbound : ∀ t ∈ Icc 0 T, ∀ x, |v t x| ≤ M+L*‖x‖) (x y : E) :
    0 ≤ deficit (v T) a b (ε*Real.exp (((Fintype.card ι : ℝ)+2*L*(M+L)+1)*T)) x y := by
  let A := (Fintype.card ι : ℝ)+2*L*(M+L)+1
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let σf (t : ℝ) := ε*Real.exp (A*t)
  have hσcont : Continuous σf := by dsimp [σf]; fun_prop
  have hσpos (t : ℝ) : 0 < σf t := by dsimp [σf]; positivity
  have hσlower {t : ℝ} (ht : 0 ≤ t) : ε ≤ σf t := by
    have hh := Real.one_le_exp_iff.mpr (mul_nonneg hA ht)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hh hε.le
  have hσt (t : ℝ) : HasDerivAt σf (A*σf t) t := by
    convert ((((hasDerivAt_id t).const_mul A).exp).const_mul ε) using 1 <;>
      first | rfl | (dsimp [σf]; ring)
  obtain ⟨R,hR⟩ := deficit_coercive_radius (E := E) ha hb hab hε hL hM
  let F (t : ℝ) (x y : E) := deficit (v t) a b (σf t) x y
  have hF : Continuous (fun q : ℝ × E × E => F q.1 q.2.1 q.2.2) := by
    have hz : Continuous (fun q : ℝ × E × E => v q.1 (a • q.2.1+b • q.2.2)) :=
      hv.comp (show Continuous (fun q : ℝ × E × E => (q.1,a • q.2.1+b • q.2.2)) from by fun_prop)
    have hx : Continuous (fun q : ℝ × E × E => v q.1 q.2.1) := hv.comp (show Continuous (fun q : ℝ × E × E => (q.1,q.2.1)) from by fun_prop)
    have hy : Continuous (fun q : ℝ × E × E => v q.1 q.2.2) := hv.comp (show Continuous (fun q : ℝ × E × E => (q.1,q.2.2)) from by fun_prop)
    dsimp only [F,deficit]
    fun_prop
  have hi (x y : E) : 0 ≤ F 0 x y := by
    have hh := hinitial.2 (mem_univ x) (mem_univ y) ha.le hb.le hab
    simp only [smul_eq_mul] at hh
    have hh' : 0 ≤ σf 0*(1+a*‖x‖^2+b*‖y‖^2) := by positivity
    dsimp only [F,deficit]
    linarith only [hh,hh']
  have hc (t : ℝ) (ht : t ∈ Icc 0 T) (x y : E) (hout : R ≤ ‖x‖ ∨ R ≤ ‖y‖) :
      0 ≤ F t x y := hR (v t) (σf t) (hσlower ht.1) (hvbound t ht) x y hout
  by_contra hneg
  obtain ⟨t,ht,x',y',hn,hm,hmt⟩ := exists_negative_minimum hF hT (lt_of_not_ge hneg) hi hc
  exact no_forbidden_minimum basis hbasis ha hb hab hL hM ht.1 (hσpos t)
    (hp t ht) (hH t ht) (hvt t ht) (hσt t) (hpbound t ht) (hvbound t ⟨ht.1.le,ht.2⟩)
    hm hmt hn.le

lemma heat_concave [ProperSpace E] {ι : Type uι} [Fintype ι] (basis : ι → E)
    (hbasis : ∀ i, ‖basis i‖ = 1)
    {v : ℝ → E → ℝ} {p : ℝ → E → E} {H : ℝ → E → E → ℝ}
    {T L M : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hv : Continuous (fun q : ℝ × E => v q.1 q.2))
    (hinitial : ConcaveOn ℝ univ (v 0))
    (hp : ∀ t ∈ Ioc 0 T, ∀ x, HasFDerivAt (v t) (innerSL ℝ (p t x)) x)
    (hH : ∀ t ∈ Ioc 0 T, ∀ x e, HasDerivAt (fun s : ℝ => ⟪p t (x+s • e),e⟫) (H t x e) 0)
    (hvt : ∀ t ∈ Ioc 0 T, ∀ x, HasDerivAt (fun s => v s x)
      (((∑ i, H t x (basis i))-v t x*‖p t x‖^2)/2) t)
    (hpbound : ∀ t ∈ Ioc 0 T, ∀ x, ‖p t x‖ ≤ L)
    (hvbound : ∀ t ∈ Icc 0 T, ∀ x, |v t x| ≤ M+L*‖x‖) :
    ConcaveOn ℝ univ (v T) := by
  refine ⟨convex_univ,?_⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  rcases ha.eq_or_lt with rfl | ha
  · have hb1 : b=1 := by linarith only [hab]
    simp [hb1]
  rcases hb.eq_or_lt with rfl | hb
  · have ha1 : a=1 := by linarith only [hab]
    simp [ha1]
  by_contra hbad
  have hbad' : 0 < a*v T x+b*v T y-v T (a • x+b • y) := by linarith only [lt_of_not_ge hbad]
  let c := Real.exp (((Fintype.card ι : ℝ)+2*L*(M+L)+1)*T)*(1+a*‖x‖^2+b*‖y‖^2)
  have hc : 0 < c := by dsimp only [c]; positivity
  let ε := (a*v T x+b*v T y-v T (a • x+b • y))/(2*c)
  have hε : 0 < ε := div_pos hbad' (by positivity)
  have hh := heat_deficit_nonneg basis hbasis hT ha hb hab hε hL hM hv hinitial hp hH hvt hpbound hvbound x y
  have heq : ε*c = (a*v T x+b*v T y-v T (a • x+b • y))/2 := by
    dsimp only [ε]
    field_simp
  dsimp only [deficit] at hh
  dsimp only [c] at heq
  nlinarith only [hh,heq,hbad']

end Spatial
end GaussianPropeller.HeatMaximum

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.SmoothedConcavity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uι

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace

open scoped NNReal
namespace GaussianPropeller.EhrhardSmooth
open GaussianPropeller.Quantile GaussianPropeller.QuantilePDE GaussianPropeller.HeatConvolution
variable {ι : Type uι} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι
local notation "γ" => stdGaussian E

lemma heat_mem {f : E → ℝ} (hf : Continuous f) (t : ℝ) (x : E) :
    heat (fun y => Φ (f y)) t x ∈ Ioo (0:ℝ) 1 := integral_Φ_mem (by fun_prop)

lemma continuous_qheat {f : E → ℝ} (hf : Continuous f) :
    Continuous (fun p : ℝ × E => qheat f p.1 p.2) := by
  have hh := continuous_heat (continuous_Φ.comp hf) (SmoothCDF.cdf_bound f)
  exact continuous_iff_continuousAt.mpr fun p =>
    (continuousAt_q (heat_mem hf p.1 p.2)).comp (f := fun p : ℝ × E => heat (fun y => Φ (f y)) p.1 p.2) hh.continuousAt

lemma qheat_zero (f : E → ℝ) (x : E) : qheat f 0 x = f x := by
  simp [qheat, heat, q_Φ]

lemma qheat_le {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (t : ℝ) (x y : E) :
    qheat f t x ≤ qheat f t y + L*‖x-y‖ := by
  have hc := hf.continuous
  have hfm : AEStronglyMeasurable (fun z : E => f (y+Real.sqrt t • z)) γ := by fun_prop
  have hxm : AEStronglyMeasurable (fun z : E => f (x+Real.sqrt t • z)) γ := by fun_prop
  have hxy (z : E) : f (x+Real.sqrt t • z) ≤ f (y+Real.sqrt t • z)+L*‖x-y‖ := by
    have hh := hf.dist_le_mul (x+Real.sqrt t • z) (y+Real.sqrt t • z)
    rw [Real.dist_eq, dist_eq_norm, add_sub_add_right_eq_sub] at hh
    linarith only [le_abs_self (f (x+Real.sqrt t • z)-f (y+Real.sqrt t • z)), hh]
  have hint : (∫ z : E, Φ (f (x+Real.sqrt t • z)) ∂γ) ≤
      ∫ z : E, Φ (f (y+Real.sqrt t • z)+L*‖x-y‖) ∂γ :=
    integral_mono (integrable_Φ_comp hxm) (integrable_Φ_comp (hfm.add_const _))
      (fun z => strictMono_Φ.monotone (hxy z))
  exact (strictMonoOn_q.monotoneOn (integral_Φ_mem hxm)
    (integral_Φ_mem (hfm.add_const _)) hint).trans (quantile_shift_le hfm (by positivity))

lemma qheat_lipschitz {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (t : ℝ) :
    LipschitzWith L (qheat f t) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, dist_eq_norm, abs_le]
  have hxy := qheat_le hf t x y
  have hyx := qheat_le hf t y x
  rw [norm_sub_rev y x] at hyx
  constructor <;> linarith only [hxy,hyx]

lemma growth_bound {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (T : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc 0 T, ∀ x, |qheat f t x| ≤ M+L*‖x‖ := by
  have hc : Continuous (fun t : ℝ => |qheat f t 0|) :=
    ((continuous_qheat hf.continuous).comp (continuous_id.prodMk continuous_const)).abs
  obtain ⟨M,hM⟩ := (isCompact_Icc.image hc).bddAbove
  refine ⟨max M 0, le_max_right _ _,?_⟩
  intro t ht x
  have hm : |qheat f t 0| ≤ max M 0 := (hM (mem_image_of_mem _ ht)).trans (le_max_left _ _)
  have hd := (qheat_lipschitz hf t).dist_le_mul x 0
  simp only [Real.dist_eq, dist_zero_right] at hd
  have hh := abs_sub_le (qheat f t x) (qheat f t 0) 0
  simp only [sub_zero] at hh
  linarith only [hh,hm,hd]

lemma qheat_concave {f : E → ℝ} {g : E → E} {K : E → E →L[ℝ] E}
    (hf : ∀ x, HasFDerivAt f (innerSL ℝ (g x)) x)
    (hg : ∀ x, HasFDerivAt g (K x) x) (hK : Continuous K)
    {L : ℝ≥0} {D : ℝ} (hL : ∀ x, ‖g x‖ ≤ L) (hD : ∀ x, ‖K x‖ ≤ D)
    (hconc : ConcaveOn ℝ univ f) {T : ℝ} (hT : 0 ≤ T) :
    ConcaveOn ℝ univ (qheat f T) := by
  have hcf : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)
  have hcg : Continuous g := continuous_iff_continuousAt.mpr (fun x => (hg x).continuousAt)
  have hlip : LipschitzWith L f := lipschitzWith_of_nnnorm_fderiv_le
    (fun x => (hf x).differentiableAt) (fun x => by
      rw [(hf x).fderiv]
      exact_mod_cast (show ‖innerSL ℝ (g x)‖ ≤ L by rw [innerSL_apply_norm]; exact hL x))
  let F : E → ℝ := fun x => Φ (f x)
  let G : E → E := SmoothCDF.grad f g
  let J : E → E →L[ℝ] E := SmoothCDF.hess f g K
  have hF (x : E) : HasFDerivAt F (innerSL ℝ (G x)) x := SmoothCDF.fderiv hf x
  have hG (x : E) : HasFDerivAt G (J x) x := SmoothCDF.grad_fderiv hf hg x
  have hcG : Continuous G := continuous_iff_continuousAt.mpr (fun x => (hG x).continuousAt)
  have hcJ : Continuous J := SmoothCDF.continuous_hess hcf hcg hK
  have hFB (x : E) : ‖F x‖ ≤ 1 := SmoothCDF.cdf_bound f x
  have hGB (x : E) : ‖G x‖ ≤ φ 0*L := SmoothCDF.grad_bound hL x
  have hJB (x : E) : ‖J x‖ ≤ φ 0*(D+(L:ℝ)^2) := SmoothCDF.hess_bound L.coe_nonneg hL hD x
  let u : ℝ → E → ℝ := heat F
  let v : ℝ → E → ℝ := qheat f
  let p : ℝ → E → E := fun t x => (φ (v t x))⁻¹ • heat G t x
  let H : ℝ → E → E → ℝ := fun t x e =>
    (φ (v t x))⁻¹*⟪heat J t x e,e⟫ + v t x*(φ (v t x))⁻¹^2*⟪heat G t x,e⟫^2
  have hu (t : ℝ) (x : E) : u t x ∈ Ioo (0:ℝ) 1 := heat_mem hcf t x
  have hdu (t : ℝ) (x : E) : HasFDerivAt (u t) (innerSL ℝ (heat G t x)) x :=
    heat_gradient hF hcG hFB hGB t x
  have hdg (t : ℝ) (x : E) : HasFDerivAt (heat G t) (heat J t x) x :=
    fderiv_heat hG hcJ hGB hJB t x
  have hdv (t : ℝ) (x : E) : HasFDerivAt (v t) (innerSL ℝ (p t x)) x :=
    quantile_fderiv (hu t x) (hdu t x)
  obtain ⟨M,hM,hgrowth⟩ := growth_bound hlip T
  apply HeatMaximum.heat_concave (EuclideanSpace.basisFun ι ℝ)
    (fun i => (EuclideanSpace.basisFun ι ℝ).orthonormal.norm_eq_one i)
    (p := p) (H := H) hT L.coe_nonneg hM (continuous_qheat hcf)
  · change ConcaveOn ℝ univ (qheat f 0)
    rw [show qheat f 0 = f from funext (qheat_zero f)]
    exact hconc
  · intro t _ x; exact hdv t x
  · intro t _ x e
    exact quantile_gradient_line_derivative (hu t) (hdu t) (hdg t) x e
  · intro t ht x
    have hh := (hasDerivAt_q (hu t x)).comp t (heat_equation hF hG hcJ hFB hGB hJB ht.1 x)
    have heq := trace_quantile_hessian (EuclideanSpace.basisFun ι ℝ)
      (v t x) ((φ (v t x))⁻¹) (heat G t x) (heat J t x)
    change HasDerivAt (fun s => q (u s x))
      (((∑ i : ι, H t x (EuclideanSpace.basisFun ι ℝ i))-v t x*‖p t x‖^2)/2) t
    convert hh using 1 <;> try rfl
    change ((∑ i : ι, ((φ (v t x))⁻¹*⟪heat J t x (EuclideanSpace.basisFun ι ℝ i),
      EuclideanSpace.basisFun ι ℝ i⟫ + v t x*(φ (v t x))⁻¹^2*⟪heat G t x,
      EuclideanSpace.basisFun ι ℝ i⟫^2))-v t x*‖(φ (v t x))⁻¹ • heat G t x‖^2)/2 = _
    rw [heq]
    change (φ (q (u t x)))⁻¹*(∑ i : ι, ⟪heat J t x (EuclideanSpace.basisFun ι ℝ i),
      EuclideanSpace.basisFun ι ℝ i⟫)/2 = _
    ring
  · intro t _ x
    have hh := (hdv t x).le_of_lipschitz (qheat_lipschitz hlip t)
    simpa only [innerSL_apply_norm] using hh
  · exact hgrowth

end GaussianPropeller.EhrhardSmooth

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.SoftMinimum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uι

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal

open Set Filter
open scoped Topology RealInnerProductSpace NNReal
namespace GaussianPropeller.SoftMin

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type uι} [Fintype ι] [Nonempty ι]

lemma Z_pos (v : ι → E) (x : E) : 0 < Z v x :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
lemma weight_pos (v : ι → E) (x : E) (i : ι) : 0 < weight v x i :=
  div_pos (Real.exp_pos _) (Z_pos v x)
lemma sum_weight (v : ι → E) (x : E) : ∑ i, weight v x i = 1 := by
  simp only [weight, ← Finset.sum_div]
  exact div_self (ne_of_gt (Z_pos v x))
omit [Nonempty ι] in
lemma continuous_Z [Nonempty ι] (v : ι → E) : Continuous (Z v) := by unfold Z; fun_prop
lemma continuous_weight (v : ι → E) (i : ι) : Continuous (fun x => weight v x i) := by
  exact (by fun_prop : Continuous (fun x : E => Real.exp (-⟪v i,x⟫))).div
    (continuous_Z v) (fun x => ne_of_gt (Z_pos v x))
lemma continuous_grad (v : ι → E) : Continuous (grad v) := by
  unfold grad
  exact continuous_finsetSum _ (fun i _ => (continuous_weight v i).smul continuous_const)
lemma continuous_hess (v : ι → E) : Continuous (hess v) := by
  unfold hess
  apply continuous_finsetSum
  intro i _
  have h := continuous_grad v
  have hw := continuous_weight v i
  fun_prop
omit [Nonempty ι] in
lemma inner_grad [Nonempty ι] (v : ι → E) (x e : E) :
    ⟪grad v x,e⟫ = ∑ i, weight v x i*⟪v i,e⟫ := by
  simp only [grad, sum_inner, real_inner_smul_left]
lemma Z_fderiv (v : ι → E) (x : E) :
    HasFDerivAt (Z v) (-(Z v x) • innerSL ℝ (grad v x)) x := by
  have hd (i : ι) : HasFDerivAt (fun y : E => Real.exp (-⟪v i,y⟫))
      (-Real.exp (-⟪v i,x⟫) • innerSL ℝ (v i)) x := by
    convert ((innerSL ℝ (v i)).hasFDerivAt.neg.exp) using 1 <;>
      (first | rfl | (ext y; simp))
  have hs := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => hd i)
  convert hs using 1 <;> try rfl
  ext e
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, sum_apply,
    inner_grad, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [weight]
  field_simp [ne_of_gt (Z_pos v x)]
lemma value_fderiv (v : ι → E) (x : E) :
    HasFDerivAt (value v) (innerSL ℝ (grad v x)) x := by
  have hh := ((Z_fderiv v x).log (ne_of_gt (Z_pos v x))).neg
  convert hh using 1 <;> (first | rfl | (ext y; simp [ne_of_gt (Z_pos v x)]))
lemma weight_fderiv (v : ι → E) (x : E) (i : ι) :
    HasFDerivAt (fun y => weight v y i)
      (weight v x i • innerSL ℝ (grad v x-v i)) x := by
  have hn := ((innerSL ℝ (v i)).hasFDerivAt (x := x)).neg.exp
  have hi := (hasDerivAt_inv (ne_of_gt (Z_pos v x))).comp_hasFDerivAt x (Z_fderiv v x)
  have hh := hn.mul hi
  convert hh using 1 <;> try rfl
  ext e
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, inner_sub_left,
    Pi.neg_apply, Function.comp_def, add_apply, neg_apply]
  dsimp only [weight]
  field_simp [ne_of_gt (Z_pos v x)]
  ring
lemma grad_fderiv (v : ι → E) (x : E) :
    HasFDerivAt (grad v) (hess v x) x := by
  have hd (i : ι) := (weight_fderiv v x i).smul_const (v i)
  have hs := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => hd i)
  convert hs using 1 <;> try rfl
  ext e
  simp [hess, smul_smul]

lemma grad_bound (v : ι → E) {L : ℝ} (hL : ∀ i, ‖v i‖ ≤ L) (x : E) : ‖grad v x‖ ≤ L := by
  calc
    ‖grad v x‖ ≤ ∑ i, ‖weight v x i • v i‖ := norm_sum_le _ _
    _ ≤ ∑ i, weight v x i*L := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (weight_pos v x i)]
      exact mul_le_mul_of_nonneg_left (hL i) (weight_pos v x i).le
    _ = L := by rw [← Finset.sum_mul, sum_weight, one_mul]

lemma hess_bound (v : ι → E) {L : ℝ} (hL0 : 0 ≤ L) (hL : ∀ i, ‖v i‖ ≤ L) (x : E) :
    ‖hess v x‖ ≤ 2*L^2 := by
  calc
    ‖hess v x‖ ≤ ∑ i, ‖weight v x i • ((innerSL ℝ (grad v x-v i)).smulRight (v i))‖ := norm_sum_le _ _
    _ ≤ ∑ i, weight v x i*(2*L^2) := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (weight_pos v x i),
        ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]
      apply mul_le_mul_of_nonneg_left _ (weight_pos v x i).le
      have hd : ‖grad v x-v i‖ ≤ 2*L := (norm_sub_le _ _).trans (by linarith [grad_bound v hL x, hL i])
      calc
        ‖grad v x-v i‖*‖v i‖ ≤ (2*L)*L := mul_le_mul hd (hL i) (norm_nonneg _) (by positivity)
        _ = _ := by ring
    _ = 2*L^2 := by rw [← Finset.sum_mul, sum_weight, one_mul]

lemma hess_nonpos (v : ι → E) (x e : E) : ⟪hess v x e,e⟫ ≤ 0 := by
  have hvariance : 0 ≤ ∑ i, weight v x i*(⟪v i,e⟫-⟪grad v x,e⟫)^2 :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (weight_pos v x i).le (sq_nonneg _))
  have heq : (∑ i, weight v x i*(⟪v i,e⟫-⟪grad v x,e⟫)^2) =
      -(∑ i, weight v x i*⟪grad v x-v i,e⟫*⟪v i,e⟫) := by
    simp_rw [inner_sub_left]
    have hp (i : ι) : weight v x i*(⟪v i,e⟫-⟪grad v x,e⟫)^2 +
        weight v x i*(⟪grad v x,e⟫-⟪v i,e⟫)*⟪v i,e⟫ =
        weight v x i*⟪grad v x,e⟫^2 - (weight v x i*⟪v i,e⟫)*⟪grad v x,e⟫ := by ring
    have hh := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => hp i)
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
      sum_weight, one_mul, ← inner_grad] at hh
    nlinarith only [hh]
  rw [heq] at hvariance
  unfold hess
  simp only [sum_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    sum_inner, real_inner_smul_left, innerSL_apply_apply, ← mul_assoc]
  linarith only [hvariance]

end GaussianPropeller.SoftMin

namespace GaussianPropeller.SoftMin
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma concave_of_hessian {f : E → ℝ} {g : E → E} {K : E → E →L[ℝ] E}
    (hf : ∀ x, HasFDerivAt f (innerSL ℝ (g x)) x)
    (hg : ∀ x, HasFDerivAt g (K x) x)
    (hK : ∀ x e, ⟪K x e,e⟫ ≤ 0) : ConcaveOn ℝ univ f := by
  refine ⟨convex_univ,?_⟩
  intro x _ y _ a b ha hb hab
  let d := y-x
  have hline (s : ℝ) : HasDerivAt (fun r : ℝ => x+r•d) d s := by
    simpa using ((hasDerivAt_id s).smul_const d).const_add x
  have hdf (s : ℝ) : HasDerivAt (fun r : ℝ => f (x+r•d)) ⟪g (x+s•d),d⟫ s := by
    simpa only [Function.comp_def, innerSL_apply_apply] using (hf (x+s•d)).comp_hasDerivAt s (hline s)
  have hdg (s : ℝ) : HasDerivAt (fun r : ℝ => ⟪g (x+r•d),d⟫) ⟪K (x+s•d) d,d⟫ s := by
    simpa using ((hg (x+s•d)).comp_hasDerivAt s (hline s)).inner ℝ (hasDerivAt_const s d)
  have hant : Antitone (fun s : ℝ => ⟪g (x+s•d),d⟫) := antitone_of_hasDerivAt_nonpos hdg (fun s => hK _ _)
  have hconc : ConcaveOn ℝ univ (fun s : ℝ => f (x+s•d)) :=
    Antitone.concaveOn_univ_of_deriv (fun s => (hdf s).differentiableAt) (by
      intro s t hst
      rw [(hdf s).deriv, (hdf t).deriv]
      exact hant hst)
  have hh := hconc.2 (mem_univ (0:ℝ)) (mem_univ (1:ℝ)) ha hb hab
  simp only [smul_eq_mul, mul_zero, mul_one, zero_add, zero_smul, add_zero, one_smul] at hh
  have heq : x+b•d = a•x+b•y := by
    dsimp [d]
    have haeq : a=1-b := by linarith only [hab]
    rw [haeq]
    module
  simpa only [heq, d, add_sub_cancel, smul_eq_mul] using hh

lemma value_concave {ι : Type uι} [Fintype ι] [Nonempty ι] (v : ι → E) :
    ConcaveOn ℝ univ (value v) := concave_of_hessian (value_fderiv v) (grad_fderiv v) (hess_nonpos v)

end GaussianPropeller.SoftMin

namespace GaussianPropeller.SoftMin
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type uι} [Fintype ι] [Nonempty ι]

omit [Nonempty ι] in
lemma value_le_score [Nonempty ι] (v : ι → E) (x : E) (i : ι) : value v x ≤ ⟪v i,x⟫ := by
  have hh : Real.exp (-⟪v i,x⟫) ≤ Z v x := by
    apply Finset.single_le_sum (f := fun j => Real.exp (-⟪v j,x⟫))
    · intro j _; exact (Real.exp_pos _).le
    · exact Finset.mem_univ i
  have hl := Real.log_le_log (Real.exp_pos _) hh
  rw [Real.log_exp] at hl
  dsimp only [value]
  linarith only [hl]

lemma value_tendsto_atBot (v : ι → E) (x : E) (i : ι) (hi : ⟪v i,x⟫ < 0) :
    Tendsto (fun n : ℕ => value (fun j => (n:ℝ) • v j) x) atTop atBot := by
  have hh : Tendsto (fun n : ℕ => (n:ℝ)*⟪v i,x⟫) atTop atBot :=
    tendsto_natCast_atTop_atTop.atTop_mul_const_of_neg hi
  apply tendsto_atBot_mono (fun n => ?_) hh
  simpa only [real_inner_smul_left] using value_le_score (fun j => (n:ℝ) • v j) x i

lemma value_tendsto_atTop (v : ι → E) (x : E) (hi : ∀ i, 0 < ⟪v i,x⟫) :
    Tendsto (fun n : ℕ => value (fun j => (n:ℝ) • v j) x) atTop atTop := by
  have hz : Tendsto (fun n : ℕ => Z (fun j => (n:ℝ) • v j) x) atTop (𝓝 0) := by
    have hh (i : ι) : Tendsto (fun n : ℕ => Real.exp (-(n:ℝ)*⟪v i,x⟫)) atTop (𝓝 0) := by
      apply Real.tendsto_exp_atBot.comp
      simpa only [neg_mul, mul_neg] using
        (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const_of_neg (neg_neg_of_pos (hi i))
    have ht := tendsto_finsetSum Finset.univ (fun i _ => hh i)
    simpa only [Z, real_inner_smul_left, neg_mul, Finset.sum_const_zero] using ht
  have hzn : Tendsto (fun n : ℕ => Z (fun j => (n:ℝ) • v j) x) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hz, Filter.Eventually.of_forall (fun n => Z_pos _ _)⟩
  exact tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp hzn)

end GaussianPropeller.SoftMin

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.ConeConcavity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX uι uκ

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal

namespace GaussianPropeller.EhrhardCone
open GaussianPropeller.Quantile GaussianPropeller.EhrhardSmooth
variable {ι : Type uι} {κ : Type uκ} [Fintype ι] [Fintype κ] [Nonempty κ]
local notation "E" => EuclideanSpace ℝ ι
local notation "γ" => stdGaussian E

omit [Nonempty κ] in
lemma measurableSet_shifted [Nonempty κ] (v : κ → E) (x : E) : MeasurableSet (shifted v x) := by
  change MeasurableSet {y : E | ∀ i, 0 ≤ ⟪v i,x+y⟫}
  simpa only [ofPred_forall] using MeasurableSet.iInter (fun i =>
    measurableSet_le (measurable_const : Measurable (fun _ : E => (0:ℝ)))
      (show Measurable (fun y : E => ⟪v i,x+y⟫) by fun_prop))

lemma gaussian_open_pos {U : Set E} (hU : IsOpen U) (hne : U.Nonempty) : 0 < γ U := by
  have hac : (volume : Measure E) ≪ γ := by
    rw [Translation.stdGaussian_density]
    exact withDensity_absolutelyContinuous' Translation.measurable_stdDensity.ennreal_ofReal.aemeasurable
      (ae_of_all _ (fun x => ne_of_gt (ENNReal.ofReal_pos.mpr (Translation.stdDensity_pos x))))
  by_contra! hz
  have heq : γ U = 0 := le_antisymm hz bot_le
  exact ne_of_gt (hU.measure_pos volume hne) (hac heq)

lemma prob_mem (v : κ → E) (e : E) (he : ∀ i, 0 < ⟪v i,e⟫) (x : E) :
    prob v x ∈ Ioo (0:ℝ) 1 := by
  let U : Set E := {y | ∀ i, 0 < ⟪v i,x+y⟫}
  have hU : IsOpen U := by
    simpa only [U, ofPred_forall] using isOpen_iInter_of_finite (fun i =>
      isOpen_lt (continuous_const : Continuous (fun _ : E => (0:ℝ)))
        (show Continuous (fun y : E => ⟪v i,x+y⟫) by fun_prop))
  have hn : U.Nonempty := ⟨e-x, by simpa only [U, mem_ofPred_eq, show x+(e-x)=e by abel] using he⟩
  have hs : U ⊆ shifted v x := fun y hy i => (hy i).le
  have hp : 0 < (γ).real (shifted v x) := ENNReal.toReal_pos
    (ne_of_gt ((gaussian_open_pos hU hn).trans_le (measure_mono hs))) (measure_ne_top _ _)
  obtain ⟨i⟩ := ‹Nonempty κ›
  have hv : v i ≠ 0 := by intro hh; simpa only [hh, inner_zero_left, lt_self_iff_false] using he i
  let V : Set E := {y | ⟪v i,x+y⟫ < 0}
  have hV : IsOpen V := isOpen_lt (by fun_prop) continuous_const
  have hnV : V.Nonempty := by
    refine ⟨-v i-x,?_⟩
    change ⟪v i,x+(-v i-x)⟫ < 0
    rw [show x+(-v i-x)= -v i by abel, inner_neg_right]
    exact neg_neg_of_pos (real_inner_self_pos.mpr hv)
  have hsV : V ⊆ (shifted v x)ᶜ := by
    intro y hy hz
    exact (not_lt_of_ge (hz i)) hy
  have hc : 0 < (γ).real (shifted v x)ᶜ := ENNReal.toReal_pos
    (ne_of_gt ((gaussian_open_pos hV hnV).trans_le (measure_mono hsV))) (measure_ne_top _ _)
  rw [probReal_compl_eq_one_sub (measurableSet_shifted v x)] at hc
  exact ⟨hp, by change (γ).real (shifted v x) < 1; linarith only [hc]⟩

lemma gaussian_hyperplane_null (z : E) (hz : z ≠ 0) (c : ℝ) :
    γ {x | ⟪z,x⟫ = c} = 0 := by
  let L : StrongDual ℝ E := innerSL ℝ z
  have hL : L ≠ 0 := by
    intro heq
    have hx : ⟪z,z⟫ = 0 := by
      have h := DFunLike.congr_fun heq z
      simpa [L] using h
    exact hz (inner_self_eq_zero.mp hx)
  have hv : (variance L γ).toNNReal ≠ 0 := by
    rw [variance_dual_stdGaussian]
    exact ne_of_gt (Real.toNNReal_pos.mpr (sq_pos_of_pos (norm_pos_iff.mpr hL)))
  have instN : NullSingletonClass (gaussianReal (∫ x, L x ∂γ) (variance L γ).toNNReal) :=
    nullSingletonClass_gaussianReal hv
  have h := congrArg (fun μ : Measure ℝ => μ {c}) (IsGaussian.map_eq_gaussianReal (μ := γ) L)
  rw [Measure.map_apply L.continuous.measurable (measurableSet_singleton c), measure_singleton] at h
  exact h

omit [Nonempty κ] in
lemma ae_no_boundary [Nonempty κ] (v : κ → E) (hv : ∀ i, v i ≠ 0) (x : E) :
    ∀ᵐ y ∂γ, ∀ i, ⟪v i,x+y⟫ ≠ 0 := by
  apply ae_all_iff.mpr
  intro i
  have hh := gaussian_hyperplane_null (v i) (hv i) (-⟪v i,x⟫)
  have hh' : ∀ᵐ y ∂γ, ⟪v i,y⟫ ≠ -⟪v i,x⟫ := by
    rw [ae_iff]
    simpa only [not_not] using hh
  filter_upwards [hh'] with y hy
  rw [inner_add_right]
  intro hzero
  apply hy
  linarith only [hzero]

lemma cdf_softmin_limit (v : κ → E) (y : E) (hy : ∀ i, ⟪v i,y⟫ ≠ 0) :
    Tendsto (fun n : ℕ => Φ (SoftMin.value (fun i => (n:ℝ) • v i) y)) atTop
      (𝓝 ((cone v).indicator (fun _ => (1:ℝ)) y)) := by
  classical
  by_cases hmem : y ∈ cone v
  · rw [Set.indicator_of_mem hmem]
    exact tendsto_Φ_atTop.comp (SoftMin.value_tendsto_atTop v y
      (fun i => lt_of_le_of_ne (hmem i) (Ne.symm (hy i))))
  · rw [Set.indicator_of_notMem hmem]
    simp only [cone, mem_ofPred_eq, not_forall, not_le] at hmem
    obtain ⟨i,hi⟩ := hmem
    exact tendsto_Φ_atBot.comp (SoftMin.value_tendsto_atBot v y i hi)

lemma prob_limit (v : κ → E) (hv : ∀ i, v i ≠ 0) (x : E) :
    Tendsto (fun n : ℕ => HeatConvolution.heat
      (fun y => Φ (SoftMin.value (fun i => (n:ℝ) • v i) y)) 1 x) atTop (𝓝 (prob v x)) := by
  classical
  have hlim := tendsto_integral_of_dominated_convergence (μ := γ) (bound := fun _ : E => (1:ℝ))
    (F := fun n : ℕ => fun y : E => Φ (SoftMin.value (fun i => (n:ℝ) • v i) (x+y)))
    (f := fun y : E => (cone v).indicator (fun _ => (1:ℝ)) (x+y)) ?_ (integrable_const _) ?_ ?_
  · convert hlim using 1
    · funext n; simp only [HeatConvolution.heat, Real.sqrt_one, one_smul]
    · rw [show (fun y : E => (cone v).indicator (fun _ => (1:ℝ)) (x+y)) =
        (shifted v x).indicator (fun _ => (1:ℝ)) by
          funext y; rfl]
      rw [integral_indicator (measurableSet_shifted v x), setIntegral_const]
      simp only [prob, smul_eq_mul, mul_one]
  · intro n
    have hc : Continuous (SoftMin.value (fun i => (n:ℝ) • v i)) :=
      continuous_iff_continuousAt.mpr (fun y => (SoftMin.value_fderiv _ y).continuousAt)
    exact (continuous_Φ.comp (hc.comp (continuous_const.add continuous_id))).aestronglyMeasurable
  · intro n
    exact ae_of_all _ (fun y => SmoothCDF.cdf_bound _ _)
  · filter_upwards [ae_no_boundary v hv x] with y hy
    exact cdf_softmin_limit v (x+y) hy

lemma quantile_prob_concave_oai (v : κ → E) (e : E) (he : ∀ i, 0 < ⟪v i,e⟫) :
    ConcaveOn ℝ univ (fun x => q (prob v x)) := by
  have hv : ∀ i, v i ≠ 0 := by
    intro i hi; simpa only [hi, inner_zero_left, lt_self_iff_false] using he i
  have hc (n : ℕ) : ConcaveOn ℝ univ (qheat (SoftMin.value (fun i => (n:ℝ) • v i)) 1) := by
    let w : κ → E := fun i => (n:ℝ) • v i
    let L : ℝ≥0 := ∑ i, ‖w i‖₊
    have hL (i : κ) : ‖w i‖ ≤ L := by
      exact_mod_cast (Finset.single_le_sum (f := fun j => ‖w j‖₊) (fun j _ => bot_le) (Finset.mem_univ i))
    exact qheat_concave (SoftMin.value_fderiv w) (SoftMin.grad_fderiv w)
      (SoftMin.continuous_hess w) (SoftMin.grad_bound w hL)
      (SoftMin.hess_bound w L.coe_nonneg hL) (SoftMin.value_concave w) (by norm_num)
  have ht (x : E) : Tendsto (fun n : ℕ => qheat (SoftMin.value (fun i => (n:ℝ) • v i)) 1 x)
      atTop (𝓝 (q (prob v x))) := (continuousAt_q (prob_mem v e he x)).tendsto.comp (prob_limit v hv x)
  refine ⟨convex_univ,?_⟩
  intro x _ y _ a b ha hb hab
  exact le_of_tendsto_of_tendsto ((ht x).const_smul a |>.add ((ht y).const_smul b))
    (ht (a•x+b•y)) (Filter.Eventually.of_forall (fun n => (hc n).2 (mem_univ x) (mem_univ y) ha hb hab))

end GaussianPropeller.EhrhardCone

end OAI
end

theorem GaussLocalMaxColoring.Main.ehrhardQuantileConcaveVerified.{uι, uκ} : type_of% @OAI.GaussianPropeller.EhrhardCone.quantile_prob_concave_oai.{uι, uκ} := @OAI.GaussianPropeller.EhrhardCone.quantile_prob_concave_oai.{uι, uκ}


set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory Set

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem concave_extrapolation {E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : E→ℝ) (hf : ConcaveOn ℝ Set.univ f) (x₀ x₁ : E) (θ : ℝ) (hθ : 0 ≤ θ) :
    f ((1+θ) • x₀-θ • x₁) ≤ (1+θ)*f x₀-θ*f x₁ := by
  have hd : 0 < 1+θ := by linarith
  have ha : 0 ≤ 1/(1+θ) := by positivity
  have hb : 0 ≤ θ/(1+θ) := div_nonneg hθ hd.le
  have hab : 1/(1+θ)+θ/(1+θ)=1 := by field_simp
  have hc := hf.2 (Set.mem_univ ((1+θ) • x₀-θ • x₁)) (Set.mem_univ x₁) ha hb hab
  have hx : (1/(1+θ)) • ((1+θ) • x₀-θ • x₁)+(θ/(1+θ)) • x₁=x₀ := by
    rw [smul_sub,smul_smul,smul_smul]
    have h₁ : (1/(1+θ))*(1+θ)=1 := by field_simp
    have h₂ : (1/(1+θ))*θ=θ/(1+θ) := by ring
    rw [h₁,h₂,one_smul]
    module
  rw [hx] at hc
  have hm := mul_le_mul_of_nonneg_left hc hd.le
  have hEq : (1+θ)*(1/(1+θ)*f ((1+θ) • x₀-θ • x₁)+θ/(1+θ)*f x₁)=
      f ((1+θ) • x₀-θ • x₁)+θ*f x₁ := by field_simp
  change (1+θ)*(1/(1+θ)*f ((1+θ) • x₀-θ • x₁)+θ/(1+θ)*f x₁) ≤ (1+θ)*f x₀ at hm
  rw [hEq] at hm
  linarith

open OAI.GaussianPropeller

theorem ehrhard_cone_extrapolation {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty κ]
    (v : κ→EuclideanSpace ℝ ι) (e : EuclideanSpace ℝ ι)
    (he : ∀i,0 < ⟪v i,e⟫) (x₀ x₁ : EuclideanSpace ℝ ι) (μ κ₀ θ : ℝ) (hθ : 0 ≤ θ)
    (h₀ : EhrhardCone.prob v x₀ ≤ Quantile.Φ (-μ))
    (h₁ : Quantile.Φ κ₀ ≤ EhrhardCone.prob v x₁) :
    EhrhardCone.prob v ((1+θ) • x₀-θ • x₁) ≤ Quantile.Φ (-(μ+θ*(μ+κ₀))) := by
  have hcc := OAI.GaussianPropeller.EhrhardCone.quantile_prob_concave_oai v e he
  have hext := concave_extrapolation _ hcc x₀ x₁ θ hθ
  have hp₀ := EhrhardCone.prob_mem v e he x₀
  have hp₁ := EhrhardCone.prob_mem v e he x₁
  have hpt := EhrhardCone.prob_mem v e he ((1+θ) • x₀-θ • x₁)
  have hq₀ := Quantile.strictMonoOn_q.monotoneOn hp₀ (Quantile.Φ_mem (-μ)) h₀
  have hq₁ := Quantile.strictMonoOn_q.monotoneOn (Quantile.Φ_mem κ₀) hp₁ h₁
  rw [Quantile.q_Φ] at hq₀ hq₁
  have hqt : Quantile.q (EhrhardCone.prob v ((1+θ) • x₀-θ • x₁)) ≤ -(μ+θ*(μ+κ₀)) := by
    nlinarith
  have hF := Quantile.strictMono_Φ.monotone hqt
  simpa only [Quantile.Φ_q hpt] using hF

end
end GaussLocalMaxColoring.Main


set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory

namespace GaussLocalMaxColoring.Main
noncomputable section

def gaussianAugmentVector {ι : Type*} [Fintype ι] (w : EuclideanSpace ℝ ι) (a b c : ℝ) :
    EuclideanSpace ℝ (ι⊕Fin 3) := WithLp.toLp 2 (Sum.elim (fun i => w i) ![a,b,c])

def gaussianBaseProjection {ι : Type*} [Fintype ι] (g : EuclideanSpace ℝ (ι⊕Fin 3)) :
    EuclideanSpace ℝ ι := WithLp.toLp 2 (fun i => g (Sum.inl i))

@[simp] theorem gaussianAugmentVector_inl {ι : Type*} [Fintype ι]
    (w : EuclideanSpace ℝ ι) (a b c : ℝ) (i : ι) :
    gaussianAugmentVector w a b c (Sum.inl i)=w i := rfl

@[simp] theorem gaussianAugmentVector_inr {ι : Type*} [Fintype ι]
    (w : EuclideanSpace ℝ ι) (a b c : ℝ) (i : Fin 3) :
    gaussianAugmentVector w a b c (Sum.inr i)=![a,b,c] i := rfl

@[simp] theorem gaussianBaseProjection_apply {ι : Type*} [Fintype ι]
    (g : EuclideanSpace ℝ (ι⊕Fin 3)) (i : ι) : gaussianBaseProjection g i=g (Sum.inl i) := rfl

@[simp] theorem gaussianBaseProjection_augment {ι : Type*} [Fintype ι]
    (w : EuclideanSpace ℝ ι) (a b c : ℝ) :
    gaussianBaseProjection (gaussianAugmentVector w a b c)=w := by ext; rfl

theorem gaussianAugmentVector_inner {ι : Type*} [Fintype ι]
    (w : EuclideanSpace ℝ ι) (a b c : ℝ) (g : EuclideanSpace ℝ (ι⊕Fin 3)) :
    ⟪gaussianAugmentVector w a b c,g⟫=⟪w,gaussianBaseProjection g⟫+
      a*g (Sum.inr 0)+b*g (Sum.inr 1)+c*g (Sum.inr 2) := by
  simp only [PiLp.inner_apply,Fintype.sum_sum_type,RCLike.inner_apply,conj_trivial]
  change (∑i : ι,g (Sum.inl i)*w i)+(∑j : Fin 3,g (Sum.inr j)*![a,b,c] j)=
    (∑i : ι,g (Sum.inl i)*w i)+a*g (Sum.inr 0)+b*g (Sum.inr 1)+c*g (Sum.inr 2)
  rw [Fin.sum_univ_three]
  change (∑i : ι,g (Sum.inl i)*w i)+(g (Sum.inr 0)*a+g (Sum.inr 1)*b+g (Sum.inr 2)*c)=_
  ring

@[fun_prop] theorem gaussianBaseProjection_measurable {ι : Type*} [Fintype ι] :
    Measurable (gaussianBaseProjection (ι:=ι)) := by
  unfold gaussianBaseProjection
  fun_prop

theorem gaussianBaseProjection_map {ι : Type*} [Fintype ι] :
    (stdGaussian (EuclideanSpace ℝ (ι⊕Fin 3))).map gaussianBaseProjection=
      stdGaussian (EuclideanSpace ℝ ι) := by
  let μ : Measure ((ι⊕Fin 3)→ℝ) := Measure.pi (fun _ => gaussianReal 0 1)
  let P : ((ι⊕Fin 3)→ℝ)→(ι→ℝ) := fun g i => g (Sum.inl i)
  have hI : iIndepFun (fun p (g : (ι⊕Fin 3)→ℝ) => g p) μ := iIndepFun_pi (fun _ => aemeasurable_id)
  have hP : iIndepFun (fun i (g : (ι⊕Fin 3)→ℝ) => g (Sum.inl i)) μ :=
    iIndepFun.precomp Sum.inl_injective hI
  have hmap : μ.map P=Measure.pi (fun _ : ι => gaussianReal 0 1) := by
    rw [iIndepFun.map_fun_eq_pi_map (fun i => (measurable_pi_apply (Sum.inl i)).aemeasurable) hP]
    congr 1
    funext i
    exact (measurePreserving_eval (fun _ : ι⊕Fin 3 => gaussianReal 0 1) (Sum.inl i)).map_eq
  rw [← map_pi_eq_stdGaussian (ι:=ι⊕Fin 3),Measure.map_map gaussianBaseProjection_measurable (by fun_prop)]
  change μ.map ((WithLp.toLp 2) ∘ P)=stdGaussian (EuclideanSpace ℝ ι)
  rw [← Measure.map_map (by fun_prop) (by dsimp [P]; fun_prop),hmap,map_pi_eq_stdGaussian]

end
end GaussLocalMaxColoring.Main


set_option autoImplicit false
set_option maxHeartbeats 1000000

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace GaussLocalMaxColoring.Main
noncomputable section

def regularizationScale (n : ℕ) : ℝ := 1/((n:ℝ)+1)

theorem regularizationScale_pos (n : ℕ) : 0 < regularizationScale n := by
  unfold regularizationScale
  positivity

theorem regularizationScale_tendsto : Tendsto regularizationScale atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem regularized_inequality_eventually (a b : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      (a ≤ regularizationScale n+(regularizationScale n)^2*b ↔ a ≤ 0) := by
  have hzero : Tendsto (fun n => regularizationScale n+(regularizationScale n)^2*b) atTop (𝓝 0) := by
    simpa using regularizationScale_tendsto.add ((regularizationScale_tendsto.pow 2).mul_const b)
  have hone : Tendsto (fun n => 1+regularizationScale n*b) atTop (𝓝 1) := by
    simpa using (regularizationScale_tendsto.mul_const b).const_add 1
  have hpos : ∀ᶠ n : ℕ in atTop,0 < regularizationScale n+(regularizationScale n)^2*b := by
    filter_upwards [hone.eventually_const_lt (by norm_num : (0:ℝ)<1)] with n hn
    have hp := mul_pos (regularizationScale_pos n) hn
    nlinarith only [hp]
  by_cases ha : a ≤ 0
  · filter_upwards [hpos] with n hn
    exact ⟨fun _ => ha,fun _ => ha.trans hn.le⟩
  · have ha0 : 0 < a := lt_of_not_ge ha
    filter_upwards [hzero.eventually_lt_const ha0] with n hn
    exact ⟨fun h => False.elim ((not_le_of_gt hn) h),fun h => False.elim (ha h)⟩

def regularizedEvent {κ Ω : Type*} (f noise : κ→Ω→ℝ) (n : ℕ) : Set Ω :=
  {ω | ∀i,f i ω ≤ regularizationScale n+(regularizationScale n)^2*noise i ω}

def closedHalfspaceEvent {κ Ω : Type*} (f : κ→Ω→ℝ) : Set Ω := {ω | ∀i,f i ω ≤ 0}

theorem regularizedEvent_eventually {κ Ω : Type*} [Finite κ] (f noise : κ→Ω→ℝ) (ω : Ω) :
    ∀ᶠ n : ℕ in atTop,(ω∈regularizedEvent f noise n ↔ ω∈closedHalfspaceEvent f) := by
  have h : ∀i : κ,∀ᶠ n : ℕ in atTop,
      (f i ω ≤ regularizationScale n+(regularizationScale n)^2*noise i ω ↔ f i ω ≤ 0) :=
    fun i => regularized_inequality_eventually (f i ω) (noise i ω)
  filter_upwards [Filter.eventually_all.mpr h] with n hn
  change (∀i,f i ω ≤ regularizationScale n+(regularizationScale n)^2*noise i ω) ↔ ∀i,f i ω ≤ 0
  exact forall_congr' hn

theorem measurableSet_regularizedEvent {κ Ω : Type*} [Finite κ] [MeasurableSpace Ω]
    (f noise : κ→Ω→ℝ) (hf : ∀i,Measurable (f i)) (hnoise : ∀i,Measurable (noise i)) (n : ℕ) :
    MeasurableSet (regularizedEvent f noise n) := by
  apply measurableSet_setOfPred.mpr
  apply Measurable.forall
  intro i
  exact measurableSet_setOfPred.mp (measurableSet_le (hf i)
    (measurable_const.add (measurable_const.mul (hnoise i))))

theorem measurableSet_closedHalfspaceEvent {κ Ω : Type*} [Finite κ] [MeasurableSpace Ω]
    (f : κ→Ω→ℝ) (hf : ∀i,Measurable (f i)) : MeasurableSet (closedHalfspaceEvent f) := by
  apply measurableSet_setOfPred.mpr
  apply Measurable.forall
  intro i
  exact measurableSet_setOfPred.mp (measurableSet_le (hf i) measurable_const)

theorem regularizedEvent_probability_tendsto {κ Ω : Type*} [Finite κ] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f noise : κ→Ω→ℝ)
    (hf : ∀i,Measurable (f i)) (hnoise : ∀i,Measurable (noise i)) :
    Tendsto (fun n : ℕ => μ.real (regularizedEvent f noise n)) atTop
      (𝓝 (μ.real (closedHalfspaceEvent f))) := by
  have ht := tendsto_integral_of_dominated_convergence (μ:=μ) (bound:=fun _ : Ω => (1:ℝ))
    (F:=fun n : ℕ => (regularizedEvent f noise n).indicator (fun _ => (1:ℝ)))
    (f:=(closedHalfspaceEvent f).indicator (fun _ => (1:ℝ)))
    (fun n => measurable_const.aestronglyMeasurable.indicator (measurableSet_regularizedEvent f noise hf hnoise n))
    (integrable_const (1:ℝ)) (fun n => Eventually.of_forall (fun ω => by
      by_cases h : ω∈regularizedEvent f noise n <;> simp [h]))
    (Eventually.of_forall (fun ω =>
      (tendsto_indicator_const_apply_iff_eventually atTop (1:ℝ) ω).mpr
        (regularizedEvent_eventually f noise ω)))
  have hIntegral (A : Set Ω) (hA : MeasurableSet A) :
      (∫ω,A.indicator (fun _ => (1:ℝ)) ω ∂μ)=μ.real A := by
    simpa only [smul_eq_mul,mul_one] using integral_indicator_const (1:ℝ) hA
  simpa only [hIntegral _ (measurableSet_closedHalfspaceEvent f hf),
    hIntegral _ (measurableSet_regularizedEvent f noise hf hnoise _)] using ht

end
end GaussLocalMaxColoring.Main


set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory ProbabilityTheory Set
open OAI.GaussianPropeller

namespace GaussLocalMaxColoring.Main
noncomputable section

def polyhedralEvent {ι κ : Type*} [Fintype ι] (w : κ→EuclideanSpace ℝ ι) (A : κ→ℝ) :
    Set (EuclideanSpace ℝ ι) := {g | ∀i,⟪w i,g⟫ ≤ A i}

def regularizedNormals {ι κ : Type*} [Fintype ι]
    (w : κ→EuclideanSpace ℝ ι) (A B : κ→ℝ) (δ : ℝ) : κ→EuclideanSpace ℝ (ι⊕Fin 3) :=
  fun i => gaussianAugmentVector (-w i) (δ^2*A i) (δ^2*B i) (δ^2)

def regularizedTranslation {ι : Type*} [Fintype ι] (u v δ : ℝ) :
    EuclideanSpace ℝ (ι⊕Fin 3) := gaussianAugmentVector 0 (u/δ^2) (v/δ^2) (1/δ)

def regularizedNoise {ι κ : Type*} [Fintype ι] (A B : κ→ℝ) (i : κ)
    (g : EuclideanSpace ℝ (ι⊕Fin 3)) : ℝ :=
  A i*g (Sum.inr 0)+B i*g (Sum.inr 1)+g (Sum.inr 2)

theorem regularizedNormals_direction {ι κ : Type*} [Fintype ι]
    (w : κ→EuclideanSpace ℝ ι) (A B : κ→ℝ) (δ : ℝ) (hδ : 0 < δ) (i : κ) :
    0 < ⟪regularizedNormals w A B δ i,gaussianAugmentVector 0 0 0 1⟫ := by
  rw [regularizedNormals,gaussianAugmentVector_inner,gaussianBaseProjection_augment]
  simpa using sq_pos_of_pos hδ

theorem regularizedNormals_translation_inner {ι κ : Type*} [Fintype ι]
    (w : κ→EuclideanSpace ℝ ι) (A B : κ→ℝ) (u v δ : ℝ) (hδ : δ≠0) (i : κ) :
    ⟪regularizedNormals w A B δ i,regularizedTranslation (ι:=ι) u v δ⟫=
      u*A i+v*B i+δ := by
  rw [regularizedNormals,regularizedTranslation,gaussianAugmentVector_inner,gaussianBaseProjection_augment]
  simp only [inner_zero_right,zero_add,gaussianAugmentVector_inr]
  change (δ^2*A i)*(u/δ^2)+(δ^2*B i)*(v/δ^2)+δ^2*(1/δ)=u*A i+v*B i+δ
  field_simp

theorem regularizedNormals_shift_inner {ι κ : Type*} [Fintype ι]
    (w : κ→EuclideanSpace ℝ ι) (A B : κ→ℝ) (u v δ : ℝ) (hδ : δ≠0) (i : κ)
    (g : EuclideanSpace ℝ (ι⊕Fin 3)) :
    ⟪regularizedNormals w A B δ i,regularizedTranslation u v δ+g⟫=
      -(⟪w i,gaussianBaseProjection g⟫-(u*A i+v*B i))+δ+δ^2*regularizedNoise A B i g := by
  rw [inner_add_right,regularizedNormals_translation_inner w A B u v δ hδ i]
  rw [regularizedNormals,gaussianAugmentVector_inner]
  simp only [inner_neg_left]
  unfold regularizedNoise
  ring

theorem regularizedTranslation_extrapolate {ι : Type*} [Fintype ι] (δ θ : ℝ) (hδ : δ≠0) :
    regularizedTranslation (ι:=ι) (1+θ) (-θ) δ=
      (1+θ) • regularizedTranslation 1 0 δ-θ • regularizedTranslation 0 1 δ := by
  ext p
  cases p with
  | inl i => simp [regularizedTranslation]
  | inr i =>
    fin_cases i <;> simp [regularizedTranslation] <;> field_simp <;> ring

theorem measurableSet_polyhedralEvent {ι κ : Type*} [Fintype ι] [Finite κ]
    (w : κ→EuclideanSpace ℝ ι) (A : κ→ℝ) : MeasurableSet (polyhedralEvent w A) := by
  apply measurableSet_setOfPred.mpr
  apply Measurable.forall
  intro i
  exact measurableSet_setOfPred.mp (measurableSet_le (by fun_prop) measurable_const)

theorem regularized_probability_tendsto {ι κ : Type*} [Fintype ι] [Fintype κ]
    (w : κ→EuclideanSpace ℝ ι) (A B : κ→ℝ) (u v : ℝ) :
    Tendsto (fun n : ℕ => EhrhardCone.prob
      (regularizedNormals w A B (regularizationScale n))
      (regularizedTranslation (ι:=ι) u v (regularizationScale n))) atTop
      (𝓝 ((stdGaussian (EuclideanSpace ℝ ι)).real (polyhedralEvent w (fun i => u*A i+v*B i)))) := by
  let f : κ→EuclideanSpace ℝ (ι⊕Fin 3)→ℝ :=
    fun i g => ⟪w i,gaussianBaseProjection g⟫-(u*A i+v*B i)
  let noise : κ→EuclideanSpace ℝ (ι⊕Fin 3)→ℝ := regularizedNoise A B
  have hF : ∀i,Measurable (f i) := by intro i; dsimp [f]; fun_prop
  have hN : ∀i,Measurable (noise i) := by
    intro i
    change Measurable (fun g : EuclideanSpace ℝ (ι⊕Fin 3) =>
      A i*g (Sum.inr 0)+B i*g (Sum.inr 1)+g (Sum.inr 2))
    fun_prop
  have ht := regularizedEvent_probability_tendsto (stdGaussian (EuclideanSpace ℝ (ι⊕Fin 3)))
    f noise hF hN
  have heq (n : ℕ) : EhrhardCone.prob
      (regularizedNormals w A B (regularizationScale n))
      (regularizedTranslation u v (regularizationScale n))=
      (stdGaussian (EuclideanSpace ℝ (ι⊕Fin 3))).real (regularizedEvent f noise n) := by
    unfold EhrhardCone.prob
    congr 1
    ext g
    change (∀i,0 ≤ ⟪regularizedNormals w A B (regularizationScale n) i,
      regularizedTranslation u v (regularizationScale n)+g⟫) ↔ _
    simp only [regularizedNormals_shift_inner w A B u v _ (regularizationScale_pos n).ne',
      regularizedEvent,f,noise,Set.mem_setOf_eq]
    exact forall_congr' (fun i => by constructor <;> intro h <;> linarith)
  have hclosed : closedHalfspaceEvent f=gaussianBaseProjection ⁻¹'
      polyhedralEvent w (fun i => u*A i+v*B i) := by
    ext g
    simp only [closedHalfspaceEvent,f,Set.mem_setOf_eq,Set.mem_preimage,polyhedralEvent,sub_nonpos]
  have hmeasure : (stdGaussian (EuclideanSpace ℝ (ι⊕Fin 3))).real (closedHalfspaceEvent f)=
      (stdGaussian (EuclideanSpace ℝ ι)).real (polyhedralEvent w (fun i => u*A i+v*B i)) := by
    rw [hclosed,← map_measureReal_apply gaussianBaseProjection_measurable
      (measurableSet_polyhedralEvent w _),gaussianBaseProjection_map]
  simpa only [heq,hmeasure] using ht

end
end GaussLocalMaxColoring.Main


set_option autoImplicit false
set_option maxHeartbeats 2000000

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory ProbabilityTheory Set
open OAI.GaussianPropeller RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem ehrhard_polyhedral_extrapolation {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty κ]
    (w : κ→EuclideanSpace ℝ ι) (A B : κ→ℝ) (μ κ₀ θ : ℝ) (hθ : 0 ≤ θ)
    (h₀ : (stdGaussian (EuclideanSpace ℝ ι)).real (polyhedralEvent w A) ≤ Quantile.Φ (-μ))
    (h₁ : Quantile.Φ κ₀ ≤ (stdGaussian (EuclideanSpace ℝ ι)).real (polyhedralEvent w B)) :
    (stdGaussian (EuclideanSpace ℝ ι)).real
      (polyhedralEvent w (fun i => (1+θ)*A i-θ*B i)) ≤ Quantile.Φ (-(μ+θ*(μ+κ₀))) := by
  let P : ℝ→ℝ→ℕ→ℝ := fun u v n => EhrhardCone.prob
    (regularizedNormals w A B (regularizationScale n)) (regularizedTranslation u v (regularizationScale n))
  have hP₀ : Tendsto (P 1 0) atTop
      (𝓝 ((stdGaussian (EuclideanSpace ℝ ι)).real (polyhedralEvent w A))) := by
    simpa only [P,one_mul,zero_mul,add_zero] using regularized_probability_tendsto w A B 1 0
  have hP₁ : Tendsto (P 0 1) atTop
      (𝓝 ((stdGaussian (EuclideanSpace ℝ ι)).real (polyhedralEvent w B))) := by
    simpa only [P,one_mul,zero_mul,zero_add] using regularized_probability_tendsto w A B 0 1
  have hPθ : Tendsto (P (1+θ) (-θ)) atTop
      (𝓝 ((stdGaussian (EuclideanSpace ℝ ι)).real (polyhedralEvent w (fun i => (1+θ)*A i-θ*B i)))) := by
    simpa only [P,neg_mul,sub_eq_add_neg] using regularized_probability_tendsto w A B (1+θ) (-θ)
  have hUpper (m : ℕ) : (stdGaussian (EuclideanSpace ℝ ι)).real
      (polyhedralEvent w (fun i => (1+θ)*A i-θ*B i)) ≤
      Quantile.Φ (-((μ-regularizationScale m)+θ*((μ-regularizationScale m)+(κ₀-regularizationScale m)))) := by
    have heps := regularizationScale_pos m
    have hlt₀ : (stdGaussian (EuclideanSpace ℝ ι)).real (polyhedralEvent w A) <
        Quantile.Φ (-(μ-regularizationScale m)) :=
      h₀.trans_lt (Quantile.strictMono_Φ (by linarith))
    have hlt₁ : Quantile.Φ (κ₀-regularizationScale m) <
        (stdGaussian (EuclideanSpace ℝ ι)).real (polyhedralEvent w B) :=
      (Quantile.strictMono_Φ (by linarith)).trans_le h₁
    apply le_of_tendsto hPθ
    filter_upwards [hP₀.eventually_lt_const hlt₀,hP₁.eventually_const_lt hlt₁] with n hn₀ hn₁
    have h := ehrhard_cone_extrapolation (regularizedNormals w A B (regularizationScale n))
      (gaussianAugmentVector 0 0 0 1)
      (regularizedNormals_direction w A B _ (regularizationScale_pos n))
      (regularizedTranslation 1 0 (regularizationScale n)) (regularizedTranslation 0 1 (regularizationScale n))
      (μ-regularizationScale m) (κ₀-regularizationScale m) θ hθ hn₀.le hn₁.le
    rw [← regularizedTranslation_extrapolate _ θ (regularizationScale_pos n).ne'] at h
    exact h
  have hμ : Tendsto (fun m => μ-regularizationScale m) atTop (𝓝 μ) := by
    simpa using tendsto_const_nhds.sub regularizationScale_tendsto
  have hκ : Tendsto (fun m => κ₀-regularizationScale m) atTop (𝓝 κ₀) := by
    simpa using tendsto_const_nhds.sub regularizationScale_tendsto
  have harg := (hμ.add ((hμ.add hκ).const_mul θ)).neg
  have hlim := Quantile.continuous_Φ.continuousAt.tendsto.comp harg
  exact ge_of_tendsto hlim (Eventually.of_forall hUpper)

theorem ehrhard_Phi_eq_cdf (a : ℝ) : Quantile.Φ a=cdf (gaussianReal 0 1) a := by
  have hφ : Quantile.φ=gaussianPDFReal 0 1 := by
    funext x
    simp [Quantile.φ,gaussianPDFReal]
  calc
    Quantile.Φ a = ∫x in Set.Iic a,gaussianPDFReal 0 1 x := by rw [Quantile.Φ,hφ]
    _ = (gaussianReal 0 1).real (Set.Iic a) := by
      rw [measureReal_def,gaussianReal_apply_eq_integral 0 (by norm_num : (1:NNReal)≠0),
        ENNReal.toReal_ofReal (integral_nonneg (fun x => gaussianPDFReal_nonneg 0 1 x))]
    _ = cdf (gaussianReal 0 1) a := (cdf_eq_real _ _).symm

theorem ehrhard_Phi_neg_eq_tail (a : ℝ) : Quantile.Φ (-a)=PhiTail a := by
  rw [Quantile.Φ_neg,ehrhard_Phi_eq_cdf]
  rfl

theorem polyhedral_gaussian_extrapolation {ι κ : Type*} [Fintype ι] [Fintype κ]
    (w : κ→EuclideanSpace ℝ ι) (A B : κ→ℝ) (μ κ₀ θ : ℝ) (hθ : 0 ≤ θ)
    (h₀ : (stdGaussian (EuclideanSpace ℝ ι)).real (polyhedralEvent w A) ≤ PhiTail μ)
    (h₁ : 1-PhiTail κ₀ ≤ (stdGaussian (EuclideanSpace ℝ ι)).real (polyhedralEvent w B)) :
    (stdGaussian (EuclideanSpace ℝ ι)).real
      (polyhedralEvent w (fun i => (1+θ)*A i-θ*B i)) ≤ PhiTail (μ+θ*(μ+κ₀)) := by
  classical
  cases isEmpty_or_nonempty κ with
  | inl hκ =>
    have heq : polyhedralEvent w A=Set.univ := by ext; simp [polyhedralEvent]
    rw [heq,probReal_univ,← ehrhard_Phi_neg_eq_tail] at h₀
    exact False.elim (not_le_of_gt (Quantile.Φ_mem (-μ)).2 h₀)
  | inr hκ =>
    have h₀' : (stdGaussian (EuclideanSpace ℝ ι)).real (polyhedralEvent w A) ≤ Quantile.Φ (-μ) := by
      simpa only [ehrhard_Phi_neg_eq_tail] using h₀
    have h₁' : Quantile.Φ κ₀ ≤ (stdGaussian (EuclideanSpace ℝ ι)).real (polyhedralEvent w B) := by
      simpa only [PhiTail,Cohen2019.Robust.Phi,sub_sub_cancel,ehrhard_Phi_eq_cdf] using h₁
    simpa only [ehrhard_Phi_neg_eq_tail] using ehrhard_polyhedral_extrapolation w A B μ κ₀ θ hθ h₀' h₁'

theorem lemma_29 {d : ℕ} {Y : Type*} [Fintype Y]
    (z : Y→RecGaussColoring.Main.Space d) (A B : Y→ℝ) (μ₀ κ₀ θ : ℝ)
    (hμ : 0 ≤ μ₀) (hκ : 0 ≤ κ₀) (hθ : 0 ≤ θ)
    (h₀ : gaussProb {g : RecGaussColoring.Main.Space d | ∀y,⟪g,z y⟫ ≤ A y} ≤ PhiTail μ₀)
    (h₁ : 1-PhiTail κ₀ ≤ gaussProb {g : RecGaussColoring.Main.Space d | ∀y,⟪g,z y⟫ ≤ B y}) :
    gaussProb {g : RecGaussColoring.Main.Space d | ∀y,⟪g,z y⟫ ≤ (1+θ)*A y-θ*B y} ≤
      PhiTail (μ₀+θ*(μ₀+κ₀)) := by
  have h₀' : (stdGaussian (EuclideanSpace ℝ (Fin d))).real (polyhedralEvent z A) ≤ PhiTail μ₀ := by
    simpa only [gaussProb,polyhedralEvent,real_inner_comm] using h₀
  have h₁' : 1-PhiTail κ₀ ≤ (stdGaussian (EuclideanSpace ℝ (Fin d))).real (polyhedralEvent z B) := by
    simpa only [gaussProb,polyhedralEvent,real_inner_comm] using h₁
  simpa only [gaussProb,polyhedralEvent,real_inner_comm] using
    polyhedral_gaussian_extrapolation z A B μ₀ κ₀ θ hθ h₀' h₁'

end
end GaussLocalMaxColoring.Main


theorem solution {d : ℕ} {Y : Type*} [Fintype Y]
    (z : Y → RecGaussColoring.Main.Space d) (A B : Y → ℝ) (μ₀ κ₀ θ : ℝ)
    (hμ : 0 ≤ μ₀) (hκ : 0 ≤ κ₀) (hθ : 0 ≤ θ)
    (h₀ : gaussProb {g : RecGaussColoring.Main.Space d | ∀ y, ⟪g, z y⟫ ≤ A y} ≤ PhiTail μ₀)
    (h₁ : 1 - PhiTail κ₀ ≤ gaussProb {g : RecGaussColoring.Main.Space d | ∀ y, ⟪g, z y⟫ ≤ B y}) :
    gaussProb {g : RecGaussColoring.Main.Space d | ∀ y, ⟪g, z y⟫ ≤ (1 + θ) * A y - θ * B y} ≤
      PhiTail (μ₀ + θ * (μ₀ + κ₀)) := GaussLocalMaxColoring.Main.lemma_29 z A B μ₀ κ₀ θ hμ hκ hθ h₀ h₁
