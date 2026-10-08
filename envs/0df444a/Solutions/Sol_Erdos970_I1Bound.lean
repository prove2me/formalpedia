-- Prove2me | solution 1 for Erdos970.I1Bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T01:17:54.636967+00:00
-- url     : https://prove2.me/submissions/3a338654-aaf1-42c1-92e7-92f5f4b98a45

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.EulerMaclaurin
namespace Erdos970

open _root_.Finset _root_.Interval _root_.MeasureTheory

variable {𝕜 : Type*} [RCLike 𝕜] {f : ℝ → 𝕜} {a b : ℝ}


@[fun_prop]
lemma aestronglyMeasurable_B1 : AEStronglyMeasurable B1 := by
  unfold B1
  fun_prop






end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.Rectangle
namespace Erdos970

open _root_.Complex _root_.Set _root_.Topology

open scoped _root_.Interval

variable {z w : ℂ} {c : ℝ}

namespace Rectangle



end Rectangle




@[simp]
theorem preimage_equivRealProdCLM_reProdIm (s t : Set ℝ) :
    equivRealProdCLM.symm ⁻¹' (s ×ℂ t) = s ×ˢ t :=
  rfl

@[simp]
theorem ContinuousLinearEquiv.coe_toLinearEquiv_symm {R : Type*} {S : Type*} [Semiring R]
    [Semiring S] {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (M : Type*) [TopologicalSpace M]
    [AddCommMonoid M] {M₂ : Type*} [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M]
    [Module S M₂] (e : M ≃SL[σ] M₂) :
    ⇑e.toLinearEquiv.symm = e.symm :=
  rfl





































end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.ResidueCalcOnRectangles
namespace Erdos970

open _root_.Complex _root_.BigOperators _root_.Nat _root_.Classical _root_.Real _root_.Topology _root_.Filter
open _root_.Set _root_.MeasureTheory _root_.intervalIntegral _root_.Asymptotics

open scoped _root_.Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : ℂ → E} {z w p c A : ℂ}
  {x x₁ x₂ y y₁ y₂ σ : ℝ}
















theorem existsDifferentiableOn_of_bddAbove [CompleteSpace E]
    {s : Set ℂ} {c : ℂ} (hc : s ∈ nhds c)
    (hd : HolomorphicOn f (s \ {c}))
    (hb : BddAbove (norm ∘ f '' (s \ {c}))) :
    ∃ (g : ℂ → E),
      HolomorphicOn g s ∧ Set.EqOn f g (s \ {c}) :=
  ⟨Function.update f c (limUnder (𝓝[{c}ᶜ] c) f),
    differentiableOn_update_limUnder_of_bddAbove hc hd hb,
    fun z hz ↦ if h : z = c then (hz.2 h).elim
      else by simp [h]⟩







































lemma IsBigO_to_BddAbove {f : ℂ → ℂ} {p : ℂ}
    (f_near_p : f =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    ∃ U ∈ 𝓝 p, BddAbove (norm ∘ f '' (U \ {p})) := by
  simp only [isBigO_iff, Pi.one_apply, one_mem, CStarRing.norm_of_mem_unitary, mul_one] at f_near_p
  obtain ⟨c, hc⟩ := f_near_p
  dsimp [Filter.Eventually, nhdsWithin] at hc
  rw [mem_inf_principal'] at hc
  obtain ⟨U, hU, ⟨U_is_open, p_in_U⟩⟩ := mem_nhds_iff.mp hc
  use U
  constructor
  · exact IsOpen.mem_nhds U_is_open p_in_U
  · refine bddAbove_def.mpr ?_
    use c
    intro y hy
    simp only [Function.comp_apply, mem_image, Set.mem_sdiff, mem_singleton_iff] at hy
    obtain ⟨x, ⟨x_in_U, x_not_p⟩, fxy⟩ := hy
    rw [← fxy]
    simpa [x_not_p] using hU x_in_U






























end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.Sobolev
namespace Erdos970

open _root_.Real _root_.Complex _root_.MeasureTheory _root_.Filter _root_.Topology _root_.BoundedContinuousFunction _root_.SchwartzMap _root_.BigOperators
open scoped _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

@[ext] structure CS (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toFun : ℝ → E
  h1 : ContDiff ℝ n toFun
  h2 : HasCompactSupport toFun




section lemmas




end lemmas

namespace CS

variable {f : CS n E} {R x v : ℝ}

instance : CoeFun (CS n E) (fun _ => ℝ → E) where coe := CS.toFun



















end CS

namespace trunc







end trunc

namespace W1











end W1

namespace W21













end W21


end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.Fourier
namespace Erdos970

open _root_.FourierTransform _root_.Real _root_.Complex _root_.MeasureTheory _root_.Filter _root_.Topology _root_.BoundedContinuousFunction _root_.SchwartzMap VectorFourier _root_.BigOperators

local instance {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n => f n⟩

section lemmas

@[simp]
theorem nnnorm_eq_of_mem_circle (z : Circle) : ‖z.val‖₊ = 1 := NNReal.coe_eq_one.mp (by simp [Circle.norm_coe])

@[simp]
theorem nnnorm_circle_smul (z : Circle) (s : ℂ) : ‖z • s‖₊ = ‖s‖₊ := by
  simp [show z • s = z.val * s from rfl]


@[simp] lemma e_apply (u : ℝ) (v : ℝ) : e u v = 𝐞 (-v * u) := rfl



@[simp] lemma F_neg {f : ℝ → ℂ} {u : ℝ} : 𝓕 (fun x => -f x) u = - 𝓕 f u := by
  simp [fourier_eq, integral_neg]

@[simp] lemma F_add {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x + g x) x = 𝓕 f x + 𝓕 g x := by
  have : Continuous fun p : ℝ × ℝ ↦ ((innerₗ ℝ) p.1) p.2 := continuous_inner
  have := fourierIntegral_add continuous_fourierChar this hf hg
  exact congr_fun this x

@[simp] lemma F_sub {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x - g x) x = 𝓕 f x - 𝓕 g x := by
  simpa [sub_eq_add_neg, Pi.neg_def] using F_add hf hg.neg x

@[simp] lemma F_mul {f : ℝ → ℂ} {c : ℂ} {u : ℝ} :
    𝓕 (fun x => c * f x) u = c * 𝓕 f u := by
  exact congr_fun (VectorFourier.fourierIntegral_const_smul 𝐞 _ _ f c) u

end lemmas


@[simp] lemma deriv_ofReal : deriv ofReal = fun _ => 1 := by
  ext x ; exact ((hasDerivAt_id x).ofReal_comp).deriv






end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.Auxiliary
namespace Erdos970

namespace Complex

open _root_.Complex




end Complex

lemma DifferentiableAt.comp_ofReal {e : ℂ → ℂ} {z : ℝ} (hf : DifferentiableAt ℂ e z) :
    DifferentiableAt ℝ (fun x : ℝ ↦ e x) z :=
  hf.hasDerivAt.comp_ofReal.differentiableAt

lemma deriv.comp_ofReal {e : ℂ → ℂ} {z : ℝ} (hf : DifferentiableAt ℂ e z) :
    deriv (fun x : ℝ ↦ e x) z = deriv e z :=
  hf.hasDerivAt.comp_ofReal.deriv


lemma DifferentiableAt.ofReal_comp {z : ℝ} {f : ℝ → ℝ} (hf : DifferentiableAt ℝ f z) :
    DifferentiableAt ℝ (fun (y : ℝ) ↦ (f y : ℂ)) z :=
  hf.hasDerivAt.ofReal_comp.differentiableAt


open _root_.Complex _root_.ContinuousLinearMap in
lemma HasDerivAt.of_hasDerivAt_ofReal_comp {z : ℝ} {f : ℝ → ℝ} {u : ℂ}
    (hf : HasDerivAt (fun y ↦ (f y : ℂ)) u z) :
    ∃ u' : ℝ, u = u' ∧ HasDerivAt f u' z := by
  lift u to ℝ
  · have H := (imCLM.hasFDerivAt.comp z hf.hasFDerivAt).hasDerivAt.deriv
    simp only [Function.comp_def, imCLM_apply, ofReal_im, deriv_const] at H
    rwa [eq_comm, comp_apply, imCLM_apply, toSpanSingleton_apply_one] at H
  refine ⟨u, rfl, ?_⟩
  convert! (preTransparency := .instances) (reCLM.hasFDerivAt.comp z hf.hasFDerivAt).hasDerivAt
  rw [comp_apply, toSpanSingleton_apply_one, reCLM_apply, ofReal_re]

lemma DifferentiableAt.ofReal_comp_iff {z : ℝ} {f : ℝ → ℝ} :
    DifferentiableAt ℝ (fun (y : ℝ) ↦ (f y : ℂ)) z ↔ DifferentiableAt ℝ f z := by
  refine ⟨fun H ↦ ?_, ofReal_comp⟩
  obtain ⟨u, _, hu₂⟩ := HasDerivAt.of_hasDerivAt_ofReal_comp H.hasDerivAt
  exact HasDerivAt.differentiableAt hu₂

lemma Differentiable.ofReal_comp_iff {f : ℝ → ℝ} :
    Differentiable ℝ (fun (y : ℝ) ↦ (f y : ℂ)) ↔ Differentiable ℝ f :=
  forall_congr' fun _ ↦ DifferentiableAt.ofReal_comp_iff

lemma deriv.ofReal_comp {z : ℝ} {f : ℝ → ℝ} :
    deriv (fun (y : ℝ) ↦ (f y : ℂ)) z = deriv f z := by
  by_cases hf : DifferentiableAt ℝ f z
  · exact hf.hasDerivAt.ofReal_comp.deriv
  · have hf' := mt DifferentiableAt.ofReal_comp_iff.mp hf
    rw [deriv_zero_of_not_differentiableAt hf, deriv_zero_of_not_differentiableAt hf',
      Complex.ofReal_zero]

end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.MellinCalculus
namespace Erdos970

open scoped _root_.ContDiff


open _root_.Complex _root_.Topology _root_.Filter _root_.Real _root_.MeasureTheory _root_.Set _root_.Function

theorem MeasureTheory.setIntegral_integral_swap {α : Type*} {β : Type*} {E : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {μ : MeasureTheory.Measure α}
    {ν : MeasureTheory.Measure β} [NormedAddCommGroup E]
    [MeasureTheory.SigmaFinite ν] [NormedSpace ℝ E] [MeasureTheory.SigmaFinite μ]
    (f : α → β → E) {s : Set α} {t : Set β}
    (hf : IntegrableOn (f.uncurry) (s ×ˢ t) (μ.prod ν)) :
    (∫ (x : α) in s, ∫ (y : β) in t, f x y ∂ν ∂μ)
      = ∫ (y : β) in t, ∫ (x : α) in s, f x y ∂μ ∂ν := by
  apply integral_integral_swap
  convert (preTransparency := .instances) hf.integrable
  exact Measure.prod_restrict s t

open _root_.Erdos970.MeasureTheory

variable {𝕂 : Type*} [RCLike 𝕂]

lemma MeasureTheory.integral_comp_mul_right_I0i_haar
    (f : ℝ → 𝕂) {a : ℝ} (ha : 0 < a) :
    ∫ (y : ℝ) in Ioi 0, f (y * a) / y = ∫ (y : ℝ) in Ioi 0, f y / y := by
  have := integral_comp_mul_right_Ioi (fun y ↦ f y / y) 0 ha
  simp only [RCLike.ofReal_mul, zero_mul, eq_inv_smul_iff₀ (ne_of_gt ha)] at this
  rw [← integral_smul] at this
  rw [← this, setIntegral_congr_fun (by simp)]
  intro _ _
  simp only [RCLike.real_smul_eq_coe_mul]
  rw [mul_comm (a : 𝕂), div_mul, mul_div_assoc, div_self ?_, mul_one]
  exact (RCLike.ofReal_ne_zero).mpr <| ne_of_gt ha


lemma MeasureTheory.integral_comp_mul_left_I0i_haar
    (f : ℝ → 𝕂) {a : ℝ} (ha : 0 < a) :
    ∫ (y : ℝ) in Ioi 0, f (a * y) / y = ∫ (y : ℝ) in Ioi 0, f y / y := by
  convert (preTransparency := .instances) integral_comp_mul_right_I0i_haar f ha using 5; ring

lemma MeasureTheory.integral_comp_rpow_I0i_haar_real (f : ℝ → ℝ) {p : ℝ} (hp : p ≠ 0) :
    ∫ (y : ℝ) in Ioi 0, |p| * f (y ^ p) / y = ∫ (y : ℝ) in Ioi 0, f y / y := by
  rw [← integral_comp_rpow_Ioi (fun y ↦ f y / y) hp, setIntegral_congr_fun (by simp)]
  intro y hy
  have ypos : 0 < y := mem_Ioi.mp hy
  simp only [rpow_sub_one ypos.ne', smul_eq_mul]
  field_simp

lemma MeasureTheory.integral_comp_inv_I0i_haar (f : ℝ → 𝕂) :
    ∫ (y : ℝ) in Ioi 0, f (1 / y) / y = ∫ (y : ℝ) in Ioi 0, f y / y := by
  have := integral_comp_rpow_Ioi (fun y ↦ f y / y) (p := -1) (by simp)
  rw [← this, setIntegral_congr_fun (by simp)]
  intro y hy
  have : (y : 𝕂) ≠ 0 := (RCLike.ofReal_ne_zero).mpr <| LT.lt.ne' hy
  simp only [abs_neg, abs_one, rpow_neg_one, map_inv₀, div_inv_eq_mul,
    RCLike.real_smul_eq_coe_mul, RCLike.algebraMap_eq_ofReal]
  ring_nf
  simp [field]

lemma MeasureTheory.integral_comp_div_I0i_haar
    (f : ℝ → 𝕂) {a : ℝ} (ha : 0 < a) :
    ∫ (y : ℝ) in Ioi 0, f (a / y) / y = ∫ (y : ℝ) in Ioi 0, f y / y := by
  calc
    _ = ∫ (y : ℝ) in Ioi 0, f (a * y) / y := ?_
    _ = _ := integral_comp_mul_left_I0i_haar f ha
  convert (preTransparency := .instances) (integral_comp_inv_I0i_haar fun y ↦ f (a * (1 / y))).symm using 4
  · rw [mul_one_div]
  · rw [one_div_one_div]


@[simp]
lemma Function.support_abs {α : Type*} (f : α → 𝕂) :
    (fun x ↦ ‖f x‖).support = f.support := by
  simp only [support, ne_eq]; simp_rw [norm_ne_zero_iff]

@[simp]
lemma Function.support_ofReal {f : ℝ → ℝ} :
    (fun x ↦ ((f x) : ℂ)).support = f.support := by
  apply Function.support_comp_eq (g := ofReal); simp

lemma Function.support_mul_subset_of_subset {s : Set ℝ} {f g : ℝ → 𝕂}
    (fSupp : f.support ⊆ s) : (f * g).support ⊆ s := by
  simp_rw [support_mul', inter_subset, subset_union_of_subset_right fSupp]


lemma Function.support_deriv_subset_Icc {a b : ℝ} {f : ℝ → 𝕂}
    (fSupp : f.support ⊆ Set.Icc a b) :
    (deriv f).support ⊆ Set.Icc a b := by
    have := support_deriv_subset (f := fun x ↦ f x)
    dsimp [tsupport] at this
    have := subset_trans this <| closure_mono fSupp
    rwa [closure_Icc] at this


lemma SetIntegral.integral_eq_integral_inter_of_support_subset {μ : Measure ℝ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s t : Set ℝ} {f : ℝ → E} (h : f.support ⊆ t) (ht : MeasurableSet t) :
    ∫ x in s, f x ∂μ = ∫ x in s ∩ t, f x ∂μ := by
  rw [← setIntegral_indicator ht, indicator_eq_self.2 h]

lemma SetIntegral.integral_eq_integral_inter_of_support_subset_Icc {a b} {μ : Measure ℝ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set ℝ} {f : ℝ → E} (h : f.support ⊆ Icc a b) (hs : Icc a b ⊆ s) :
    ∫ x in s, f x ∂μ = ∫ x in Icc a b, f x ∂μ := by
  rw [SetIntegral.integral_eq_integral_inter_of_support_subset h measurableSet_Icc,
      inter_eq_self_of_subset_right hs]

lemma intervalIntegral.norm_integral_le_of_norm_le_const' {a b C : ℝ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hab : a ≤ b) (h : ∀ x ∈ (Icc a b), ‖f x‖ ≤ C) :
    ‖∫ x in a..b, f x‖ ≤ C * |b - a| := by
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  exact fun x hx ↦ h x <| mem_Icc_of_Ioc <| uIoc_of_le hab ▸ hx

lemma Filter.TendstoAtZero_of_support_in_Icc {a b : ℝ} (f : ℝ → 𝕂) (ha : 0 < a)
    (fSupp : f.support ⊆ Set.Icc a b) :
    Tendsto f (𝓝[>]0) (𝓝 0) := by
  apply Tendsto.comp (tendsto_nhds_of_eventually_eq ?_) tendsto_id
  filter_upwards [Ioo_mem_nhdsGT ha] with c hc; replace hc := (mem_Ioo.mp hc).2
  have h : c ∉ Icc a b := fun h ↦ by linarith [mem_Icc.mp h]
  convert (preTransparency := .instances) mt (Function.support_subset_iff.mp fSupp c) h; simp

lemma Filter.TendstoAtTop_of_support_in_Icc {a b : ℝ} (f : ℝ → 𝕂)
    (fSupp : f.support ⊆ Set.Icc a b) :
    Tendsto f atTop (𝓝 0) := by
  apply Tendsto.comp (tendsto_nhds_of_eventually_eq ?_) tendsto_id
  filter_upwards [Ioi_mem_atTop b] with c hc; rw [mem_Ioi] at hc
  have h : c ∉ Icc a b := fun h ↦ by linarith [mem_Icc.mp h]
  convert (preTransparency := .instances) mt (Function.support_subset_iff.mp fSupp c) h; simp



open _root_.Erdos970.Filter

lemma deriv.ofReal_comp' {f : ℝ → ℝ} :
    deriv (fun x : ℝ ↦ (f x : ℂ)) = (fun x ↦ ((deriv f) x : ℂ)) :=
  funext fun _ ↦ deriv.ofReal_comp


lemma PartialIntegration (f g : ℝ → ℂ)
    (fDiff : DifferentiableOn ℝ f (Ioi 0))
    (gDiff : DifferentiableOn ℝ g (Ioi 0))
    (fDerivgInt : IntegrableOn (f * deriv g) (Ioi 0))
    (gDerivfInt : IntegrableOn (deriv f * g) (Ioi 0))
    (lim_at_zero : Tendsto (f * g) (𝓝[>] 0) (𝓝 0))
    (lim_at_inf : Tendsto (f * g) atTop (𝓝 0)) :
    ∫ x in Ioi 0, f x * deriv g x = -∫ x in Ioi 0, deriv f x * g x := by
  simpa using integral_Ioi_mul_deriv_eq_deriv_mul
    (fun x hx ↦ fDiff.hasDerivAt (Ioi_mem_nhds hx))
    (fun x hx ↦ gDiff.hasDerivAt (Ioi_mem_nhds hx))
    fDerivgInt gDerivfInt lim_at_zero lim_at_inf

lemma PartialIntegration_of_support_in_Icc {a b : ℝ} (f g : ℝ → ℂ) (ha : 0 < a)
    (h : a ≤ b)
    (fSupp : f.support ⊆ Set.Icc a b)
    (fDiff : DifferentiableOn ℝ f (Ioi 0))
    (gDiff : DifferentiableOn ℝ g (Ioi 0))
    (fderivCont : ContinuousOn (deriv f) (Ioi 0))
    (gderivCont : ContinuousOn (deriv g) (Ioi 0)) :
    ∫ x in Ioi 0, f x * deriv g x = -∫ x in Ioi 0, deriv f x * g x := by
  have Icc_sub : Icc a b ⊆ Ioi 0 := (Icc_subset_Ioi_iff h).mpr ha
  have fderivSupp := Function.support_deriv_subset_Icc fSupp
  have fgSupp : (f * g).support ⊆ Icc a b := Function.support_mul_subset_of_subset fSupp
  have fDerivgInt : IntegrableOn (f * deriv g) (Ioi 0) := by
    apply (integrableOn_iff_integrable_of_support_subset <|
           Function.support_mul_subset_of_subset fSupp).mp
    exact fDiff.continuousOn.mono Icc_sub |>.mul (gderivCont.mono Icc_sub) |>.integrableOn_Icc
  have gDerivfInt : IntegrableOn (deriv f * g) (Ioi 0) := by
    apply (integrableOn_iff_integrable_of_support_subset <|
           Function.support_mul_subset_of_subset fderivSupp).mp
    exact fderivCont.mono Icc_sub |>.mul (gDiff.continuousOn.mono Icc_sub) |>.integrableOn_Icc
  have lim_at_zero : Tendsto (f * g) (𝓝[>]0) (𝓝 0) :=
    TendstoAtZero_of_support_in_Icc (f * g) ha fgSupp
  have lim_at_inf : Tendsto (f * g) atTop (𝓝 0) := TendstoAtTop_of_support_in_Icc (f * g) fgSupp
  apply PartialIntegration f g fDiff gDiff fDerivgInt gDerivfInt lim_at_zero lim_at_inf

local notation (name := mellintransform) "𝓜" => mellin


lemma MellinConvolutionSymmetric (f g : ℝ → 𝕂) {x : ℝ} (xpos : 0 < x) :
    MellinConvolution f g x = MellinConvolution g f x := by
  unfold MellinConvolution
  calc
    _ = ∫ y in Ioi 0, f (y * x) * g (1 / y) / y := ?_
    _ = _ := ?_
  · rw [← integral_comp_mul_right_I0i_haar (fun y ↦ f y * g (x / y)) xpos]
    simp [div_mul_cancel_right₀ <| ne_of_gt xpos]
  · convert (preTransparency := .instances) (integral_comp_inv_I0i_haar fun y ↦ f (y * x) * g (1 / y)).symm using 3
    rw [one_div_one_div, mul_comm, mul_comm_div, one_mul]




lemma MellinConvolutionTransform (f g : ℝ → ℂ) (s : ℂ)
    (hf : IntegrableOn (fun x y ↦ f y * g (x / y) / (y : ℂ) * (x : ℂ) ^ (s - 1)).uncurry
      (Ioi 0 ×ˢ Ioi 0)) :
    𝓜 (MellinConvolution f g) s = 𝓜 f s * 𝓜 g s := by
  dsimp [mellin, MellinConvolution]
  set f₁ : ℝ × ℝ → ℂ :=
    fun ⟨x, y⟩ ↦ f y * g (x / y) / (y : ℂ) * (x : ℂ) ^ (s - 1)
  calc
    _ = ∫ (x : ℝ) in Ioi 0, ∫ (y : ℝ) in Ioi 0, f₁ (x, y) := ?_
    _ = ∫ (y : ℝ) in Ioi 0, ∫ (x : ℝ) in Ioi 0, f₁ (x, y) :=
        setIntegral_integral_swap _ hf
    _ = ∫ (y : ℝ) in Ioi 0, ∫ (x : ℝ) in Ioi 0,
        f y * g (x / y) / ↑y * ↑x ^ (s - 1) := rfl
    _ = ∫ (y : ℝ) in Ioi 0, ∫ (x : ℝ) in Ioi 0,
        f y * g (x * y / y) / ↑y * ↑(x * y) ^ (s - 1) * y := ?_
    _ = ∫ (y : ℝ) in Ioi 0, ∫ (x : ℝ) in Ioi 0,
        f y * ↑y ^ (s - 1) * (g x * ↑x ^ (s - 1)) := ?_
    _ = ∫ (y : ℝ) in Ioi 0,
        f y * ↑y ^ (s - 1) * ∫ (x : ℝ) in Ioi 0, g x * ↑x ^ (s - 1) := ?_
    _ = _ := integral_mul_const _ _
  <;> try (rw [setIntegral_congr_fun (by simp)]; intro y hy; simp only [ofReal_mul])
  · simp only [integral_mul_const, f₁, mul_comm]
  · simp only [integral_mul_const]
    have := integral_comp_mul_right_Ioi
      (fun x ↦ f y * g (x / y) / (y : ℂ) * (x : ℂ) ^ (s - 1)) 0 hy
    have y_ne_zeroℂ : (y : ℂ) ≠ 0 := slitPlane_ne_zero (Or.inl hy)
    field_simp at this ⊢
    simp only [ofReal_mul, one_div, mul_zero, real_smul, ofReal_inv, field] at this ⊢
    rw [← this]
    field_simp
    congr with x
    ring_nf
  · rw [setIntegral_congr_fun (by simp)]
    intro x hx
    have y_ne_zeroℝ : y ≠ 0 := ne_of_gt (mem_Ioi.mp hy)
    have y_ne_zeroℂ : (y : ℂ) ≠ 0 := by exact_mod_cast y_ne_zeroℝ
    field_simp
    rw [mul_cpow_ofReal_nonneg hy.le hx.le]
    ring
  · apply integral_const_mul
  · congr <;> ext <;> ring


lemma MellinOfPsi_aux {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Set.Icc (1 / 2) 2)
    {s : ℂ} (hs : s ≠ 0) :
    ∫ (x : ℝ) in Ioi 0, (ν x) * (x : ℂ) ^ (s - 1) =
    - (1 / s) * ∫ (x : ℝ) in Ioi 0, (deriv ν x) * (x : ℂ) ^ s := by
  let g (s : ℂ) := fun (x : ℝ)  ↦ x ^ s / s
  have gderiv {s : ℂ} (hs : s ≠ 0) {x: ℝ} (hx : x ∈ Ioi 0) :
      deriv (g s) x = x ^ (s - 1) := by
    have := HasDerivAt.cpow_const (c := s) (hasDerivAt_id (x : ℂ)) (Or.inl hx)
    simp_rw [mul_one, id_eq] at this
    rw [deriv_div_const, deriv.comp_ofReal (e := fun x ↦ x ^ s)]
    · rw [this.deriv, mul_div_right_comm, div_self hs, one_mul]
    · apply hasDerivAt_deriv_iff.mp
      simp only [this.deriv, this]
  calc
    _ =  ∫ (x : ℝ) in Ioi 0, ↑(ν x) * deriv (@g s) x := ?_
    _ = -∫ (x : ℝ) in Ioi 0, deriv (fun x ↦ ↑(ν x)) x * @g s x := ?_
    _ = -∫ (x : ℝ) in Ioi 0, deriv ν x * @g s x := ?_
    _ = -∫ (x : ℝ) in Ioi 0, deriv ν x * x ^ s / s := by simp only [mul_div, g]
    _ = _ := ?_
  · rw [setIntegral_congr_fun (by simp)]
    intro _ hx
    simp only [gderiv hs hx]
  · apply PartialIntegration_of_support_in_Icc (ν ·) (g s)
      (a := 1 / 2) (b := 2) (by norm_num) (by norm_num)
    · simpa only [Function.support_subset_iff, ne_eq, ofReal_eq_zero]
    · exact (Differentiable.ofReal_comp_iff.mpr
        (diffν.differentiable (by norm_num))).differentiableOn
    · refine DifferentiableOn.div_const ?_ s
      intro a ha
      refine DifferentiableAt.comp_ofReal (e := fun x ↦ x ^ s) ?_ |>.differentiableWithinAt
      apply differentiableAt_fun_id.cpow (differentiableAt_const s) <| by exact Or.inl ha
    · simp only [deriv.ofReal_comp']
      exact continuous_ofReal.comp (diffν.continuous_deriv (by norm_num)) |>.continuousOn
    · apply ContinuousOn.congr (f := fun (x : ℝ) ↦ (x : ℂ) ^ (s - 1)) ?_
        fun x hx ↦ gderiv hs hx
      exact Continuous.continuousOn (by continuity) |>.cpow continuousOn_const (by simp)
  · congr; funext; congr
    apply (hasDerivAt_deriv_iff.mpr ?_).ofReal_comp.deriv
    exact diffν.contDiffAt.differentiableAt (by norm_num)
  · simp only [neg_mul, neg_inj]
    conv => lhs; rhs; intro; rw [← mul_one_div, mul_comm]
    rw [integral_const_mul]

lemma MellinOfPsi {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Set.Icc (1 / 2) 2) :
    ∃ C > 0, ∀ (σ₁ : ℝ) (_ : 0 < σ₁) (s : ℂ) (_ : σ₁ ≤ s.re) (_ : s.re ≤ 2),
    ‖𝓜 (fun x ↦ (ν x : ℂ)) s‖ ≤ C * ‖s‖⁻¹ := by
  let f := fun (x : ℝ) ↦ ‖deriv ν x‖
  have cont : ContinuousOn f (Icc (1 / 2) 2) :=
    (Continuous.comp (by continuity) <| diffν.continuous_deriv (by norm_num)).continuousOn
  obtain ⟨a, _, max⟩ := isCompact_Icc.exists_isMaxOn (f := f) (by norm_num) cont
  let σ₂ : ℝ := 2
  let C : ℝ := f a * 2 ^ σ₂ * (3 / 2)
  have mainBnd : ∀ (σ₁ : ℝ), 0 < σ₁ → ∀ (s : ℂ), σ₁ ≤ s.re → s.re ≤ 2 →
      ‖𝓜 (fun x ↦ (ν x : ℂ)) s‖ ≤ C * ‖s‖⁻¹ := by
    intro σ₁ σ₁pos s hs₁ hs₂
    have s_ne_zero: s ≠ 0 := fun h ↦ by linarith [zero_re ▸ h ▸ hs₁]
    simp only [mellin, f, MellinOfPsi_aux diffν suppν s_ne_zero, norm_mul, smul_eq_mul, mul_comm]
    gcongr
    · simp
    calc
      _ ≤ ∫ (x : ℝ) in Ioi 0, ‖(deriv ν x * (x : ℂ) ^ s)‖ := ?_
      _ = ∫ (x : ℝ) in Icc (1 / 2) 2, ‖(deriv ν x * (x : ℂ) ^ s)‖ := ?_
      _ ≤ ‖∫ (x : ℝ) in Icc (1 / 2) 2, ‖(deriv ν x * (x : ℂ) ^ s)‖‖ :=
          le_abs_self _
      _ ≤ _ := ?_
    · simp_rw [norm_integral_le_integral_norm]
    · apply SetIntegral.integral_eq_integral_inter_of_support_subset_Icc
      · simp only [Function.support_abs, Function.support_mul, Function.support_ofReal]
        apply subset_trans (by apply inter_subset_left) <| Function.support_deriv_subset_Icc suppν
      · exact (Icc_subset_Ioi_iff (by norm_num)).mpr (by norm_num)
    · have := intervalIntegral.norm_integral_le_of_norm_le_const' (C := f a * 2 ^ σ₂)
        (f := fun x ↦ f x * ‖(x : ℂ) ^ s‖) (a := (1 / 2 : ℝ)) ( b := 2) (by norm_num) ?_
      · simp only [Real.norm_eq_abs, norm_real, norm_mul] at this ⊢
        rwa [(by norm_num: |(2 : ℝ) - 1 / 2| = 3 / 2),
            intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc] at this
      · intro x hx;
        have f_bound := isMaxOn_iff.mp max x hx
        have pow_bound : ‖(x : ℂ) ^ s‖ ≤ 2 ^ σ₂ := by
          rw [norm_cpow_eq_rpow_re_of_pos (by linarith [mem_Icc.mp hx])]
          have xpos : 0 ≤ x := by linarith [(mem_Icc.mp hx).1]
          have h := rpow_le_rpow xpos (mem_Icc.mp hx).2 (by linarith : 0 ≤ s.re)
          exact le_trans h <| rpow_le_rpow_of_exponent_le (by norm_num) hs₂
        convert! (preTransparency := .instances) mul_le_mul f_bound pow_bound (norm_nonneg _) ?_ using 1 <;> simp [f]
  have Cnonneg : 0 ≤ C := by
    have hh := mainBnd 1 (by norm_num) ((3 : ℂ) / 2) (by norm_num) (by norm_num)
    have hhh : 0 ≤ ‖𝓜 (fun x ↦ (ν x : ℂ)) ((3 : ℂ) / 2)‖ := by positivity
    have hhhh : 0 < ‖(3 : ℂ) / 2‖⁻¹ := by norm_num
    have := hhh.trans hh
    exact (mul_nonneg_iff_of_pos_right hhhh).mp this
  by_cases CeqZero : C = 0
  · refine ⟨1, by linarith, ?_⟩
    intro ε εpos s hs₁ hs₂
    have := mainBnd ε εpos s hs₁ hs₂
    rw [CeqZero, zero_mul] at this
    have : 0 ≤ 1 * ‖s‖⁻¹ := by positivity
    linarith
  · exact ⟨C, lt_of_le_of_ne Cnonneg fun a ↦ CeqZero (id (Eq.symm a)), mainBnd⟩



lemma DeltaSpikeSupport_aux {ν : ℝ → ℝ} {ε : ℝ} (εpos : 0 < ε)
    (suppν : ν.support ⊆ Icc (1 / 2) 2) :
    (fun x ↦ if x < 0 then 0 else DeltaSpike ν ε x).support ⊆ Icc (2 ^ (-ε)) (2 ^ ε) := by
  unfold DeltaSpike
  simp only [one_div, Function.support_subset_iff, ne_eq, ite_eq_left_iff, not_lt, div_eq_zero_iff,
    not_forall, exists_prop, mem_Icc, and_imp]
  intro x hx h; push Not at h
  have := suppν <| Function.mem_support.mpr h.1
  simp only [one_div, mem_Icc] at this
  have hl := (le_rpow_inv_iff_of_pos (by norm_num) hx εpos).mp this.1
  rw [inv_rpow (by norm_num) ε, ← rpow_neg (by norm_num)] at hl
  refine ⟨hl, (rpow_inv_le_iff_of_pos ?_ (by norm_num) εpos).mp this.2⟩
  linarith [(by apply rpow_nonneg (by norm_num) : 0 ≤ (2 : ℝ) ^ (-ε))]

lemma DeltaSpikeSupport' {ν : ℝ → ℝ} {ε x : ℝ} (εpos : 0 < ε) (xnonneg : 0 ≤ x)
    (suppν : ν.support ⊆ Icc (1 / 2) 2) :
    DeltaSpike ν ε x ≠ 0 → x ∈ Icc (2 ^ (-ε)) (2 ^ ε) := by
  intro h
  have : (fun x ↦ if x < 0 then 0 else DeltaSpike ν ε x) x = DeltaSpike ν ε x := by
    simp [xnonneg]
  rw [← this] at h
  exact (Function.support_subset_iff.mp <| DeltaSpikeSupport_aux εpos suppν) _ h

lemma DeltaSpikeSupport {ν : ℝ → ℝ} {ε x : ℝ} (εpos : 0 < ε) (xnonneg : 0 ≤ x)
    (suppν : ν.support ⊆ Icc (1 / 2) 2) :
    x ∉ Icc (2 ^ (-ε)) (2 ^ ε) → DeltaSpike ν ε x = 0 := by
  contrapose!; exact DeltaSpikeSupport' εpos xnonneg suppν

@[fun_prop]
lemma DeltaSpikeContinuous {ν : ℝ → ℝ} {ε : ℝ} (εpos : 0 < ε)
    (diffν : ContDiff ℝ 1 ν) : Continuous (fun x ↦ DeltaSpike ν ε x) := by
  apply diffν.continuous.comp (g := ν) _ |>.div_const
  exact continuous_id.rpow_const fun _ ↦ Or.inr <| div_nonneg (by norm_num) εpos.le

lemma DeltaSpikeOfRealContinuous {ν : ℝ → ℝ} {ε : ℝ} (εpos : 0 < ε)
    (diffν : ContDiff ℝ 1 ν) : Continuous (fun x ↦ (DeltaSpike ν ε x : ℂ)) :=
  continuous_ofReal.comp <| DeltaSpikeContinuous εpos diffν


theorem MellinOfDeltaSpike (ν : ℝ → ℝ) {ε : ℝ} (εpos : ε > 0) (s : ℂ) :
    𝓜 (fun x ↦ (DeltaSpike ν ε x : ℂ)) s = 𝓜 (fun x ↦ (ν x : ℂ)) (ε * s) := by
  unfold DeltaSpike
  push_cast
  rw [mellin_div_const, mellin_comp_rpow (fun x ↦ (ν x : ℂ)), abs_of_nonneg (by positivity)]
  simp only [one_div, inv_inv, ofReal_inv, div_inv_eq_mul, real_smul]
  rw [mul_div_cancel_left₀ _ (ne_zero_of_re_pos εpos)]
  ring_nf



lemma MellinOf1 (s : ℂ) (h : s.re > 0) :
    𝓜 ((fun x ↦ if 0 < x ∧ x ≤ 1 then 1 else 0)) s = 1 / s := by
  convert (preTransparency := .instances) (hasMellin_one_Ioc h).right
  congr



lemma Smooth1Properties_estimate {ε : ℝ} (εpos : 0 < ε) :
    (1 - 2 ^ (-ε)) / ε < Real.log 2 := by
  apply (div_lt_iff₀' εpos).mpr
  have : 1 - 1 / (2 : ℝ) ^ ε = ((2 : ℝ) ^ ε - 1) / (2 : ℝ) ^ ε := by
    rw [sub_div, div_self (by positivity)]
  rw [← Real.log_rpow (by norm_num), rpow_neg (by norm_num), inv_eq_one_div (2 ^ ε), this]
  set c := (2 : ℝ) ^ ε
  have hc : 1 < c := by
    rw [← rpow_zero (2 : ℝ)]
    apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num) εpos
  apply (div_lt_iff₀' (by positivity)).mpr <| lt_sub_iff_add_lt'.mp ?_
  let f := (fun x ↦ x * Real.log x - x)
  rw [(by simp [f] : -1 = f 1), (by simp [f] : c * Real.log c - c = f c)]
  have mono: StrictMonoOn f <| Ici 1 := by
    refine strictMonoOn_of_deriv_pos (convex_Ici _) ?_ ?_
    · apply continuousOn_id.mul (continuousOn_id.log ?_) |>.sub continuousOn_id
      intro x hx; simp only [mem_Ici] at hx; simp only [id_eq, ne_eq]; linarith
    · intro x hx; simp only [nonempty_Iio, interior_Ici', mem_Ioi] at hx
      dsimp only [f]
      rw [deriv_fun_sub, deriv_fun_mul, Real.deriv_log, deriv_id'', one_mul, mul_inv_cancel₀]
      · simp [log_pos hx]
      · linarith
      · simp only [differentiableAt_fun_id]
      · simp only [differentiableAt_log_iff, ne_eq]; linarith
      · exact differentiableAt_fun_id.mul <| differentiableAt_fun_id.log (by linarith)
      · simp only [differentiableAt_fun_id]
  exact mono (by rw [mem_Ici]) (mem_Ici.mpr <| le_of_lt hc) hc



lemma Smooth1Properties_above_aux {x ε : ℝ} (hx : 1 + (2 * Real.log 2) * ε ≤ x)
    (hε : ε ∈ Ioo 0 1) :
    2 ^ ε < x := by
  calc
    x ≥ 1 + (2 * Real.log 2) * ε := hx
    _ > 2 ^ ε := ?_
  refine lt_add_of_sub_left_lt <| (div_lt_iff₀ hε.1).mp ?_
  calc
    2 * Real.log 2 > 2 * (1 - 2 ^ (-ε)) / ε := ?_
    _ > 2 ^ ε * (1 - 2 ^ (-ε)) / ε := ?_
    _ = (2 ^ ε - 1) / ε := ?_
  · field_simp
    exact Smooth1Properties_estimate hε.1
  · have : (2 : ℝ) ^ ε < 2 := by
      have h := rpow_lt_rpow_of_exponent_lt (x := 2) (by norm_num) hε.2
      rwa [Real.rpow_one] at h
    have pos: 0 < (1 - 2 ^ (-ε)) / ε := by
      refine div_pos ?_ hε.1
      rw [sub_pos]
      have h := rpow_lt_rpow_of_exponent_lt (x := 2) (by norm_num) (neg_lt_zero.mpr hε.1)
      rwa [Real.rpow_zero] at h
    have := (mul_lt_mul_iff_left₀ pos).mpr this
    ring_nf at this ⊢
    exact this
  · have : (2 : ℝ) ^ ε * (2 : ℝ) ^ (-ε) = (2 : ℝ) ^ (ε - ε) := by
      rw [← rpow_add (by norm_num), add_neg_cancel, sub_self]
    conv => lhs; lhs; ring_nf; rhs; simp [this]

lemma Smooth1Properties_above_aux2 {x y ε : ℝ} (hε : ε ∈ Ioo 0 1) (hy : y ∈ Ioc 0 1)
  (hx2 : 2 ^ ε < x) :
    2 < (x / y) ^ (1 / ε) := by
  obtain ⟨εpos, ε1⟩ := hε
  obtain ⟨ypos, y1⟩ := hy
  calc
    _ > (2 ^ ε / y) ^ (1 / ε) := ?_
    _ = 2 / y ^ (1 / ε) := ?_
    _ ≥ 2 / y := ?_
    _ ≥ 2 := ?_
  · rw [gt_iff_lt, div_rpow, div_rpow, lt_div_iff₀, mul_comm_div, div_self, mul_one]
    <;> try positivity
    · exact rpow_lt_rpow (by positivity) hx2 (by positivity)
    · exact LT.lt.le <| lt_trans (by positivity) hx2
  · rw [div_rpow, ← rpow_mul, mul_div_cancel₀ 1 <| ne_of_gt εpos, rpow_one] <;> positivity
  · have : y ^ (1 / ε) ≤ y := by
      nth_rewrite 2 [← rpow_one y]
      exact rpow_le_rpow_of_exponent_ge ypos y1 (by linarith [one_lt_one_div εpos ε1])
    have pos : 0 < y ^ (1 / ε) := rpow_pos_of_pos ypos _
    rw [ge_iff_le, div_le_iff₀, div_mul_eq_mul_div, le_div_iff₀', mul_comm] <;> try linarith
  · rw [ge_iff_le, le_div_iff₀ <| ypos]; exact (mul_le_iff_le_one_right zero_lt_two).mpr y1

lemma Smooth1Properties_above {ν : ℝ → ℝ} (suppν : ν.support ⊆ Icc (1 / 2) 2) :
    ∃ (c : ℝ), 0 < c ∧ c = 2 * Real.log 2 ∧
      ∀ (ε x) (_ : ε ∈ Ioo 0 1), 1 + c * ε ≤ x → Smooth1 ν ε x = 0 := by
  set c := 2 * Real.log 2; use c
  constructor
  · simp only [c, zero_lt_two, mul_pos_iff_of_pos_left]; exact log_pos (by norm_num)
  constructor
  · rfl
  intro ε x hε hx
  have hx2 := Smooth1Properties_above_aux hx hε
  unfold Smooth1 MellinConvolution
  simp only [ite_mul, one_mul, zero_mul, RCLike.ofReal_real_eq_id, id_eq]
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro y hy
  have ypos := mem_Ioi.mp hy
  by_cases y1 : y ≤ 1
  swap
  · simp [ypos, y1]
  simp only [mem_Ioi.mp hy, y1, and_self, ↓reduceIte, div_eq_zero_iff]; left
  apply DeltaSpikeSupport hε.1 ?_ suppν
  on_goal 1 =>
    simp only [mem_Icc, not_and, not_le]
  on_goal 2 =>
    suffices h : 2 ^ ε < x / y by
      linarith [(by apply rpow_pos_of_pos (by norm_num) : 0 < (2 : ℝ) ^ ε)]
  all_goals
  try intro
  have : x / y = ((x / y) ^ (1 / ε)) ^ ε := by
    rw [← rpow_mul]
    simp only [one_div, inv_mul_cancel₀ (ne_of_gt hε.1), rpow_one]
    apply div_nonneg_iff.mpr; left;
    exact ⟨(le_trans (rpow_pos_of_pos (by norm_num) ε).le) hx2.le, ypos.le⟩
  rw [this]
  refine rpow_lt_rpow (by norm_num) ?_ hε.1
  exact Smooth1Properties_above_aux2 hε ⟨ypos, y1⟩ hx2

lemma DeltaSpikeNonNeg_of_NonNeg {ν : ℝ → ℝ} (νnonneg : ∀ x > 0, 0 ≤ ν x)
     {x ε : ℝ} (xpos : 0 < x) (εpos : 0 < ε) :
    0 ≤ DeltaSpike ν ε x := by
  dsimp [DeltaSpike]
  have : 0 < x ^ (1 / ε) := by positivity
  have : 0 ≤ ν (x ^ (1 / ε)) := νnonneg _ this
  positivity

lemma MellinConvNonNeg_of_NonNeg {f g : ℝ → ℝ} (f_nonneg : ∀ x > 0, 0 ≤ f x)
    (g_nonneg : ∀ x > 0, 0 ≤ g x) {x : ℝ} (xpos : 0 < x) :
    0 ≤ MellinConvolution f g x := by
  dsimp [MellinConvolution]
  apply MeasureTheory.setIntegral_nonneg
  · exact measurableSet_Ioi
  · intro y ypos; simp only [mem_Ioi] at ypos
    have : 0 ≤ f y := f_nonneg _ ypos
    have : 0 < x / y := by positivity
    have : 0 ≤ g (x / y) := g_nonneg _ this
    positivity

lemma Smooth1Nonneg {ν : ℝ → ℝ} (νnonneg : ∀ x > 0, 0 ≤ ν x) {ε x : ℝ}
    (xpos : 0 < x) (εpos : 0 < ε) : 0 ≤ Smooth1 ν ε x := by
  dsimp [Smooth1]
  apply MellinConvNonNeg_of_NonNeg ?_ ?_ xpos
  · intro y hy; by_cases h : y ≤ 1 <;> simp [h, hy]
  · intro y ypos; exact DeltaSpikeNonNeg_of_NonNeg νnonneg ypos εpos

lemma Smooth1LeOne_aux {x ε : ℝ} {ν : ℝ → ℝ} (xpos : 0 < x) (εpos : 0 < ε)
    (mass_one : ∫ x in Ioi 0, ν x / x = 1) :
    ∫ (y : ℝ) in Ioi 0, ν ((x / y) ^ (1 / ε)) / ε / y = 1 := by
    calc
      _ = ∫ (y : ℝ) in Ioi 0, (ν (y ^ (1 / ε)) / ε) / y := ?_
      _ = ∫ (y : ℝ) in Ioi 0, ν y / y := ?_
      _ = 1 := mass_one
    · have := integral_comp_div_I0i_haar (fun y ↦ ν ((x / y) ^ (1 / ε)) / ε) xpos
      convert! (preTransparency := .instances) this.symm using 1
      congr; funext y; congr; field_simp [mul_comm]
    · have := integral_comp_rpow_I0i_haar_real (fun y ↦ ν y) (one_div_ne_zero εpos.ne')
      rw [← this, abs_of_pos <| one_div_pos.mpr εpos]
      field_simp

lemma Smooth1LeOne {ν : ℝ → ℝ} (νnonneg : ∀ x > 0, 0 ≤ ν x)
    (mass_one : ∫ x in Ioi 0, ν x / x = 1) {ε : ℝ} (εpos : 0 < ε) {x : ℝ} (xpos : 0 < x) :
    Smooth1 ν ε x ≤ 1 := by
  unfold Smooth1 MellinConvolution DeltaSpike
  have := Smooth1LeOne_aux xpos εpos mass_one
  calc
    _ = ∫ (y : ℝ) in Ioi 0,
        (fun y ↦ if y ∈ Ioc 0 1 then 1 else 0) y * (ν ((x / y) ^ (1 / ε)) / ε / y) := ?_
    _ ≤ ∫ (y : ℝ) in Ioi 0, (ν ((x / y) ^ (1 / ε)) / ε) / y := ?_
    _ = 1 := this
  · rw [setIntegral_congr_fun (by simp)]
    simp only [ite_mul, one_mul, zero_mul, RCLike.ofReal_real_eq_id, id_eq, mem_Ioc]
    intro y hy; aesop
  · refine setIntegral_mono_on ?_ (integrable_of_integral_eq_one this) (by simp) ?_
    · refine integrable_of_integral_eq_one this |>.bdd_mul ?_
        (ae_of_all _ <| by aesop)
      have : (fun x ↦ if 0 < x ∧ x ≤ 1 then 1 else 0) =
          indicator (Ioc 0 1) (1 : ℝ → ℝ) := by
        aesop
      simp only [mem_Ioc, this, measurableSet_Ioc, aestronglyMeasurable_indicator_iff]
      exact aestronglyMeasurable_one
    · simp only [ite_mul, one_mul, zero_mul]
      intro y hy
      by_cases h : y ≤ 1
      · aesop
      field_simp
      simp only [mem_Ioc, h, and_false, ↓reduceIte, one_div, mul_zero]
      simp only [mem_Ioi] at hy
      apply div_nonneg
      · apply νnonneg; exact rpow_pos_of_pos (div_pos xpos <| mem_Ioi.mp hy) _
      · positivity

lemma MellinOfSmooth1a {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Icc (1 / 2) 2)
    {ε : ℝ} (εpos : 0 < ε) {s : ℂ} (hs : 0 < s.re) :
    𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) s =
      s⁻¹ * 𝓜 (fun x ↦ (ν x : ℂ)) (ε * s) := by
  let f' : ℝ → ℂ := fun x ↦ DeltaSpike ν ε x
  let f : ℝ → ℂ := fun x ↦ DeltaSpike ν ε x / x
  let g : ℝ → ℂ := fun x ↦ if 0 < x ∧ x ≤ 1 then 1 else 0
  let F : ℝ × ℝ → ℂ := Function.uncurry fun x y ↦ f y * g (x / y) * (x : ℂ) ^ (s - 1)
  let S := {⟨x, y⟩ : ℝ × ℝ | 0 < x  ∧ x ≤ y ∧ 2 ^ (-ε) ≤ y ∧ y ≤ 2 ^ ε}
  let F' : ℝ × ℝ → ℂ := piecewise S (fun ⟨x, y⟩ ↦ f y * (x : ℂ) ^ (s - 1))
     (fun _ ↦ 0)
  let Tx := Ioc 0 ((2 : ℝ) ^ ε)
  let Ty := Icc ((2 : ℝ) ^ (-ε)) ((2 : ℝ) ^ ε)

  have Seq : S = (Tx ×ˢ Ty) ∩ {(x, y) : ℝ × ℝ | x ≤ y} := by
    ext ⟨x, y⟩; constructor
    · exact fun h ↦ ⟨⟨⟨h.1, le_trans h.2.1 h.2.2.2⟩, ⟨h.2.2.1, h.2.2.2⟩⟩, h.2.1⟩
    · exact fun h ↦  ⟨h.1.1.1, ⟨h.2, h.1.2.1, h.1.2.2⟩⟩
  have SsubI : S ⊆ Ioi 0 ×ˢ Ioi 0 :=
    fun z hz ↦ ⟨hz.1, lt_of_lt_of_le (by apply rpow_pos_of_pos; norm_num) hz.2.2.1⟩
  have SsubT: S ⊆ Tx ×ˢ Ty := by simp_rw [Seq, inter_subset_left]
  have Smeas : MeasurableSet S := by
    rw [Seq]; apply MeasurableSet.inter ?_ <| measurableSet_le measurable_fst measurable_snd
    simp [measurableSet_prod, Tx, Ty]

  have int_F: IntegrableOn F (Ioi 0 ×ˢ Ioi 0) := by
    apply IntegrableOn.congr_fun (f := F') ?_ ?_ (by simp [measurableSet_prod]); swap
    · simp only [F, F', f, g, mul_ite, mul_one, mul_zero]
      intro ⟨x, y⟩ hz
      by_cases hS : ⟨x, y⟩ ∈ S <;> simp only [hS, piecewise]
      <;> simp only [mem_prod, mem_Ioi, mem_ofPred_eq, not_and, not_le, S] at hz hS
      · simp [div_pos hz.1 hz.2, (div_le_one hz.2).mpr hS.2.1]
      · by_cases hxy : x / y ≤ 1
        swap
        · simp [hxy]
        have hy : y ∉ Icc (2 ^ (-ε)) (2 ^ ε) := by
          simp only [mem_Icc, not_and, not_le]; exact hS hz.1 <| (div_le_one hz.2).mp hxy
        simp [DeltaSpikeSupport εpos hz.2.le suppν hy]
    · apply Integrable.piecewise Smeas ?_ integrableOn_zero
      simp only [IntegrableOn, Measure.restrict_restrict_of_subset SsubI]
      apply MeasureTheory.Integrable.mono_measure ?_
      · apply MeasureTheory.Measure.restrict_mono' SsubT.eventuallyLE le_rfl
      change Integrable (fun x : ℝ × ℝ => f x.2 * (x.1 : ℂ) ^ (s - 1))
        (volume.restrict (Tx ×ˢ Ty))
      have : volume.restrict (Tx ×ˢ Ty) = (volume.restrict Tx).prod (volume.restrict Ty) := by
        rw [Measure.prod_restrict, MeasureTheory.Measure.volume_eq_prod]
      conv => rw [this]; lhs; intro; rw [mul_comm]
      apply MeasureTheory.Integrable.mul_prod (f := fun x ↦ (x : ℂ) ^ (s - 1))
        (μ := Measure.restrict volume Tx)
      · simp only [Tx]
        rw [← IntegrableOn, integrableOn_Ioc_iff_integrableOn_Ioo,
          intervalIntegral.integrableOn_Ioo_cpow_iff]
        · simp [hs]
        · apply rpow_pos_of_pos (by norm_num)
      · apply (ContinuousOn.div ?_ ?_ ?_).integrableOn_compact isCompact_Icc
        · exact (DeltaSpikeOfRealContinuous εpos diffν).continuousOn
        · exact continuous_ofReal.continuousOn
        · intro x hx; simp only [mem_Icc] at hx; simp only [ofReal_ne_zero]
          linarith [(by apply rpow_pos_of_pos (by norm_num) : (0 : ℝ) < 2 ^ (-ε))]

  have : 𝓜 (MellinConvolution g f') s = 𝓜 g s * 𝓜 f' s := by
    rw [mul_comm, ← MellinConvolutionTransform f' g s
      (by convert (preTransparency := .instances) int_F using 1; simp only [f', F, f]; field_simp)]
    dsimp [mellin]; rw [setIntegral_congr_fun (by simp)]
    intro x hx; simp_rw [MellinConvolutionSymmetric _ _ <| mem_Ioi.mp hx]

  convert! (preTransparency := .instances) this using 1
  · congr; funext x; convert! (preTransparency := .instances) integral_ofReal.symm
    simp only [MellinConvolution, RCLike.ofReal_div, ite_mul, one_mul, zero_mul, @apply_ite ℝ ℂ,
      algebraMap.coe_zero, g]; rfl
  · rw [MellinOf1 s hs, MellinOfDeltaSpike ν εpos s]
    simp

lemma MellinOfSmooth1b {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Set.Icc (1 / 2) 2) :
    ∃ (C : ℝ) (_ : 0 < C), ∀ (σ₁ : ℝ) (_ : 0 < σ₁)
    (s) (_ : σ₁ ≤ s.re) (_ : s.re ≤ 2) (ε : ℝ) (_ : 0 < ε) (_ : ε < 1),
    ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) s‖ ≤ C * (ε * ‖s‖ ^ 2)⁻¹ := by
  obtain ⟨C, Cpos, hC⟩ := MellinOfPsi diffν suppν
  refine ⟨C, Cpos, ?_⟩
  intro σ₁ σ₁pos s hs1 hs2 ε εpos ε_lt_one
  rw [MellinOfSmooth1a diffν suppν εpos <| lt_of_le_of_lt' hs1 σ₁pos]
  have hh1 : ε * σ₁ ≤ (ε * s).re := by
    simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    nlinarith
  have hh2 : (ε * s).re ≤ 2 := by
    simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    nlinarith
  calc
    ‖s⁻¹ * 𝓜 (fun x ↦ (ν x : ℂ)) (ε * s)‖ =
        ‖s⁻¹‖ * ‖𝓜 (fun x ↦ (ν x : ℂ)) (ε * s)‖ := by simp
    _                        ≤ ‖s⁻¹‖ * (C * (ε * ‖s‖)⁻¹) := by
      gcongr
      convert! (preTransparency := .instances) hC (ε * σ₁) (by positivity) (ε * s) hh1 hh2
      simp [abs_eq_self.mpr εpos.le]
    _                        = C * (ε * ‖s‖ ^ 2)⁻¹ := by
      simp only [norm_inv, mul_inv_rev]
      ring


lemma Smooth1ContinuousAt {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFpos : ∀ x > 0, 0 ≤ SmoothingF x)
    (suppSmoothingF : SmoothingF.support ⊆ Icc (1 / 2) 2)
    {ε : ℝ} (εpos : 0 < ε) {y : ℝ} (ypos : 0 < y) :
    ContinuousAt (fun x ↦ Smooth1 SmoothingF ε x) y := by
  apply ContinuousAt.congr
    (f := (fun x ↦ MellinConvolution (DeltaSpike SmoothingF ε)
      (fun x ↦ if 0 < x ∧ x ≤ 1 then 1 else 0) x)) _
  · filter_upwards [lt_mem_nhds ypos] with x hx
    apply MellinConvolutionSymmetric _ _ hx
  apply continuousAt_of_dominated (bound := (fun x ↦ 2 ^ ε * DeltaSpike SmoothingF ε x))
  · filter_upwards [lt_mem_nhds ypos] with x hx
    apply Measurable.aestronglyMeasurable
    apply Measurable.mul
    · apply Measurable.mul
      · exact Continuous.measurable <| DeltaSpikeContinuous εpos diffSmoothingF
      · apply Measurable.ite _ (by fun_prop) (by fun_prop)
        apply MeasurableSet.congr (s := Ici x) (by measurability)
        ext a
        constructor
        · intro ha
          have apos : 0 < a := lt_of_lt_of_le hx ha
          constructor
          · exact div_pos hx apos
          · exact (div_le_one apos).mpr ha
        · intro ha
          have : 0 < a := (div_pos_iff_of_pos_left hx).mp ha.1
          exact (div_le_one this).mp ha.2
    · fun_prop
  · filter_upwards [lt_mem_nhds ypos] with x hx
    filter_upwards [ae_restrict_mem (by measurability)] with t ht
    simp only [mul_ite, mul_one, mul_zero, RCLike.ofReal_real_eq_id, id_eq, norm_div, norm_eq_abs]
    by_cases! h : DeltaSpike SmoothingF ε t = 0
    · simp [h]
    have := DeltaSpikeSupport' εpos ht.le suppSmoothingF h
    have dsnonneg : 0 ≤ DeltaSpike SmoothingF ε t := by
      apply DeltaSpikeNonNeg_of_NonNeg <;> assumption
    calc
      _ ≤ |DeltaSpike SmoothingF ε t| / |t| := by
        gcongr
        · split_ifs with h
          · apply le_refl
          · exact dsnonneg
      _ ≤ _ := by
        rw [_root_.abs_of_nonneg dsnonneg, mul_comm, div_eq_mul_one_div, _root_.abs_of_pos ht]
        gcongr
        apply (one_div_le ht (by bound)).mpr
        · convert (preTransparency := .instances) this.1 using 1
          rw [div_eq_iff (by positivity), ← rpow_add (by norm_num), neg_add_cancel, rpow_zero]
  · apply Integrable.const_mul
    apply (integrable_indicator_iff (by measurability)).mp
    apply (integrableOn_iff_integrable_of_support_subset (s := Icc (2 ^ (-ε)) (2 ^ ε)) _).mp
    · apply ContinuousOn.integrableOn_compact isCompact_Icc
      apply ContinuousOn.congr  (f := DeltaSpike SmoothingF ε)
      · apply Continuous.continuousOn
        apply DeltaSpikeContinuous<;> assumption
      · intro x hx
        have : x ∈ Ioi 0 := by
          apply mem_Ioi.mpr
          apply lt_of_lt_of_le (by bound) hx.1
        rw [indicator, if_pos this]
    · unfold indicator
      simp_rw [mem_Ioi]
      apply Function.support_subset_iff.mpr
      simp only [ne_eq, ite_eq_right_iff, Classical.not_imp, mem_Icc, and_imp]
      intro x hx
      apply DeltaSpikeSupport' εpos hx.le suppSmoothingF
  · have : ∀ᵐ (a : ℝ) ∂volume.restrict (Ioi 0), a ≠ y := by
      apply ae_iff.mpr
      simp
    filter_upwards [ae_restrict_mem (by measurability), this] with x hx hx2
    simp only [mem_Ioi] at hx
    apply ContinuousAt.div_const
    apply ContinuousAt.mul (by fun_prop)
    have : (fun x_1 ↦ if 0 < x_1 / x ∧ x_1 / x ≤ 1 then 1 else 0) =
        (Ioc 0 x).indicator (fun _ ↦ (1 : ℝ)) := by
      ext t
      unfold indicator
      simp [div_pos_iff_of_pos_right, div_le_one₀, hx]
    rw [this]
    apply ContinuousOn.continuousAt_indicator (by fun_prop)
    simp [frontier_Ioc hx, ypos.ne', hx2.symm]


lemma Smooth1MellinDifferentiable {Ψ : ℝ → ℝ} {ε : ℝ} (diffΨ : ContDiff ℝ 1 Ψ)
    (suppΨ : Ψ.support ⊆ Icc (1 / 2) 2) (hε : ε ∈ Ioo 0 1)
    (Ψnonneg : ∀ x > 0, 0 ≤ Ψ x) (mass_one : ∫ x in Ioi 0, Ψ x / x = 1)
    {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (𝓜 (fun x ↦ (Smooth1 Ψ ε x : ℂ))) s := by
  apply mellin_differentiableAt_of_isBigO_rpow_exp zero_lt_one _ _ _ hs
  · apply ContinuousOn.locallyIntegrableOn _ (by measurability)
    apply continuousOn_of_forall_continuousAt
    exact fun x hx ↦ Smooth1ContinuousAt diffΨ Ψnonneg suppΨ hε.1 hx |>.ofReal
  · rw [Asymptotics.isBigO_iff]
    use 1
    obtain ⟨c, cpos, ceq, hc⟩ := Smooth1Properties_above suppΨ
    filter_upwards [eventually_ge_atTop (1 + c * ε)] with x hx
    rw [hc _ _ hε hx]
    simp only [ofReal_zero, norm_zero, neg_mul, one_mul, norm_eq_abs, abs_exp]
    bound
  · rw [Asymptotics.isBigO_iff]
    use 1
    filter_upwards [eventually_mem_nhdsWithin] with x hx
    simp only [norm_real, norm_eq_abs, neg_zero, rpow_zero, one_mem, CStarRing.norm_of_mem_unitary,
      mul_one]
    rw [_root_.abs_of_nonneg <| Smooth1Nonneg Ψnonneg hx hε.1]
    exact Smooth1LeOne Ψnonneg mass_one hε.1 hx

end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.ZetaBounds
namespace Erdos970


open _root_.Complex _root_.Topology _root_.Filter _root_.Interval _root_.Set _root_.Asymptotics






local notation (name := riemannzeta) "ζ" => riemannZeta
local notation (name := derivriemannzeta) "ζ'" => deriv riemannZeta

theorem ResidueOfTendsTo {f : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (hU : U ∈ 𝓝 p)
    (hf : HolomorphicOn f (U \ {p}))
    {A : ℂ}
    (h_limit : Tendsto (fun s ↦ (s - p) * f s) (𝓝[≠] p) (𝓝 A)) :
    ∃ V ∈ 𝓝 p,
    BddAbove (norm ∘ (f - fun s ↦ A * (s - p)⁻¹) '' (V \ {p})) := by
                                                                
  have h_event : ∀ᶠ s in 𝓝[≠] p, ‖(s - p) * f s - A‖ < 1 := by
    simp_rw [← dist_eq_norm_sub]
    exact h_limit.eventually (Metric.ball_mem_nhds _ (by norm_num))
  have h_event_nhds :
      ∀ᶠ s in 𝓝 p, s ≠ p → ‖(s - p) * f s - A‖ < 1 := by
    exact (eventually_nhdsWithin_iff).1 h_event
  rcases (eventually_nhds_iff.1 h_event_nhds) with ⟨V₀, hV₀_mem, hV₀_prop⟩
  have h_bound :
      ∀ s, s ∈ V₀ \ {p} → ‖(s - p) * f s‖ ≤ ‖A‖ + 1 := by
    intro s hs
    rcases hs with ⟨hV₀, hsne⟩
    calc ‖(s - p) * f s‖ = ‖((s - p) * f s - A) + A‖ := by
          ring_nf
        _ ≤ ‖(s - p) * f s - A‖ + ‖A‖ := norm_add_le ((s - p) * f s - A) A
        _ ≤ 1 + ‖A‖ := add_le_add_left (le_of_lt (hV₀_mem s hV₀ hsne)) ‖A‖
        _ = ‖A‖ + 1 := add_comm 1 ‖A‖
  have h_bdd :
      BddAbove (norm ∘ (fun s ↦ (s - p) * f s) '' (V₀ \ {p})) := by
    refine ⟨‖A‖ + 1, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    exact h_bound s hs
                                                                 
  set W : Set ℂ := V₀ ∩ U with hW_def
  have hW_mem : (W : Set ℂ) ∈ 𝓝 p := inter_mem (IsOpen.mem_nhds hV₀_prop.1 hV₀_prop.2) hU
  have h_subset_V₀ : (W \ {p}) ⊆ (V₀ \ {p}) := by
    intro z hz; exact ⟨hz.1.1, hz.2⟩
  have h_prod_holo : HolomorphicOn (fun z ↦ (z - p) * f z) (W \ {p}) := by
    have h_id : HolomorphicOn (fun z : ℂ ↦ z - p) (W \ {p}) :=
      Differentiable.differentiableOn (Differentiable.sub_const differentiable_fun_id p)
    have hfW : HolomorphicOn f (W \ {p}) := by
      apply hf.mono
      exact Set.sdiff_subset_sdiff_left inter_subset_right
    simpa using! h_id.mul hfW
  have h_bdd_W : BddAbove (norm ∘ (fun s ↦ (s - p) * f s) '' (W \ {p})) :=
    h_bdd.mono (image_mono h_subset_V₀)
                                                                    
  obtain ⟨g, hg_holo, hg_eq⟩ :=
    existsDifferentiableOn_of_bddAbove hW_mem h_prod_holo h_bdd_W
  have h_event_eq :
      (fun z ↦ g z) =ᶠ[𝓝[≠] p] fun z ↦ (z - p) * f z := by
    have hW_diff_mem : (W \ {p} : Set ℂ) ∈ 𝓝[≠] p :=
      sdiff_mem_nhdsWithin_compl hW_mem {p}
    exact (hg_eq.eventuallyEq_of_mem hW_diff_mem).symm
  have h_tendsto_gA : Tendsto g (𝓝[≠] p) (𝓝 A) :=
      h_limit.congr' (id (EventuallyEq.symm h_event_eq))
  have hpW : p ∈ W := by
    exact mem_of_mem_nhds hW_mem
  have h_cont_g : ContinuousAt g p := by
    apply (hg_holo.continuousOn.continuousWithinAt hpW).continuousAt hW_mem
  have h_tendsto_gp : Tendsto g (𝓝[≠] p) (𝓝 (g p)) :=
    h_cont_g.tendsto.mono_left inf_le_left
  have g_p_eq : g p = A :=
    tendsto_nhds_unique' (NormedField.nhdsNE_neBot p) h_tendsto_gp h_tendsto_gA
  let q : ℂ → ℂ := fun z ↦ (g z - A) / (z - p)
  have h_deriv : HasDerivAt g (deriv g p) p := by
    exact DifferentiableOn.hasDerivAt hg_holo hW_mem
  have h_q_limit : Tendsto q (𝓝[≠] p) (𝓝 (deriv g p)) := by
    rw [hasDerivAt_iff_tendsto_slope] at h_deriv
    unfold slope at h_deriv
    simp only [vsub_eq_sub, smul_eq_mul, inv_mul_eq_div, g_p_eq] at h_deriv
    exact h_deriv
  have h_event_q : ∀ᶠ z in 𝓝[≠] p, ‖q z - deriv g p‖ < 1 := by
    simp_rw [← dist_eq_norm_sub]
    exact h_q_limit.eventually (Metric.ball_mem_nhds _ (by norm_num))
  have h_event_q_nhds : ∀ᶠ z in 𝓝 p, z ≠ p → ‖q z - deriv g p‖ < 1 := by
    simpa using (eventually_nhdsWithin_iff).1 h_event_q
  rcases (eventually_nhds_iff.1 h_event_q_nhds) with
    ⟨V₁, hV₁_mem, hV₁_prop⟩
  have h_q_bound :
      ∀ z, z ∈ V₁ \ {p} → ‖q z‖ ≤ ‖deriv g p‖ + 1 := by
    intro z hz
    rcases hz with ⟨hV₁, hz_ne⟩
    calc ‖q z‖ = ‖(q z - deriv g p) + (deriv g p)‖ := by
          ring_nf
        _ ≤ ‖q z - deriv g p‖ + ‖deriv g p‖ := norm_add_le (q z - deriv g p) (deriv g p)
        _ ≤ 1 + ‖deriv g p‖  := add_le_add_left (le_of_lt (hV₁_mem z hV₁ hz_ne)) ‖deriv g p‖
        _ = ‖deriv g p‖ + 1 := add_comm 1 ‖deriv g p‖
                                                   
  have h_eq_diff :
      EqOn (fun z ↦ f z - A * (z - p)⁻¹) q (W \ {p}) := by
    intro z hz
    simp only
    have hz_ne : (z - p) ≠ 0 := sub_ne_zero.mpr hz.2
    have hgz : g z = (z - p) * f z := by
      exact id (EqOn.symm hg_eq) hz
    simp only [hgz, q]
    field_simp
  apply IsBigO_to_BddAbove
  rw [isBigO_iff]
  use ‖deriv g p‖ + 1
  apply eventually_nhdsWithin_iff.mpr
  filter_upwards [IsOpen.mem_nhds hV₁_prop.1 hV₁_prop.2, hW_mem] with z hV₁ hW z_ne_p
  specialize h_eq_diff ⟨ hW, z_ne_p⟩
  simp only [Pi.sub_apply, Pi.one_apply, one_mem, CStarRing.norm_of_mem_unitary,
    mul_one] at h_eq_diff ⊢
  rw [h_eq_diff]
  exact h_q_bound _ ⟨hV₁, z_ne_p⟩

theorem analyticAt_riemannZeta {s : ℂ} (s_ne_one : s ≠ 1) :
  AnalyticAt ℂ riemannZeta s := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [eventually_ne_nhds s_ne_one] with z hz using differentiableAt_riemannZeta hz

theorem differentiableAt_deriv_riemannZeta {s : ℂ} (s_ne_one : s ≠ 1) :
    DifferentiableAt ℂ ζ' s := by
  exact (analyticAt_riemannZeta s_ne_one).deriv.differentiableAt

theorem riemannZetaResidue :
    ∃ U ∈ 𝓝 1, BddAbove (norm ∘ (ζ - (fun s ↦ (s - 1)⁻¹)) '' (U \ {1})) := by
  have zeta_holc : HolomorphicOn ζ (univ \ {1}) := by
    intro y hy
    exact DifferentiableAt.differentiableWithinAt <| differentiableAt_riemannZeta hy.2
  convert (preTransparency := .instances) ResidueOfTendsTo univ_mem zeta_holc riemannZeta_residue_one using 6
  simp

theorem deriv_eqOn_of_eqOn_punctured (f g : ℂ → ℂ) (U : Set ℂ) (p : ℂ)
    (hU_open : IsOpen U)
    (h_eq : EqOn f g (U \ {p})) :
    EqOn (deriv f) (deriv g) (U \ {p}) := by
  intro x hx
  apply EventuallyEq.deriv_eq
  filter_upwards [IsOpen.mem_nhds (hU_open.sdiff isClosed_singleton) hx] with t ht using h_eq ht

theorem analytic_deriv_bounded_near_point
    (f : ℂ → ℂ) {U : Set ℂ} {p : ℂ} (hU : IsOpen U) (hp : p ∈ U) (hf : HolomorphicOn f U) :
    (deriv f) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
  have U_in_filter : U ∈ 𝓝 p := by
    exact IsOpen.mem_nhds hU hp
  have T := (analyticOn_iff_differentiableOn hU).mpr hf
  have T2 : ContDiffOn ℂ 1 f U :=
      DifferentiableOn.contDiffOn hf hU
  have T3 : ContinuousOn (fun x ↦ ((deriv f) x)) U := by
    apply T2.continuousOn_deriv_of_isOpen hU (by simp)
  have T4 := T3.continuousAt U_in_filter
  have T5 : (deriv f) =O[𝓝 p] (1 : ℂ → ℂ) :=
    T4.norm.isBoundedUnder_le.isBigO_one ℂ
  exact Asymptotics.IsBigO.mono T5 inf_le_left

theorem derivative_const_plus_product {g : ℂ → ℂ} (A p x : ℂ) (hg : DifferentiableAt ℂ g x) :
    deriv ((fun _ ↦ A) + g * fun s ↦ s - p) x = deriv g x * (x - p) + g x := by
  rw [deriv_add (by fun_prop) (by fun_prop), deriv_const, deriv_mul hg (by fun_prop)]
  simp

lemma deriv_inv_sub {x p : ℂ} (hp : x ≠ p) :
  deriv (fun z => (z - p)⁻¹) x =  -((x - p) ^ 2)⁻¹ := by
  rw [deriv_fun_inv'' (by fun_prop) (by grind)]
  simp
  field

theorem deriv_f_minus_A_inv_sub_clean (f : ℂ → ℂ) (A x p : ℂ)
    (hf : DifferentiableAt ℂ f x) (hp : x ≠ p) :
    deriv (f  - (fun z ↦ A * (z - p)⁻¹)) x = deriv f x + A * ((x - p) ^ 2)⁻¹ := by
  have h1 : DifferentiableAt ℂ (fun z => (z - p)⁻¹) x := by
    fun_prop (disch := grind)
  rw [deriv_sub hf (h1.const_mul A), deriv_const_mul A h1, deriv_inv_sub hp]
  ring

theorem nonZeroOfBddAbove {f : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (U_in_nhds : U ∈ 𝓝 p) {A : ℂ} (A_ne_zero : A ≠ 0)
    (f_near_p : BddAbove (norm ∘ (f - fun s ↦ A * (s - p)⁻¹) '' (U \ {p}))) :
    ∃ V ∈ 𝓝 p, IsOpen V ∧ ∀ s ∈ V \ {p}, f s ≠ 0 := by

  have h_decomp : ∀ s, f s = (f s - A * (s - p)⁻¹) + A * (s - p)⁻¹ := by
    intro s
    ring
                                      
  obtain ⟨M, hM⟩ := f_near_p

  have A_norm_pos : 0 < ‖A‖ := norm_pos_iff.mpr A_ne_zero
                                                                        
  let δ := ‖A‖ / (‖M‖ + 1)
  have δ_pos : 0 < δ := by
    refine div_pos A_norm_pos (add_pos_of_nonneg_of_pos (norm_nonneg M) one_pos)
                                                                            
  obtain ⟨V, hV_open, hV_mem, hV_sub⟩ : ∃ V, IsOpen V ∧ p ∈ V ∧ V ⊆ U ∩ Metric.ball p δ := by
                                     
    obtain ⟨W, hW_sub, hW_open, hW_mem⟩ := mem_nhds_iff.mp U_in_nhds
    let V := W ∩ Metric.ball p δ
    have VNp : V ∈ 𝓝 p := (𝓝 p).inter_mem (IsOpen.mem_nhds hW_open hW_mem)
      (Metric.ball_mem_nhds p δ_pos)
    exact ⟨V, IsOpen.inter hW_open Metric.isOpen_ball, mem_of_mem_nhds VNp,
      inter_subset_inter_left _ hW_sub⟩
  use V, mem_nhds_iff.mpr ⟨V, subset_refl V, hV_open, hV_mem⟩, hV_open
                    
  intro s hs
  have hs_in_U : s ∈ U := hV_sub hs.1 |>.1
  have hs_near_p : dist s p < δ := hV_sub hs.1 |>.2
  have hs_ne_p : s ≠ p := hs.2
                                                              
  rw [h_decomp s]
                                 
  have bound_first : ‖f s - A * (s - p)⁻¹‖ ≤ M := by
    apply hM
    exact ⟨s, ⟨hs_in_U, hs_ne_p⟩, rfl⟩
                                      
  have large_second : ‖M‖ + 1 < ‖A * (s - p)⁻¹‖ := by
    rw [norm_mul, norm_inv, ← div_eq_mul_inv]
    rw [lt_div_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hs_ne_p))]
    rw [mul_comm, ← lt_div_iff₀ (add_pos_of_nonneg_of_pos (norm_nonneg M) one_pos)]
    rw [dist_eq_norm_sub] at hs_near_p
    exact hs_near_p
                                                
  by_contra h_zero
                                                                  
  rw [add_eq_zero_iff_eq_neg] at h_zero
  rw [h_zero, norm_neg] at bound_first
                                    
  have : ‖M‖ + 1 < ‖M‖ := (lt_of_lt_of_le (lt_of_lt_of_le large_second bound_first)
    (Real.le_norm_self M))
  norm_num at this

theorem logDerivResidue' {f : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (U_is_open : IsOpen U)
    (non_zero : ∀ x ∈ U \ {p}, f x ≠ 0)
    (holc : HolomorphicOn f (U \ {p}))
    (U_in_nhds : U ∈ 𝓝 p) {A : ℂ} (A_ne_zero : A ≠ 0)
    (f_near_p : BddAbove (norm ∘ (f - fun s ↦ A * (s - p)⁻¹) '' (U \ {p}))) :
    (deriv f * f⁻¹ + (fun s ↦ (s - p)⁻¹)) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by

  have simpleHolo : HolomorphicOn (fun s ↦ A / (s - p)) (U \ {p}) := by
    apply DifferentiableOn.mono (t := {p}ᶜ)
    · apply DifferentiableOn.div
      · exact differentiableOn_const _
      · exact DifferentiableOn.sub differentiableOn_id (differentiableOn_const _)
      · exact fun x hx => by rw [sub_ne_zero]; exact hx
    · rintro s ⟨_, hs⟩ ; exact hs

  have f_minus_pole_is_holomorphic : HolomorphicOn (f - (fun s ↦ A * (s - p)⁻¹)) (U \ {p}) := by
    exact (DifferentiableOn.sub_iff_right holc).mpr simpleHolo

  let ⟨g, ⟨g_is_holomorphic, g_is_f_minus_pole⟩⟩ := existsDifferentiableOn_of_bddAbove
    U_in_nhds f_minus_pole_is_holomorphic f_near_p

  let h := (fun _ ↦ A) + g * (fun (s : ℂ) ↦ (s - p))

  have linear_is_holomorphic : HolomorphicOn (fun (s : ℂ ) ↦ (s - p)) U := by
    exact DifferentiableOn.sub_const differentiableOn_id p

  have h_is_holomorphic : HolomorphicOn h U := by
    have T := DifferentiableOn.mul g_is_holomorphic linear_is_holomorphic
    exact DifferentiableOn.const_add A T

  have h_continuous : ContinuousOn h U :=
    by exact DifferentiableOn.continuousOn h_is_holomorphic

  have deriv_h_identity : ∀x ∈ (U \ {p}), (deriv h) x = f x + (deriv f x) * (x - p) := by
    intro x x_in_u_not_p
    have x_in_u : x ∈ U := by exact Set.mem_of_mem_sdiff x_in_u_not_p
    have x_not_p : x ≠ p := by
      exact ((Set.mem_sdiff x).mp x_in_u_not_p).2

    have weird : U ∈ 𝓝 x := by
      exact IsOpen.mem_nhds (U_is_open) (x_in_u)

    rw [derivative_const_plus_product, ← g_is_f_minus_pole x_in_u_not_p,
      ← deriv_eqOn_of_eqOn_punctured _ _ U p U_is_open g_is_f_minus_pole x_in_u_not_p,
      deriv_f_minus_A_inv_sub_clean]
    · simp only [Pi.sub_apply]
      have := sub_ne_zero_of_ne x_not_p
      field_simp
      ring
    · apply holc.differentiableAt
      exact Filter.inter_mem weird <| compl_singleton_mem_nhds x_not_p
    · exact x_not_p
    · exact g_is_holomorphic.differentiableAt weird
  have h_identity : ∀x ∈ (U \ {p}), h x = (f x) * (x - p)  := by
    intro x x_in_u_not_p
    have hyp_x_not_p : x ≠ p := by
      exact ((Set.mem_sdiff x).mp x_in_u_not_p).2
    simp only [h, Pi.add_apply, Pi.mul_apply]
    rw [← g_is_f_minus_pole x_in_u_not_p]
    simp only [Pi.sub_apply]
    field [sub_ne_zero.mpr hyp_x_not_p]
  have log_deriv_f_plus_pole_equal_log_deriv_h :
      EqOn (deriv f * f⁻¹ + fun s ↦ (s - p)⁻¹) ((deriv h) * h⁻¹) (U \ {p}) := by
    simp only [Set.mem_sdiff, mem_singleton_iff, ne_eq, and_imp, Function.comp_apply, Pi.sub_apply,
      DifferentiableOn.sub_iff_right, differentiableOn_const, DifferentiableOn.fun_sub_iff_left,
      holc] at *
    intro x hyp_x
    have x_not_p : x ≠ p := by
      exact ((Set.mem_sdiff x).mp hyp_x).2
    have x_in_u : x ∈ U := by exact Set.mem_of_mem_sdiff hyp_x
    simp only [Pi.add_apply, Pi.mul_apply, Pi.inv_apply]
    rw [deriv_h_identity _ x_in_u x_not_p, h_identity _ x_in_u x_not_p]

    field [sub_ne_zero.mpr x_not_p, non_zero x (x_in_u) x_not_p]
  have h_inv_bounded :
      h⁻¹ =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
    have : ContinuousAt h⁻¹ p := by
      apply ContinuousOn.continuousAt h_continuous U_in_nhds |>.inv₀
      simp [h, A_ne_zero]
    exact Asymptotics.IsBigO.mono (this.norm.isBoundedUnder_le.isBigO_one ℂ) inf_le_left

  have h_deriv_bounded :
        (deriv h) =O[𝓝[≠] p] (1 : ℂ → ℂ) :=
          analytic_deriv_bounded_near_point h U_is_open
            (by exact mem_of_mem_nhds U_in_nhds) h_is_holomorphic

  have h_log_deriv_bounded :
    ((deriv h) * h⁻¹) =O[𝓝[≠] p] (1 : ℂ → ℂ)  := by
      have T := Asymptotics.IsBigO.mul h_deriv_bounded h_inv_bounded
      exact IsBigO.of_const_mul_right T

  have u_not_p_in_filter : U \ {p} ∈ 𝓝[≠] p := by
    exact sdiff_mem_nhdsWithin_compl U_in_nhds {p}
  have T := Set.EqOn.eventuallyEq_of_mem log_deriv_f_plus_pole_equal_log_deriv_h u_not_p_in_filter
  exact EventuallyEq.trans_isBigO T h_log_deriv_bounded

theorem logDerivResidue {f : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (non_zero : ∀ x ∈ U \ {p}, f x ≠ 0)
    (holc : HolomorphicOn f (U \ {p}))
    (U_in_nhds : U ∈ 𝓝 p) {A : ℂ} (A_ne_zero : A ≠ 0)
    (f_near_p : BddAbove (norm ∘ (f - fun s ↦ A * (s - p)⁻¹) '' (U \ {p}))) :
    (deriv f * f⁻¹ + (fun s ↦ (s - p)⁻¹)) =O[𝓝[≠] p] (1 : ℂ → ℂ) :=
    by
      let ⟨U', ⟨a,b,c⟩⟩ := mem_nhds_iff.mp U_in_nhds
      have W : (U' \ {p}) ⊆ U' := by
        exact Set.sdiff_subset

      have T : (U' \ {p}) ⊆ (U \ {p}) := by
        exact Set.sdiff_subset_sdiff a (subset_refl _)

      refine logDerivResidue' b ?_ ?_ (IsOpen.mem_nhds b c) A_ne_zero ?_
      · intro x hyp_x
        exact non_zero x <| T hyp_x
      · exact DifferentiableOn.mono holc T
      · exact (f_near_p.mono (image_mono (Set.sdiff_subset_sdiff a (subset_refl _))))


theorem logDerivResidue'' {f : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (non_zero : ∀ x ∈ U \ {p}, f x ≠ 0)
    (holc : HolomorphicOn f (U \ {p}))
    (U_in_nhds : U ∈ 𝓝 p) {A : ℂ} (A_ne_zero : A ≠ 0)
    (f_near_p : BddAbove (norm ∘ (f - fun s ↦ A * (s - p)⁻¹) '' (U \ {p}))) :
    ∃ V ∈ 𝓝 p, BddAbove (norm ∘ (deriv f * f⁻¹ + (fun s ↦ (s - p)⁻¹)) '' (V \ {p})) := by
  apply IsBigO_to_BddAbove
  exact logDerivResidue non_zero holc U_in_nhds A_ne_zero f_near_p


theorem riemannZetaLogDerivResidue :
    ∃ U ∈ 𝓝 1, BddAbove (norm ∘ (-(ζ' / ζ) - (fun s ↦ (s - 1)⁻¹)) '' (U \ {1})) := by
  obtain ⟨U,U_in_nhds, hU⟩ := riemannZetaResidue
  have hU' : BddAbove (norm ∘ (ζ - fun s ↦ 1 * (s - 1)⁻¹) '' (U \ {1})) := by
    simp only [Function.comp_apply, Pi.sub_apply, one_mul] at hU ⊢
    exact hU
  obtain ⟨V,V_in_nhds, V_is_open, hV⟩ := nonZeroOfBddAbove U_in_nhds one_ne_zero hU'
  let W := V ∩ interior U
  have hW : ∀ s ∈ W \ {1}, ζ s ≠ 0 := by
    intro s hs
    have s_in_V_diff : s ∈ V \ {1} := ⟨hs.1.1, hs.2⟩
    exact hV s s_in_V_diff
  have ζ_holc: HolomorphicOn ζ (W \ {1}) := by
    intro y hy
    simp only [Set.mem_sdiff, mem_singleton_iff] at hy
    refine DifferentiableAt.differentiableWithinAt ?_
    apply differentiableAt_riemannZeta hy.2
  have W_in_nhds : W ∈ 𝓝 1 := by
    refine inter_mem V_in_nhds ?_
    exact interior_mem_nhds.mpr U_in_nhds
  have := logDerivResidue'' hW ζ_holc W_in_nhds one_ne_zero
  have HW : BddAbove (norm ∘ (ζ - fun s ↦ (s - 1)⁻¹) '' (W \ {1})) := by
    obtain ⟨c, hc⟩ := bddAbove_def.mp hU
    apply bddAbove_def.mpr
    use c
    rintro y ⟨x, x_in_W, fxy⟩
    apply hc
    exact ⟨x, ⟨interior_subset x_in_W.1.2, x_in_W.2⟩, fxy⟩
  simp only [one_mul] at this
  have aux: ∀ a, ‖-(deriv ζ a / ζ a) - (a - 1)⁻¹‖ = ‖(deriv ζ a / ζ a) + (a - 1)⁻¹‖ := by
    intro a
    calc ‖-(deriv ζ a / ζ a) - (a - 1)⁻¹‖
         = ‖-((deriv ζ a / ζ a) + (a - 1)⁻¹)‖ := by ring_nf
       _ = ‖(deriv ζ a / ζ a) + (a - 1)⁻¹‖ := by rw [norm_neg]
  simp only [Function.comp_apply, Pi.sub_apply] at hU
  simp only [Function.comp_apply, Pi.sub_apply, Pi.neg_apply, Pi.div_apply, aux]
  apply this HW



local notation (name := riemannzeta0) "ζ₀" => riemannZeta0

































































































































open ArithmeticFunction (vonMangoldt)
local notation "Λ" => vonMangoldt
                                                              



end Erdos970

end

section
-- module Solutions.OAIChowla.StrongPNT.Erdos970.PNT5_Strong
namespace Erdos970


open _root_.Set _root_.Function _root_.Filter _root_.Complex _root_.Real

open _root_.ArithmeticFunction (vonMangoldt)







local notation (name := mellintransform2) "𝓜" => MellinTransform

local notation "Λ" => vonMangoldt

local notation "ζ" => riemannZeta

local notation "ζ'" => deriv ζ

local notation "I" => Complex.I


local notation "ψ" => ChebyshevPsi




open _root_.ComplexConjugate


open _root_.MeasureTheory

lemma SmoothedChebyshevDirichlet_aux_integrable {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFpos : ∀ x > 0, 0 ≤ SmoothingF x)
    (suppSmoothingF : support SmoothingF ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ (x : ℝ) in Ioi 0, SmoothingF x / x = 1)
    {ε : ℝ} (εpos : 0 < ε) (ε_lt_one : ε < 1) {σ : ℝ} (σ_gt : 1 < σ) (σ_le : σ ≤ 2) :
    MeasureTheory.Integrable
      (fun (y : ℝ) ↦ 𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (σ + y * I)) := by
  obtain ⟨c, cpos, hc⟩ := MellinOfSmooth1b diffSmoothingF suppSmoothingF
  apply Integrable.mono' (g := (fun t ↦ c / ε * 1 / (1 + t ^ 2)))
  · apply Integrable.const_mul integrable_inv_one_add_sq
  · apply Continuous.aestronglyMeasurable
    apply continuous_iff_continuousAt.mpr
    intro x
    have := Smooth1MellinDifferentiable diffSmoothingF suppSmoothingF ⟨εpos, ε_lt_one⟩
      SmoothingFpos mass_one (s := σ + x * I) (by simp only [add_re, ofReal_re, mul_re, I_re,
        mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero]; linarith) |>.continuousAt
    fun_prop
  · filter_upwards [] with t
    calc
      _≤ c / ε * 1 / (σ^2 + t^2) := by
        convert (preTransparency := .instances) hc (σ / 2) (by linarith) (σ + t * I) (by simp only [add_re, ofReal_re, mul_re,
          I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero, half_le_self_iff]; linarith)
          (by simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
            sub_self, add_zero]; linarith) ε εpos  ε_lt_one using 1
        simp only [mul_one, Complex.sq_norm, normSq_apply, add_re, ofReal_re, mul_re, I_re,
          mul_zero, ofReal_im, I_im, sub_self, add_zero, add_im, mul_im, zero_add, mul_inv_rev]
        ring_nf
      _ ≤ _ := by
        gcongr; nlinarith

attribute [fun_prop] Continuous.const_cpow
















theorem realDiff_of_complexDiff {f : ℂ → ℂ} (s : ℂ) (hf : DifferentiableAt ℂ f s) :
    ContinuousAt (fun (x : ℝ) ↦ f (s.re + x * I)) s.im := by
  apply ContinuousAt.comp _ (by fun_prop)
  convert (preTransparency := .instances) hf.continuousAt
  simp


theorem summable_real_iff_summable_coe_complex (f : ℕ → ℝ) :
    Summable f ↔ Summable (fun n => (f n : ℂ)) := by
  constructor

  · intro ⟨s, hs⟩
    use (s : ℂ)
    exact hasSum_ofReal.mpr hs

  · intro ⟨s, hs⟩
    use s.re
    have h_re : HasSum (fun n => ((f n : ℂ)).re) s.re :=
      by exact hasSum_re hs
    simpa using! h_re

theorem cast_pow_eq (n : ℕ) (σ₀ : ℝ):
  (↑((↑n : ℝ) ^ σ₀) : ℂ )  = (↑n : ℂ) ^ (↑σ₀ : ℂ) := by
    have U : (↑n : ℝ) ≥ 0 := by exact Nat.cast_nonneg' n
    have endit := Complex.ofReal_cpow U σ₀
    exact endit

theorem strongPnt_summable_complex_then_summable_real_part (f : ℕ → ℂ) :
  Summable f → Summable (fun n ↦ (f n).re) := by
    intro ⟨s, hs⟩
    use s.re
    have h_re : HasSum (fun n => ((f n : ℂ)).re) s.re :=
      by exact hasSum_re hs
    convert (preTransparency := .instances) h_re using 1

theorem strongPnt_dlog_riemannZeta_bdd_on_vertical_lines_generalized :
  ∀(σ₀ σ₁ : ℝ), ∀(t : ℝ), 1 < σ₀ → σ₀ ≤ σ₁ →
    ‖(- ζ' (σ₁ + t * I) / ζ (σ₁ + t * I))‖ ≤ ‖ζ' σ₀ / ζ σ₀‖ := by
  intro σ₀ σ₁ t σ₀_gt_one σ₀_lt_σ₁

  let s₁ := σ₁ + t * I
  have s₁_re_eq_sigma : s₁.re = σ₁ := by
    rw [Complex.add_re (σ₁) (t * I)]
    rw [Complex.ofReal_re σ₁]
    rw [Complex.mul_I_re]
    simp [*]

  have s₀_re_eq_sigma : (↑σ₀ : ℂ).re = σ₀ := by
    rw [Complex.ofReal_re σ₀]

  let s₀ := σ₀

  have σ₁_gt_one : 1 < σ₁ := by exact lt_of_le_of_lt' σ₀_lt_σ₁ σ₀_gt_one
  have s₀_gt_one : 1 < (↑σ₀ : ℂ).re := by exact σ₀_gt_one

  have s₁_re_geq_one : 1 < s₁.re := by exact lt_of_lt_of_eq σ₁_gt_one (id (Eq.symm s₁_re_eq_sigma))
  have s₁_re_coerce_geq_one : 1 < (↑s₁.re : ℂ).re := by exact s₁_re_geq_one
  rw [← (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div s₁_re_geq_one)]
  unfold LSeries

  have summable_von_mangoldt : Summable (fun i ↦ LSeries.term (fun n ↦ ↑(Λ n)) s₁.re i) := by
    exact ArithmeticFunction.LSeriesSummable_vonMangoldt s₁_re_geq_one

  have summable_von_mangoldt_at_σ₀ : Summable (fun i ↦ LSeries.term (fun n ↦ ↑(Λ n)) σ₀ i) := by
    exact ArithmeticFunction.LSeriesSummable_vonMangoldt σ₀_gt_one

  have summable_re_von_mangoldt : Summable (fun i ↦ (LSeries.term (fun n ↦ ↑(Λ n)) s₁.re i).re) := by
    exact strongPnt_summable_complex_then_summable_real_part (LSeries.term (fun n ↦ ↑(Λ n)) s₁.re) summable_von_mangoldt

  have summable_re_von_mangoldt_at_σ₀ : Summable (fun i ↦ (LSeries.term (fun n ↦ ↑(Λ n)) σ₀ i).re) := by
    exact strongPnt_summable_complex_then_summable_real_part (LSeries.term (fun n ↦ ↑(Λ n)) σ₀) summable_von_mangoldt_at_σ₀

  have positivity : ∀(n : ℕ), ‖LSeries.term (fun n ↦ ↑(Λ n)) s₁ n‖ = (LSeries.term (fun n ↦ Λ n) s₁.re n).re := by
    intro n
    calc
      ‖LSeries.term (fun n ↦ ↑(Λ n)) s₁ n‖ = Λ n / ‖(↑n : ℂ)^(s₁ : ℂ)‖ := by
        unfold LSeries.term
        by_cases h : n = 0
        · simp [*]
        · push Not at h
          simp [*]

      _ = Λ n / (↑n)^s₁.re := by
        by_cases h : n = 0
        · simp [*]
        · rw [Complex.norm_natCast_cpow_of_pos]
          push Not at h
          exact Nat.zero_lt_of_ne_zero h

      _ = (LSeries.term (fun n ↦ Λ n) s₁.re n).re := by
        unfold LSeries.term
        by_cases h : n = 0
        · simp [*]
        · simp [*]
          push Not at h
          ring_nf
          rw [Complex.re_ofReal_mul (Λ n)]
          ring_nf
          rw [Complex.inv_re]
          rw [Complex.cpow_ofReal_re]
          simp [*]
          left
          have N : (0 : ℝ) ≤ ↑n := by exact Nat.cast_nonneg' n
          have T2 : ((↑n : ℂ) ^ (↑σ₁ : ℂ)).re = (↑n : ℝ)^σ₁ := by exact rfl
          have T1 : ((↑n : ℂ ) ^ (↑σ₁ : ℂ)).im = 0 := by
            refine abs_re_eq_norm.mp ?_
            rw [T2]
            simp [*]
            exact Real.rpow_nonneg N σ₁

          simp [Complex.normSq_apply]
          simp [T1, T2]

  have summable_abs_value : Summable (fun i ↦ ‖LSeries.term (fun n ↦ ↑(Λ n)) s₁ i‖) := by
    rw [summable_congr positivity]
    exact summable_re_von_mangoldt

  have triangle_ineq : ‖LSeries (fun n ↦ ↑(Λ n)) s₁‖ ≤ ∑' (n : ℕ), ↑‖LSeries.term (fun n ↦ ↑(Λ n)) s₁ n‖ :=
    norm_tsum_le_tsum_norm summable_abs_value

  have bounded_by_sum_of_re : ‖LSeries (fun n ↦ ↑(Λ n)) s₁‖ ≤ ∑' (n : ℕ), (LSeries.term (fun n ↦ ↑(Λ n)) (↑s₁.re) n).re :=
    by
      simp [positivity] at triangle_ineq
      exact triangle_ineq

  have sum_of_re_commutes : ∑' (n : ℕ), (LSeries.term (fun n ↦ ↑(Λ n)) (↑s₁.re) n).re = (∑' (n : ℕ), (LSeries.term (fun n ↦ ↑(Λ n)) (↑s₁.re) n)).re :=
    (Complex.re_tsum (summable_von_mangoldt)).symm

  have re_of_sum_bdd_by_norm : (∑' (n : ℕ), (LSeries.term (fun n ↦ ↑(Λ n)) (↑s₁.re) n)).re  ≤ ‖∑' (n : ℕ), (LSeries.term (fun n ↦ ↑(Λ n)) (↑s₁.re) n)‖ :=
    Complex.re_le_norm (∑' (n : ℕ), (LSeries.term (fun n ↦ ↑(Λ n)) (↑s₁.re) n))

  have ineq_s₁_s₀ : ∀(n : ℕ),
    (LSeries.term (fun n ↦ Λ n) s₁.re n).re ≤ (LSeries.term (fun n ↦ Λ n) σ₀ n).re :=
  by
    intro n
    unfold LSeries.term
    by_cases h : n = 0
    · simp [*]
    · push Not at h
      simp [*]
      have H : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
      ring_nf
      rw [Complex.re_ofReal_mul (Λ n) ((↑n : ℂ) ^ (↑σ₁ : ℂ))⁻¹]
      rw [Complex.re_ofReal_mul (Λ n) ((↑n : ℂ) ^ (↑σ₀ : ℂ))⁻¹]
      refine mul_le_mul_of_nonneg_left ?_ H
      · simp [Complex.inv_re]
        have R1 : ((↑n : ℂ) ^ (↑σ₀ : ℂ)).re = (↑n : ℝ) ^ σ₀ := rfl
        have R2 : ((↑n : ℂ) ^ (↑σ₁ : ℂ)).re = (↑n : ℝ) ^ σ₁ := rfl
        have geq : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr h
        have geq_zero : 0 ≤ n := Nat.zero_le n
        have n_geq_one : (1 : ℝ) ≤ ↑n := by
          norm_cast
        have n_geq_pos : (0 : ℝ) ≤ ↑n := by
          norm_cast
        have n_gt_pos : (0 : ℝ) < (↑n) := by
          norm_cast

        have I1 : ((↑n : ℂ) ^ (↑σ₀ : ℂ)).im = 0 := by
            refine abs_re_eq_norm.mp ?_
            rw [R1]
            simp [*]
            exact Real.rpow_nonneg n_geq_pos σ₀

        have I2 : ((↑n : ℂ) ^ (↑σ₁ : ℂ)).im = 0 := by
            refine abs_re_eq_norm.mp ?_
            rw [R2]
            simp [*]
            exact Real.rpow_nonneg n_geq_pos σ₁

        simp [Complex.normSq_apply, R1, R2, I1, I2]
        have P1 : 0 < (↑n : ℝ)^σ₁ := Real.rpow_pos_of_pos n_gt_pos σ₁
        have P2 : 0 < (↑n : ℝ)^σ₀ := Real.rpow_pos_of_pos n_gt_pos σ₀

        have N : (↑n : ℝ)^σ₀ ≤ (↑n : ℝ)^σ₁ :=
          Real.rpow_le_rpow_of_exponent_le n_geq_one σ₀_lt_σ₁
        apply inv_anti₀
        · exact P2
        · exact N

  have Z :=
    by
      calc
        ‖LSeries (fun n ↦ ↑(Λ n)) s₁‖ ≤ ∑' (n : ℕ), ‖LSeries.term (fun n ↦ ↑(Λ n)) s₁ n‖
            := norm_tsum_le_tsum_norm summable_abs_value
      _ ≤ ∑' (n : ℕ), (LSeries.term (fun n ↦ Λ n) s₁.re n).re := by simp [←positivity]
      _ ≤ ∑' (n : ℕ), (LSeries.term (fun n ↦ Λ n) σ₀ n).re := by
          refine Summable.tsum_mono ?_ ?_ ineq_s₁_s₀
          · exact summable_re_von_mangoldt
          · exact summable_re_von_mangoldt_at_σ₀
      _ = (∑' (n : ℕ), (LSeries.term (fun n ↦ Λ n) σ₀ n)).re := (Complex.re_tsum (summable_von_mangoldt_at_σ₀)).symm
      _ ≤ ‖∑' (n : ℕ), (LSeries.term (fun n ↦ Λ n) σ₀ n)‖ := re_le_norm (∑' (n : ℕ), LSeries.term (fun n ↦ ↑(Λ n)) σ₀ n)
      _ = ‖- ζ' (σ₀) / ζ (σ₀)‖ := by
          simp only [← (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div s₀_gt_one)]
          unfold LSeries
          rfl
      _ = ‖ζ' σ₀ / ζ σ₀‖ := by
        rw [← s₀_re_eq_sigma]
        simp [*]

  exact Z

theorem strongPnt_triv_bound_zeta :
  ∃C ≥ 0, ∀(σ₀ t : ℝ), 1 < σ₀ → ‖- ζ' (σ₀ + t * I) / ζ (σ₀ + t * I)‖ ≤ (σ₀ - 1)⁻¹ + C
  := by

      let ⟨U, ⟨U_in_nhds, zeta_residue_on_U⟩⟩ := riemannZetaLogDerivResidue

      let ⟨open_in_U, ⟨open_in_U_subs_U, open_in_U_is_open, one_in_open_U⟩⟩ := mem_nhds_iff.mp U_in_nhds

      let ⟨ε₀, ⟨ε_pos, metric_ball_around_1_is_in_U'⟩⟩ := EMetric.isOpen_iff.mp open_in_U_is_open (1 : ℂ) one_in_open_U

      let ε := if ε₀ = ⊤ then ENNReal.ofReal 1 else ε₀
      have O1 : ε ≠ ⊤ := by
        by_cases h : ε₀ = ⊤
        · unfold ε
          simp [*]
        · unfold ε
          simp [*]

      have metric_ball_around_1_is_in_U :
        Metric.eball (1 : ℂ) ε ⊆ U := by
          by_cases h : ε₀ = ⊤
          · unfold ε
            simp [*]
            have T : Metric.eball (1 : ℂ) 1 ⊆ Metric.eball 1 ε₀ := by
              rw [h]
              exact Metric.eball_subset_eball (by simp)
            exact subset_trans (subset_trans T metric_ball_around_1_is_in_U') open_in_U_subs_U

          · unfold ε

            simp [h]
            exact subset_trans metric_ball_around_1_is_in_U' open_in_U_subs_U

      have O2 : ε ≠ 0 := by
        by_cases h : ε₀ = ⊤
        · unfold ε
          simp [*]
        · unfold ε
          simp [*]
          exact pos_iff_ne_zero.mp ε_pos

      let metric_ball_around_1 := Metric.eball (1 : ℂ) ε
      let ε_div_two := ε / 2
      let boundary := ENNReal.toReal (1 + ε_div_two)

      let ⟨bound, ⟨bound_pos, bound_prop⟩⟩ :=
          BddAbove.exists_ge zeta_residue_on_U 0

      have boundary_geq_one : 1 < boundary := by
          unfold boundary
          have Z : (1 : ENNReal).toReal = 1 := by rfl
          rw [←Z]
          have U : ε_div_two ≠ ⊤ := by
            refine ENNReal.div_ne_top O1 ?_
            simp
          simp
          simp [ENNReal.toReal_add _ U]
          refine ENNReal.toReal_pos ?_ ?_
          · unfold ε_div_two
            simp [*]
          · exact U

      let const : ℝ := bound
      let final_const : ℝ := (boundary - 1)⁻¹ + const
      have boundary_inv_pos : 0 < (boundary - 1)⁻¹ := by
        ring_nf
        apply inv_pos_of_pos
        simp [*]

      have final_const_pos : final_const ≥ 0 := by
        unfold final_const
        simp [*]
        have Z :=
          by
            calc
              0 ≤ (boundary - 1)⁻¹ := by simp; linarith
              _ ≤ (boundary - 1)⁻¹ + const := by unfold const; simp [bound_pos]

        exact Z

      have const_le_final_const : const ≤ final_const := by
        calc
          const ≤ (boundary - 1)⁻¹ + const := by simp; linarith
          _ = final_const := by rfl

      have const_pos : const ≥ 0 := by
        linarith

      use final_const
      use final_const_pos
      intro σ₀ t σ₀_gt

      by_cases h : σ₀ ≤ boundary
      · have σ₀_in_ball : (↑σ₀ : ℂ) ∈ metric_ball_around_1 := by
          unfold metric_ball_around_1
          unfold Metric.eball
          simp [*]
          have Z := edist_dist (↑σ₀) (↑1 : ℂ)
          rw [Z]
          have U := dist_eq_norm (↑σ₀) (↑1 : ℂ)
          rw [U]
          norm_cast
          have U : 0 ≤ σ₀ - 1 := by linarith
          have U1 : ‖σ₀ - 1‖ = σ₀ - 1 := by exact norm_of_nonneg U
          have U2 : ε ≠ ⊤ := by exact O1
          have U3 : 0 ≤ ε := by exact zero_le
          simp [Real.norm_of_nonneg U]
          simp [ENNReal.ofReal_lt_iff_lt_toReal U U2]
          have U4 : ENNReal.ofReal 1 ≠ ⊤ := by exact ENNReal.ofReal_ne_top
          have Z0 : ε_div_two.toReal < ε.toReal := by
            have T1 : ε ≠ ⊤ := by exact U2
            have T2 : ε ≠ 0 := by exact O2
            have T3 : ε_div_two < ε := by
              refine ENNReal.half_lt_self ?_ U2
              exact T2

            exact ENNReal.toReal_strict_mono T1 T3

          have Z := by
            calc
              σ₀ - 1 ≤ boundary - 1 := by linarith
              _ = ENNReal.toReal (1 + ε_div_two) - 1 := rfl
              _ = ENNReal.toReal (1 + ε_div_two) - ENNReal.toReal (ENNReal.ofReal 1) := by simp
              _ ≤ ENNReal.toReal (1 + ε_div_two - ENNReal.ofReal 1) := ENNReal.le_toReal_sub U4
              _ = ENNReal.toReal (ε_div_two) := by simp only [ENNReal.ofReal_one, ENNReal.addLECancellable_iff_ne, ne_eq, ENNReal.one_ne_top, not_false_eq_true, AddLECancellable.add_tsub_cancel_left]
              _ < ε.toReal := Z0

          exact Z

        have σ₀_in_U : (↑σ₀ : ℂ) ∈ (U \ {1}) := by
          refine mem_sdiff_singleton.mpr ?_
          constructor
          · unfold metric_ball_around_1 at σ₀_in_ball
            exact metric_ball_around_1_is_in_U σ₀_in_ball
          · by_contra a
            have U : σ₀ = 1 := by exact ofReal_eq_one.mp a
            rw [U] at σ₀_gt
            linarith

        have bdd := Set.forall_mem_image.mp bound_prop (σ₀_in_U)
        simp [*] at bdd
        have Z :=
          calc
            ‖- ζ' (σ₀ + t * I) / ζ (σ₀ + t * I)‖ ≤ ‖ζ' σ₀ / ζ σ₀‖ := by
               have U := strongPnt_dlog_riemannZeta_bdd_on_vertical_lines_generalized σ₀ σ₀ t (σ₀_gt) (by simp)
               exact U
            _ = ‖- ζ' σ₀ / ζ σ₀‖ := by simp only [Complex.norm_div, norm_neg]
            _ = ‖(- ζ' σ₀ / ζ σ₀ - (σ₀ - 1)⁻¹) + (σ₀ - 1)⁻¹‖ := by simp only [Complex.norm_div, norm_neg, ofReal_inv, ofReal_sub, ofReal_one, sub_add_cancel]
            _ ≤ ‖(- ζ' σ₀ / ζ σ₀ - (σ₀ - 1)⁻¹)‖ + ‖(σ₀ - 1)⁻¹‖ := by
              have Z := norm_add_le (- ζ' σ₀ / ζ σ₀ - (σ₀ - 1)⁻¹) ((σ₀ - 1)⁻¹)
              norm_cast at Z
            _ ≤ const + ‖(σ₀ - 1)⁻¹‖ := by
              have U := add_le_add_left bdd ‖(σ₀ - 1)⁻¹‖
              ring_nf at U
              ring_nf
              norm_cast at U
              norm_cast
            _ ≤ const + (σ₀ - 1)⁻¹ := by
              simp [norm_inv]
              have pos : 0 ≤ σ₀ - 1 := by
                linarith
              simp [abs_of_nonneg pos]
            _ = (σ₀ - 1)⁻¹ + const := by
              rw [add_comm]
            _ ≤ (σ₀ - 1)⁻¹ + final_const := by
              simp [const_le_final_const]

        exact Z

      · push Not at h

        have boundary_geq_one : 1 < boundary := by
          unfold boundary
          have Z : (1 : ENNReal).toReal = 1 := by rfl
          rw [←Z]
          have U : ε_div_two ≠ ⊤ := by
            refine ENNReal.div_ne_top O1 ?_
            simp
          simp
          simp [ENNReal.toReal_add _ U]
          refine ENNReal.toReal_pos ?_ ?_
          · unfold ε_div_two
            simp [*]
          · exact U

        have boundary_in_ball : (↑boundary : ℂ) ∈ metric_ball_around_1 := by
          unfold metric_ball_around_1
          unfold Metric.eball
          simp [*]
          have Z := edist_dist (↑boundary) (↑1 : ℂ)
          rw [Z]
          have U := dist_eq_norm (↑boundary) (↑1 : ℂ)
          rw [U]
          norm_cast
          have U : 0 ≤ boundary - 1 := by linarith
          have U1 : ‖boundary - 1‖ = boundary - 1 := by exact norm_of_nonneg U
          have U2 : ε ≠ ⊤ := by exact O1
          have U3 : 0 ≤ ε := by exact zero_le
          simp [Real.norm_of_nonneg U]
          simp [ENNReal.ofReal_lt_iff_lt_toReal U U2]
          have U4 : ENNReal.ofReal 1 ≠ ⊤ := by exact ENNReal.ofReal_ne_top
          have Z0 : ε_div_two.toReal < ε.toReal := by
            have T1 : ε ≠ ⊤ := by exact U2
            have T2 : ε ≠ 0 := by exact O2
            have T3 : ε_div_two < ε := by
              refine ENNReal.half_lt_self ?_ U2
              exact T2

            exact ENNReal.toReal_strict_mono T1 T3

          have Z := by
            calc
              boundary - 1 ≤ boundary - 1 := by linarith
              _ = ENNReal.toReal (1 + ε_div_two) - 1 := rfl
              _ = ENNReal.toReal (1 + ε_div_two) - ENNReal.toReal (ENNReal.ofReal 1) := by simp
              _ ≤ ENNReal.toReal (1 + ε_div_two - ENNReal.ofReal 1) := ENNReal.le_toReal_sub U4
              _ = ENNReal.toReal (ε_div_two) := by simp only [ENNReal.ofReal_one, ENNReal.addLECancellable_iff_ne, ne_eq, ENNReal.one_ne_top, not_false_eq_true, AddLECancellable.add_tsub_cancel_left]
              _ < ε.toReal := Z0

          exact Z

        have boundary_in_U : (↑boundary : ℂ) ∈ U \ {1} := by
          refine mem_sdiff_singleton.mpr ?_
          constructor
          · unfold metric_ball_around_1 at boundary_in_ball
            exact metric_ball_around_1_is_in_U boundary_in_ball
          · by_contra a
            norm_cast at a
            norm_cast at boundary_geq_one
            simp [←a] at boundary_geq_one

        have bdd := Set.forall_mem_image.mp bound_prop (boundary_in_U)

        have Z :=
          calc
            ‖- ζ' (σ₀ + t * I) / ζ (σ₀ + t * I)‖ ≤ ‖ζ' boundary / ζ boundary‖ := by
               have U := strongPnt_dlog_riemannZeta_bdd_on_vertical_lines_generalized boundary σ₀ t (boundary_geq_one) (by linarith)
               exact U
            _ = ‖- ζ' boundary / ζ boundary‖ := by simp only [Complex.norm_div, norm_neg]
            _ = ‖(- ζ' boundary / ζ boundary - (boundary - 1)⁻¹) + (boundary - 1)⁻¹‖ := by simp only [Complex.norm_div, norm_neg, ofReal_inv, ofReal_sub, ofReal_one, sub_add_cancel]
            _ ≤ ‖(- ζ' boundary / ζ boundary - (boundary - 1)⁻¹)‖ + ‖(boundary - 1)⁻¹‖ := by
              have Z := norm_add_le (- ζ' boundary / ζ boundary - (boundary - 1)⁻¹) ((boundary - 1)⁻¹)
              norm_cast at Z
            _ ≤ const + ‖(boundary - 1)⁻¹‖ := by
              have U9 := add_le_add_left bdd ‖(boundary - 1)⁻¹‖
              ring_nf at U9
              ring_nf
              norm_cast at U9
              norm_cast
              simp [*] at U9
              simp [*]
              exact U9

            _ ≤ const + (boundary - 1)⁻¹ := by
              simp [norm_inv]
              have pos : 0 ≤ boundary - 1 := by
                linarith
              simp [abs_of_nonneg pos]
            _ = (boundary - 1)⁻¹ + const := by
              rw [add_comm]
            _ = final_const := by rfl
            _ ≤ (σ₀ - 1)⁻¹ + final_const := by
              have H : 0 ≤ (σ₀ - 1)⁻¹ := by
                simp
                linarith

              simp [H]

        exact Z




theorem dlog_riemannZeta_bdd_on_vertical_lines {σ₀ : ℝ} (σ₀_gt : 1 < σ₀)  :
  ∃ c > 0, ∀(t : ℝ), ‖ζ' (σ₀ + t * I) / ζ (σ₀ + t * I)‖ ≤ c := by

    let s_re : ℂ  := σ₀

    let new_const : ℝ := 1 + (↑(Norm.norm (∑' (n : ℕ), ‖LSeries.term (fun x ↦ Λ x) (↑ s_re : ℂ ) n‖)) : ℝ )
    have new_const_is_pos : new_const > 0 := by positivity

    use new_const
    use new_const_is_pos
    intro t

    let s := σ₀ + t * I

    have DD : (↑ s.re : ℂ)  = s_re := by
      refine ofReal_inj.mpr ?_
      rw [add_re, ofReal_re, mul_re, ofReal_re, I_re, I_im]
      simp

    have L : s_re = σ₀ := by rfl

    have H : s.re = σ₀ := by
          rw [add_re, ofReal_re, mul_re, ofReal_re, I_re, I_im]
          simp

    have non_neg : σ₀ ≠ 0 := by
      by_contra h
      rw [h] at σ₀_gt
      norm_cast at σ₀_gt

    have pos : s.re > 1 := by exact lt_of_lt_of_eq σ₀_gt (id (Eq.symm H))
    have pos_triv : s_re.re > 1 := by exact σ₀_gt

    rw [← norm_neg, ← neg_div, ← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div pos]

    have identity0 : ∀(n : ℕ), ‖LSeries.term 1 s n‖ = 1 / n^σ₀ := by
      unfold LSeries.term
      intro n
      by_cases h0 : n = 0
      · simp [*]
      · simp [*]
        push Not at h0
        have C : n > 0 := by exact Nat.zero_lt_of_ne_zero h0
        have T :=  Complex.norm_natCast_cpow_of_pos C s
        rw [H] at T
        exact T

    have O : ∀(s : ℂ), ∀(n : ℕ), s.re = σ₀ → (↑(‖LSeries.term (fun x ↦ (Λ x)) s n‖ : ℝ) : ℂ) = LSeries.term (fun x ↦ Λ x) (↑ s.re : ℂ ) n := by
      intro s n cond
                                    
      by_cases h1 : (n = 0)
      · simp [h1]
      · push Not at h1
        unfold LSeries.term
        simp [*]
        have U : |Λ n| = Λ n := abs_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg)
        have R : n > 0 := by exact Nat.zero_lt_of_ne_zero h1
        rw [U]
        have Z := Complex.norm_natCast_cpow_of_pos R s
        rw [Z]
        rw [← L]
                   
        by_cases h : (Λ n = 0)
        · simp [h]
        · norm_cast
          apply_fun (fun (w : ℂ) ↦ w * (↑ n : ℂ)^s_re  / (Λ n))
          · simp [*]
            ring_nf
            rw [mul_comm]
            nth_rewrite 1 [mul_assoc]
            simp [*]
            have := cast_pow_eq n σ₀
            rw [this]
            simp [*]

          · have G : (↑ n : ℂ)^s_re  / (Λ n) ≠ 0 := by
              have T : (↑ n : ℂ)^s_re ≠ 0 := by
                have T : n > 0 := by exact R
                have M : ∃(m : ℕ), n = m + 1 := by exact Nat.exists_eq_succ_of_ne_zero h1
                let ⟨m, pf⟩ := M
                have U := Complex.natCast_add_one_cpow_ne_zero m s_re
                rw [pf]
                push_cast
                exact U
              refine div_ne_zero T ?_
              push Not at h
              norm_cast
            have U := by exact mul_left_injective₀ G
            have T : (fun (x : ℂ) ↦ x * (↑ n : ℂ)^s_re  / (Λ n)) = (fun (x : ℂ) ↦ x * ((↑ n : ℂ)^s_re  / (Λ n))) := by funext x; exact mul_div_assoc x (↑n ^ s_re) ↑(Λ n)
            simp [←T] at U
            exact U

    have K : (fun (n : ℕ) ↦ ↑(‖LSeries.term (fun x ↦ (Λ x)) s n‖ : ℝ)) = (fun (n : ℕ) ↦ (LSeries.term (fun x ↦ Λ x) (↑ s.re : ℂ )  n )) := by
      funext n
      rw [O s n H]

    have K1 : (fun (n : ℕ) ↦ ↑(‖LSeries.term (fun x ↦ (Λ x)) (↑ s.re : ℂ) n‖ : ℝ)) = (fun (n : ℕ) ↦ (LSeries.term (fun x ↦ Λ x) (↑ s.re : ℂ )  n )) := by
      funext n
      rw [O (↑ s.re : ℂ) n H]
      simp [*]

    have D2 :  (fun (n : ℕ) ↦ ↑(‖LSeries.term (fun x ↦ (Λ x)) s n‖ : ℝ)) = (fun (n : ℕ) ↦ ↑(‖LSeries.term (fun x ↦ (Λ x)) (↑ s.re : ℂ)  n‖ : ℝ)) := by
      simp [← K]

    have S : Summable (fun n ↦ (↑(‖LSeries.term (fun x ↦ Λ x) s n‖ : ℝ) : ℝ  )) := by
      apply (summable_real_iff_summable_coe_complex (fun n ↦ (↑(‖LSeries.term (fun x ↦ Λ x) s n‖ : ℝ) : ℝ  ))).mpr
      rw [K]
      have T := ArithmeticFunction.LSeriesSummable_vonMangoldt (pos_triv)
      have U : s_re = s.re := by exact congrFun (congrArg Complex.mk (id (Eq.symm H))) 0
      simp [← U]
      exact T

    have C := calc
      ‖∑' (n : ℕ), (LSeries.term (fun x ↦ Λ x) s n)‖ ≤ ∑' (n : ℕ), ‖LSeries.term (fun x ↦ Λ x) s n‖ := norm_tsum_le_tsum_norm S
                                                                                                                                
      _                                              ≤ norm (∑' (n : ℕ), ‖LSeries.term (fun x ↦ Λ x) s n‖) := by exact le_norm_self (∑' (n : ℕ), ‖LSeries.term (fun x ↦ ↑(Λ x)) s n‖)
      _                                              = norm (∑' (n : ℕ), ‖LSeries.term (fun x ↦ Λ x) (↑ s.re : ℂ) n‖) := by simp [D2]
      _                                              ≤ 1 + norm (∑' (n : ℕ), ‖LSeries.term (fun x ↦ Λ x) ( ↑ s.re : ℂ) n‖ ) := by linarith
      _                                              = new_const := by rw [DD]

    exact C

theorem dlog_riemannZeta_bdd_on_vertical_lines' {σ₀ : ℝ} (σ₀_gt : 1 < σ₀) :
  ∃ C > 0, ∀ (t : ℝ), ‖ζ' (σ₀ + t * I) / ζ (σ₀ + t * I)‖ ≤ C :=
  dlog_riemannZeta_bdd_on_vertical_lines σ₀_gt

theorem SmoothedChebyshevPull1_aux_integrable {SmoothingF : ℝ → ℝ} {ε : ℝ} (ε_pos : 0 < ε)
    (ε_lt_one : ε < 1)
    {X : ℝ} (X_gt : 3 < X)
    {σ₀ : ℝ} (σ₀_gt : 1 < σ₀) (σ₀_le_2 : σ₀ ≤ 2)
    (suppSmoothingF : support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ (x : ℝ) in Ioi 0, SmoothingF x / x = 1)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    :
    Integrable (fun (t : ℝ) ↦
      SmoothedChebyshevIntegrand SmoothingF ε X (σ₀ + (t : ℂ) * I)) volume := by
  obtain ⟨C, C_pos, hC⟩ := dlog_riemannZeta_bdd_on_vertical_lines' σ₀_gt
  let c : ℝ := C * X ^ σ₀
  have : ∀ t, ‖(fun (t : ℝ) ↦ (- deriv riemannZeta (σ₀ + (t : ℂ) * I)) /
    riemannZeta (σ₀ + (t : ℂ) * I) *
    (X : ℂ) ^ (σ₀ + (t : ℂ) * I)) t‖ ≤ c := by
    intro t
    simp only [Complex.norm_mul, c]
    gcongr
    · simpa only [neg_div, norm_neg] using hC t

    · rw [Complex.norm_cpow_eq_rpow_re_of_nonneg]
      · simp
      · linarith
      · simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
        add_zero, ne_eq]
        linarith
  convert! (preTransparency := .instances) (SmoothedChebyshevDirichlet_aux_integrable ContDiffSmoothingF SmoothingFnonneg
    suppSmoothingF mass_one ε_pos ε_lt_one σ₀_gt σ₀_le_2).bdd_mul (c := c) ?_ (Filter.Eventually.of_forall this) using 2
  · unfold SmoothedChebyshevIntegrand
    ring
  · apply Continuous.aestronglyMeasurable
    apply continuousOn_univ.mp
    intro t _
    let s := σ₀ + (t : ℂ) * I
    have s_ne_one : s ≠ 1 := by
      intro h
                                                               
      have : σ₀ = 1 := by
        have := congr_arg Complex.re h
        simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
          sub_self, add_zero, one_re, s] at this
        exact this
                                    
      linarith [σ₀_gt]
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.mul
    · have diffζ := differentiableAt_riemannZeta s_ne_one
      apply ContinuousAt.div
      · apply ContinuousAt.neg
        have : DifferentiableAt ℂ (fun s ↦ deriv riemannZeta s) s :=
          differentiableAt_deriv_riemannZeta s_ne_one
        convert (preTransparency := .instances) realDiff_of_complexDiff (s := σ₀ + (t : ℂ) * I) this <;> simp
      · convert (preTransparency := .instances) realDiff_of_complexDiff (s := σ₀ + (t : ℂ) * I) diffζ <;> simp
      · apply riemannZeta_ne_zero_of_one_lt_re
        simp [σ₀_gt]
    · apply ContinuousAt.comp _ (by fun_prop)
      apply continuousAt_const_cpow
      norm_cast
      linarith









theorem norm_reciprocal_inequality_1 (x : ℝ) (x₁ : ℝ) (hx₁ : x₁ ≥ 1) :
  ‖x^2 + x₁^2‖₊⁻¹ ≤ (‖x₁‖₊^2)⁻¹ := by
                                                
  have h1 : x₁^2 ≥ 1 := by
    have h_abs : |x₁| ≥ 1 := by
      rw [abs_of_pos]
      linarith
      positivity
    simp only [ge_iff_le, one_le_sq_iff_one_le_abs, h_abs]

  have h2 : x^2 + x₁^2 ≥ x₁^2 := by
    linarith [sq_nonneg x]

  have h3 : x₁^2 > 0 := by
    apply sq_pos_of_ne_zero
    linarith

  have h33 : 2 * x₁^2 > 0 := by
    simp [*]

  have h4 : x^2 + x₁^2 > 0 := by
    linarith [sq_nonneg x, h3]

  have h5 : x₁^2 ≤ x^2 + x₁^2 := h2

  have h6 : ‖x₁^2‖₊ = ‖x₁‖₊^2 := by
    rw [nnnorm_pow]

  have h7 : ‖x^2 + x₁^2‖₊ = x^2 + x₁^2 := by
    rw [Real.nnnorm_of_nonneg (le_of_lt h4)]
    norm_cast

  rw [← NNReal.coe_le_coe]
  push_cast
  simp [*]
  simp_all
  rw [abs_of_nonneg]
  · have U := inv_le_inv₀ h4 h3
    rw [U]
    simp [*]

  · positivity

theorem norm_reciprocal_inequality (x : ℝ) (x₁ : ℝ) (hx₁ : x₁ ≤ -1) :
  ‖x^2 + x₁^2‖₊⁻¹ ≤ (‖x₁‖₊^2)⁻¹ := by
                                                
  have h1 : x₁^2 ≥ 1 := by
    have h_abs : |x₁| ≥ 1 := by
      rw [abs_of_nonpos (le_of_lt (lt_of_le_of_lt hx₁ (by norm_num : (-1 : ℝ) < 0)))]
      linarith
    simp only [ge_iff_le, one_le_sq_iff_one_le_abs, h_abs]

  have h2 : x^2 + x₁^2 ≥ x₁^2 := by
    linarith [sq_nonneg x]

  have h3 : x₁^2 > 0 := by
    apply sq_pos_of_ne_zero
    linarith

  have h33 : 2 * x₁^2 > 0 := by
    simp [*]

  have h4 : x^2 + x₁^2 > 0 := by
    linarith [sq_nonneg x, h3]

  have h5 : x₁^2 ≤ x^2 + x₁^2 := h2

  have h6 : ‖x₁^2‖₊ = ‖x₁‖₊^2 := by
    rw [nnnorm_pow]

  have h7 : ‖x^2 + x₁^2‖₊ = x^2 + x₁^2 := by
    rw [Real.nnnorm_of_nonneg (le_of_lt h4)]
    norm_cast

  rw [← NNReal.coe_le_coe]
  push_cast
  simp [*]
  simp_all
  rw [abs_of_nonneg]
  · have U := inv_le_inv₀ h4 h3
    rw [U]
    simp [*]

  · positivity

theorem poisson_kernel_integrable (x : ℝ) (hx : x ≠ 0) :
  MeasureTheory.Integrable (fun (t : ℝ) ↦ (‖x + t * I‖^2)⁻¹) := by
                                     
  have h1 : ∀ t : ℝ, ‖x + t * I‖^2 = x^2 + t^2 := by
    intro t
    rw [Complex.norm_add_mul_I, Real.sq_sqrt]
    positivity
                                                    
  have h2 : (fun (t : ℝ) ↦ (‖x + t * I‖^2)⁻¹) = (fun (t : ℝ) ↦ (x^2 + t^2)⁻¹) := by
    ext t
    rw [h1]
  rw [h2]
                                                 
  have h3 : ∀ t : ℝ, x^2 + t^2 > 0 := by
    intro t
    apply add_pos_of_pos_of_nonneg
    · exact sq_pos_of_ne_zero hx
    · exact sq_nonneg t
                                          
  have h4 : Continuous (fun t : ℝ ↦ (x^2 + t^2)⁻¹) := by
    apply Continuous.inv₀
    · exact continuous_const.add (continuous_pow 2)
    · intro t
      exact ne_of_gt (h3 t)

  have integrable_on_bounded : ∀ R > 0, MeasureTheory.IntegrableOn (fun t : ℝ ↦ (x^2 + t^2)⁻¹) (Set.Icc (-R) R) := by
    intro R hR
    refine ContinuousOn.integrableOn_Icc ?_
    · exact Continuous.continuousOn h4

  have decay_bound : ∀ t : ℝ, 0 < |t| → (x^2 + t^2)⁻¹ ≤ (t^2)⁻¹ := by
    intro t hyp_t
    rw [←inv_le_inv₀]
    simp_all only [ne_eq, gt_iff_lt, abs_pos, inv_inv, le_add_iff_nonneg_left]
    · positivity
    · simp_all only [ne_eq, gt_iff_lt, abs_pos, inv_pos]
      positivity
    · positivity

  have decay_bound_1 : ∀ x_1 ≤ -1, ‖x ^ 2 + x_1 ^ 2‖₊⁻¹ ≤ (‖x_1‖₊ ^ 2)⁻¹ := by
    exact norm_reciprocal_inequality x

  have decay_bound_2 : ∀ (x_1 : ℝ), 1 ≤ x_1 → ‖x ^ 2 + x_1 ^ 2‖₊⁻¹ ≤ (‖x_1‖₊ ^ 2)⁻¹ := by
    exact norm_reciprocal_inequality_1 x

  have f_int_1 : IntegrableOn (fun (t : ℝ) ↦ (t^2)⁻¹) (Set.Iic (-1)) volume := by
    have D1 : (-2) < (-1 : ℝ) := by simp_all only [ne_eq, gt_iff_lt, abs_pos, neg_lt_neg_iff,
      Nat.one_lt_ofNat]
    have D2 : 0 < (1 : ℝ) := by simp only [zero_lt_one]
    have D := integrableOn_Ioi_rpow_of_lt D1 D2
    have D3 := MeasureTheory.IntegrableOn.comp_neg D
    simp only [rpow_neg_ofNat, Int.reduceNeg, zpow_neg, neg_Ioi] at D3
    have D4 :=
      (integrableOn_Iic_iff_integrableOn_Iio'
        (by
          refine EReal.coe_ennreal_ne_coe_ennreal_iff.mp ?_
          · simp_all only [ne_eq, gt_iff_lt, abs_pos, neg_lt_neg_iff, Nat.one_lt_ofNat,
            zero_lt_one, rpow_neg_ofNat, Int.reduceNeg, zpow_neg, measure_singleton,
            EReal.coe_ennreal_zero, EReal.coe_ennreal_top, EReal.zero_ne_top, not_false_eq_true])).mpr D3
    simp_all only [ne_eq, gt_iff_lt, abs_pos, neg_lt_neg_iff, Nat.one_lt_ofNat, zero_lt_one,
      rpow_neg_ofNat, Int.reduceNeg, zpow_neg]
    unfold IntegrableOn at D4
    have eq_fun : (fun (x : ℝ) ↦ ((-x)^2)⁻¹) = fun x ↦ (x^2)⁻¹ := by
      funext x
      simp_all only [even_two, Even.neg_pow]
    simp_all only [even_two, Even.neg_pow]
    norm_cast at D4
    simp_all only [even_two, Even.neg_pow, Int.reduceNegSucc, Int.cast_neg, Int.cast_one]
    exact D4

  have f_int_2 : IntegrableOn (fun (t : ℝ) ↦ (t^2)⁻¹) (Set.Ici 1) volume := by
    have D1 : (-2) < (-1 : ℝ) := by simp_all only [ne_eq, gt_iff_lt, abs_pos, neg_lt_neg_iff,
      Nat.one_lt_ofNat]
    have D2 : 0 < (1 : ℝ) := by simp only [zero_lt_one]
    have D3 := integrableOn_Ioi_rpow_of_lt D1 D2
    simp only [rpow_neg_ofNat, Int.reduceNeg, zpow_neg] at D3
    have D4 :=
      (integrableOn_Ici_iff_integrableOn_Ioi'
        (by
          refine EReal.coe_ennreal_ne_coe_ennreal_iff.mp ?_
          · simp_all only [ne_eq, gt_iff_lt, abs_pos, neg_lt_neg_iff, Nat.one_lt_ofNat,
            zero_lt_one, measure_singleton, EReal.coe_ennreal_zero, EReal.coe_ennreal_top,
            EReal.zero_ne_top, not_false_eq_true])).mpr D3
    simp_all only [ne_eq, gt_iff_lt, abs_pos, neg_lt_neg_iff, Nat.one_lt_ofNat, zero_lt_one]
    unfold IntegrableOn at D4
    have eq_fun : (fun (x : ℝ) ↦ ((-x)^2)⁻¹) = fun x ↦ (x^2)⁻¹ := by
      funext x
      simp_all only [even_two, Even.neg_pow]
    simp_all only [even_two, Even.neg_pow]
    norm_cast at D4

  have int_neg : IntegrableOn (fun t : ℝ ↦ (x^2 + t^2)⁻¹) (Set.Iic (-1)) volume := by
    have h_le : ∀ t ∈ Set.Iic (-1), (x^2 + t^2)⁻¹ ≤ (t^2)⁻¹ := by
      intro t ht
      simp only [Set.mem_Iic] at ht
                                                    
      have t_neg : t < 0 := lt_of_le_of_lt ht (by norm_num : (-1 : ℝ) < 0)
      exact decay_bound t (abs_pos.mpr (ne_of_lt t_neg))
    have h_meas : AEStronglyMeasurable (fun t : ℝ ↦ (x^2 + t^2)⁻¹) (volume.restrict (Set.Iic (-1))) := by
      exact Continuous.aestronglyMeasurable h4

    unfold IntegrableOn
    unfold Integrable
    constructor
    · exact h_meas
    · have Z : HasFiniteIntegral (fun t : ℝ ↦ (x^2 + t^2)⁻¹) (volume.restrict (Iic (-1))) := by
        refine MeasureTheory.HasFiniteIntegral.mono'_enorm f_int_1.2 ?_
        · unfold Filter.Eventually
          simp only [measurableSet_Iic, ae_restrict_eq, nnnorm_inv, nnnorm_pow, enorm_le_coe]
          refine mem_inf_of_right ?_
          · refine mem_principal.mpr ?_
            · rw [Set.subset_def]
              simp only [mem_Iic, mem_ofPred_eq]
              exact decay_bound_1

      exact Z

  have int_pos : IntegrableOn (fun t : ℝ ↦ (x^2 + t^2)⁻¹) (Set.Ici 1) volume := by
    have h_le : ∀ t ∈ Set.Ici 1, (x^2 + t^2)⁻¹ ≤ (t^2)⁻¹ := by
      intro t ht
      simp only [Set.mem_Ici] at ht
                                                   
      have t_pos : t > 0 := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) ht
      exact decay_bound t (abs_pos.mpr (ne_of_gt t_pos))
    have h_meas : AEStronglyMeasurable (fun t : ℝ ↦ (x^2 + t^2)⁻¹) (volume.restrict (Set.Ici 1)) := by
      exact Continuous.aestronglyMeasurable h4

    unfold IntegrableOn
    unfold Integrable
    constructor
    · exact h_meas
    · have Z : HasFiniteIntegral (fun t : ℝ ↦ (x^2 + t^2)⁻¹) (volume.restrict (Ici (1))) := by
        refine MeasureTheory.HasFiniteIntegral.mono'_enorm f_int_2.2 ?_
        · unfold Filter.Eventually
          simp only [measurableSet_Ici, ae_restrict_eq, nnnorm_inv, nnnorm_pow, enorm_le_coe]
          refine mem_inf_of_right ?_
          · refine mem_principal.mpr ?_
            · rw [Set.subset_def]
              simp only [mem_Ici, mem_ofPred_eq]
              exact decay_bound_2

      exact Z

  have split : Set.univ = Set.Iic (-1) ∪ Set.Icc (-1) 1 ∪ Set.Ici 1 := by
    ext t
    simp only [Set.mem_univ, Set.mem_union, Set.mem_Iic, Set.mem_Icc, Set.mem_Ici, true_iff]
    by_cases h : t ≤ -1
    · left; left; exact h
    · by_cases h' : t ≥ 1
      · right; exact h'
      · left; right; constructor <;> linarith

  have Z :=
    MeasureTheory.IntegrableOn.union
      (MeasureTheory.IntegrableOn.union
          (int_neg)
          (integrable_on_bounded 1 zero_lt_one))
      (int_pos)

  simp_all only [ne_eq, gt_iff_lt, abs_pos, Int.reduceNeg, neg_le_self_iff, zero_le_one, Iic_union_Icc_eq_Iic,
  Iic_union_Ici, integrableOn_univ]

theorem ae_volume_of_contains_compl_singleton_zero                                                                             
  (s : Set ℝ)
  (h : (univ : Set ℝ) \ {0} ⊆ s) :
  s ∈ (MeasureTheory.ae volume) := by
                                                      
  have h_zero_null : volume ({0} : Set ℝ) = 0 := by
    exact volume_singleton

  have h_compl_subset : sᶜ ⊆ {0} := by
    intro x hx

    by_contra h_not_zero
    have : x ∈ univ \ {0} := ⟨trivial, h_not_zero⟩
    exact hx (h this)

  have h_compl_measure : volume sᶜ ≤ volume ({0} : Set ℝ) :=
    measure_mono h_compl_subset

  have h_compl_zero : volume sᶜ = 0 := by
    rw [h_zero_null] at h_compl_measure
    exact le_antisymm h_compl_measure zero_le

  rwa [mem_ae_iff]

theorem integral_evaluation (x : ℝ) (T : ℝ)
  : (3 < T) → ∫ (t : ℝ) in Iic (-T), (‖x + t * I‖ ^ 2)⁻¹ ≤ T⁻¹ := by

  intro T_large

  have T00 : ∀ (x t : ℝ), t^2 ≤ ‖x + t * I‖^2 := by
    intro x t
    rw [Complex.norm_add_mul_I x t]
    ring_nf
    rw [Real.sq_sqrt _]
    simp only [le_add_iff_nonneg_right]; positivity
    positivity

  have T0 : ∀ (x t : ℝ), t ≠ 0 → (‖x + t * I‖^2)⁻¹ ≤ (t^2)⁻¹ := by
    intro x t hyp
    have U0 : 0 < t^2 := by positivity
    have U1 : 0 < ‖x + t * I‖^2 := by
      rw [Complex.norm_add_mul_I x t]
      rw [Real.sq_sqrt _]
      positivity
      positivity
    rw [inv_le_inv₀ U1 U0]
    exact (T00 x t)

  have T1 : (fun (t : ℝ) ↦ (‖x + t * I‖^2)⁻¹) ≤ᶠ[ae (volume.restrict (Iic (-T)))] (fun (t : ℝ) ↦ (t^2)⁻¹) := by
    unfold Filter.EventuallyLE
    unfold Filter.Eventually
    simp_all only [ne_eq, measurableSet_Iic, ae_restrict_eq]
    refine mem_inf_of_left ?_
    · refine Filter.mem_sets.mp ?_
      · have U :  {x_1 : ℝ | x_1 ≠ 0} ⊆ {x_1 : ℝ | (‖x + x_1 * I‖ ^ 2)⁻¹ ≤ (x_1 ^ 2)⁻¹}  := by
          rw [Set.ofPred_subset_ofPred]
          intro t hyp_t
          exact T0 x t hyp_t
        have U1 : {x_1 : ℝ | x_1 ≠ 0} = (univ \ {0}) := by
          apply Set.ext
          intro x
          simp_all only [ne_eq, ofPred_subset_ofPred, not_false_eq_true, implies_true, mem_ofPred_eq, Set.mem_sdiff, mem_univ,
  mem_singleton_iff, true_and]

        rw [U1] at U
        have Z := ae_volume_of_contains_compl_singleton_zero
          ({x_1 : ℝ | (‖x + x_1 * I‖ ^ 2)⁻¹ ≤ (x_1 ^ 2)⁻¹} : Set ℝ) U
        exact Z

  have T2 : 0 ≤ᶠ[ae (volume.restrict (Iic (-T)))] (fun (t : ℝ) ↦ (‖x + t * I‖^2)⁻¹) := by
    unfold Filter.EventuallyLE
    unfold Filter.Eventually
    simp_all only [ne_eq, Pi.zero_apply, inv_nonneg, norm_nonneg, pow_nonneg,
  ofPred_true, univ_mem]

  have T4 : deriv (fun (t : ℝ) ↦ t⁻¹) = (fun t ↦ (- (t^2)⁻¹)) := by
    exact deriv_inv'

  have hcont : ContinuousWithinAt (fun t ↦ t⁻¹) (Set.Iic (-T)) (-T) := by
    refine ContinuousWithinAt.inv₀ ?_ ?_
    · exact ContinuousAt.continuousWithinAt fun ⦃U⦄ a ↦ a
    · intro hyp
      linarith

  have hderiv : ∀ x ∈ Set.Iio (-T), HasDerivAt (fun t ↦ t⁻¹) ((fun t ↦ - (t^2)⁻¹) x) x := by
                                                                                    
    intro x hx
                                            
    have hx_ne_zero : x ≠ 0 := by
      intro h
      rw [h] at hx
      simp [Set.Iio] at hx
      linarith
                                                    
    convert (preTransparency := .instances) hasDerivAt_inv hx_ne_zero

  have f'int : IntegrableOn (fun t ↦ - (t^2)⁻¹) (Set.Iic (-T)) volume := by
    have D1 : (-2) < (-1 : ℝ) := by simp only [neg_lt_neg_iff, Nat.one_lt_ofNat]
    have D2 : 0 < T := by positivity
    have D := integrableOn_Ioi_rpow_of_lt D1 D2
              
    have D3 := MeasureTheory.IntegrableOn.comp_neg D
    simp [*] at D3
    have D4 :=
      (integrableOn_Iic_iff_integrableOn_Iio'
        (by
          refine EReal.coe_ennreal_ne_coe_ennreal_iff.mp ?_
          · simp_all only [ne_eq, measurableSet_Iic, ae_restrict_eq, deriv_inv', mem_Iio, neg_lt_neg_iff,
  Nat.one_lt_ofNat, rpow_neg_ofNat, Int.reduceNeg, zpow_neg, measure_singleton, EReal.coe_ennreal_zero,
  EReal.coe_ennreal_top, EReal.zero_ne_top, not_false_eq_true])).mpr D3
    simp_all only [ne_eq, measurableSet_Iic, ae_restrict_eq, deriv_inv', mem_Iio, neg_lt_neg_iff,
  Nat.one_lt_ofNat, rpow_neg_ofNat, Int.reduceNeg, zpow_neg]
                       
    unfold IntegrableOn at D4
    have eq_fun : (fun (x : ℝ) ↦ ((-x)^2)⁻¹) = fun x ↦ (x^2)⁻¹ := by
      funext x
      simp_all only [even_two, Even.neg_pow]

    simp_all only [even_two, Even.neg_pow]
    have D6 := MeasureTheory.integrable_neg_iff.mpr D4
    have eq_fun : (-fun x ↦ (x^2)⁻¹) = (fun (x : ℝ) ↦ - (x^2)⁻¹) := by
      funext x
      simp only [Pi.neg_apply]
    rw [eq_fun] at D6
    exact D6

  have hf : Filter.Tendsto (fun (t : ℝ) ↦ t⁻¹) Filter.atBot (nhds 0) := by exact
    tendsto_inv_atBot_zero

  have T5 : ∫ (t : ℝ) in Iic (-T), - (t^2)⁻¹ = (-T)⁻¹ - 0 := by
    exact MeasureTheory.integral_Iic_of_hasDerivAt_of_tendsto hcont hderiv f'int hf

  have T6 : ∫ (t : ℝ) in Iic (-T), (t^2)⁻¹ = T⁻¹ := by
    simp only [inv_neg, sub_zero] at T5
    have D6 : - ∫ (t : ℝ) in Iic (-T), - (t^2)⁻¹ =  ∫ (t : ℝ) in Iic (-T), (t^2)⁻¹ := by
      simp only [integral_neg fun a ↦ (a ^ 2)⁻¹, neg_neg]

    rw [←D6]
    rw [T5]
    simp only [neg_neg]

  have T3 : Integrable (fun (t : ℝ) ↦ (t^2)⁻¹) (volume.restrict (Iic (-T))) := by
              
    have D1 : (-2) < (-1 : ℝ) := by simp only [neg_lt_neg_iff, Nat.one_lt_ofNat]
    have D2 : 0 < T := by positivity
    have D := integrableOn_Ioi_rpow_of_lt D1 D2
              
    have D3 := MeasureTheory.IntegrableOn.comp_neg D
    simp only [rpow_neg_ofNat, Int.reduceNeg, zpow_neg, neg_Ioi] at D3
    have D4 :=
      (integrableOn_Iic_iff_integrableOn_Iio'
        (by
          refine EReal.coe_ennreal_ne_coe_ennreal_iff.mp ?_
          · simp_all only [ne_eq, measurableSet_Iic, ae_restrict_eq, deriv_inv', mem_Iio, inv_neg, sub_zero,
  neg_lt_neg_iff, Nat.one_lt_ofNat, rpow_neg_ofNat, Int.reduceNeg, zpow_neg, measure_singleton, EReal.coe_ennreal_zero,
  EReal.coe_ennreal_top, EReal.zero_ne_top, not_false_eq_true])).mpr D3
    simp_all only [ne_eq, measurableSet_Iic, ae_restrict_eq, deriv_inv', mem_Iio, inv_neg, sub_zero,
  neg_lt_neg_iff, Nat.one_lt_ofNat, rpow_neg_ofNat, Int.reduceNeg, zpow_neg]
                       
    unfold IntegrableOn at D4
    have eq_fun : (fun (x : ℝ) ↦ ((-x)^2)⁻¹) = fun x ↦ (x^2)⁻¹ := by
      funext x
      simp_all only [even_two, Even.neg_pow]
    simp_all only [even_two, Even.neg_pow]
    norm_cast at D4
    simp_all only [even_two, Even.neg_pow]

  have Z :=
    by
      calc
        ∫ (t : ℝ) in Iic (-T), (‖x + t * I‖ ^ 2)⁻¹ ≤ ∫ (t : ℝ) in Iic (-T), (t^2)⁻¹  := by
          exact MeasureTheory.integral_mono_of_nonneg T2 T3 T1

        _ = T⁻¹ := by exact T6

  exact Z



theorem I1Bound
    {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2) (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1) :
    ∃ C > 0, ∀(ε : ℝ) (_ : 0 < ε)
    (_ : ε < 1)
    (X : ℝ) (_ : 3 < X)
    {T : ℝ} (_ : 3 < T),
    ‖I₁ SmoothingF ε X T‖ ≤ C * X * Real.log X / (ε * T) := by

  obtain ⟨M, ⟨M_is_pos, M_bounds_mellin_hard⟩⟩ :=
    MellinOfSmooth1b ContDiffSmoothingF suppSmoothingF

  have G0 : ∃K > 0, ∀(t σ : ℝ), 1 < σ → σ < 2 → ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ ≤ K * (σ - 1)⁻¹ := by
    let ⟨K', ⟨K'_pos, K'_bounds_zeta⟩⟩ := strongPnt_triv_bound_zeta
    use (2 * (K' + 1))
    use (by positivity)
    intro t σ cond cond2

    have T0 : 0 < K' + 1 := by positivity
    have T1 : 1 ≤ (σ - 1)⁻¹ := by
      have U : σ - 1 ≤ 1 := by linarith
      have U1 := (inv_le_inv₀ (by positivity) (by exact sub_pos.mpr cond)).mpr U
      simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, mul_inv_rev, ge_iff_le, Complex.norm_div,
  norm_neg, tsub_le_iff_right, inv_one]

    have T : (K' + 1) * 1 ≤ (K' + 1) * (σ - 1)⁻¹ :=
      by
        exact (mul_le_mul_iff_right₀ T0).mpr T1
    have T2 : (K' + 1) ≤ (K' + 1) * (σ - 1)⁻¹ := by
      simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, mul_inv_rev, ge_iff_le, Complex.norm_div,
  norm_neg, mul_one, le_mul_iff_one_le_right]

    have U := calc
      ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ = ‖-ζ' (σ + t * I) / ζ (σ + t * I)‖ := by
        rw [← norm_neg _, mul_comm, neg_div' _ _]
      _ ≤ (σ - 1)⁻¹ + K' := K'_bounds_zeta σ t cond
      _ ≤ (σ - 1)⁻¹ + (K' + 1) := by aesop
      _ ≤ (K' + 1) * (σ - 1)⁻¹ + (K' + 1) := by aesop
      _ ≤ (K' + 1) * (σ - 1)⁻¹ + (K' + 1) * (σ - 1)⁻¹ := by linarith
      _ = 2 * (K' + 1) * (σ - 1)⁻¹ := by
        ring_nf

    exact U

  obtain ⟨K, ⟨K_is_pos, K_bounds_zeta_at_any_t'⟩⟩ := G0

  have C_final_pos : |π|⁻¹ * 2⁻¹ * (Real.exp 1 * K * M) > 0 := by
    positivity

  use (|π|⁻¹ * 2⁻¹ * (Real.exp 1 * K * M))
  use C_final_pos

  intro eps eps_pos eps_less_one X X_large T T_large

  let pts_re := 1 + (Real.log X)⁻¹
  let pts := fun (t : ℝ) ↦ (pts_re + t * I)

  have pts_re_triv : ∀(t : ℝ), (pts t).re = pts_re := by
    intro t
    unfold pts
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero]

  have pts_re_ge_one : 1 < pts_re := by
    unfold pts_re
    simp only [lt_add_iff_pos_right, inv_pos]
    have U : 1 < X := by linarith
    exact Real.log_pos U

  have pts_re_le_one : pts_re < 2 := by
    unfold pts_re
    have Z0 : 3 ∈ {x : ℝ | 1 ≤ x} := by
      simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, mul_inv_rev, gt_iff_lt, Complex.norm_div,
  mem_ofPred_eq, Nat.one_le_ofNat]
    have Z1 : X ∈ {x : ℝ | 1 ≤ x} := by
      simp only [mem_ofPred_eq]
      linarith
    have Z : Real.log 3 < Real.log X :=
      by
        refine log_lt_log ?_ X_large
        simp only [Nat.ofNat_pos]

    have Z01 : 1 < Real.log 3  :=
      by
        have Z001 : 1 = Real.log (rexp 1) := by exact Eq.symm (Real.log_exp 1)
        rw [Z001]
        have Z002 : (0 : ℝ) < rexp 1 := by positivity
        have Z003 : (0 : ℝ) < 3 := by positivity
        have Z004 : rexp 1 < 3 := by
          calc
            rexp 1 < (↑ 2.7182818286 : ℚ) := Real.exp_one_lt_d9
            _ < (↑ 3 : ℚ) := by linarith

        exact (Real.log_lt_log_iff Z002 Z003).mpr Z004

    have Zpos0 : 0 < Real.log 3 := by positivity
    have Zpos1 : 0 < Real.log X := by calc
      0 < Real.log 3 := Zpos0
      _ < Real.log X := Z

    have Z1 : (Real.log X)⁻¹ < (Real.log 3)⁻¹ :=
      by
        exact (inv_lt_inv₀ Zpos1 Zpos0).mpr Z

    have Z02 : (Real.log 3)⁻¹ < 1 := by
      have T01 := (inv_lt_inv₀ ?_ ?_).mpr Z01
      simp only [inv_one] at T01
      exact T01
      exact Zpos0
      simp only [zero_lt_one]

    have Z2 : 1 + (Real.log X)⁻¹ < 1 + (Real.log 3)⁻¹ := by
      exact (add_lt_add_iff_left 1).mpr Z1

    have Z3 : 1 + (Real.log 3)⁻¹ < 2 := by
      calc
        1 + (Real.log 3)⁻¹ < 1 + 1 := by linarith
        _ = 2 := by ring_nf

    calc
      1 + (Real.log X)⁻¹ < 1 + (Real.log 3)⁻¹ := Z2
      _ < 2 := Z3

  have inve : (pts_re - 1)⁻¹ = Real.log X := by
    unfold pts_re
    simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, mul_inv_rev, gt_iff_lt,
      Complex.norm_div, add_sub_cancel_left, inv_inv]

  have K_bounds_zeta_at_any_t : ∀(t : ℝ), ‖ζ' (pts t) / ζ (pts t)‖ ≤ K * Real.log X := by
    intro t
    rw [←inve]
    exact K_bounds_zeta_at_any_t' t pts_re pts_re_ge_one pts_re_le_one

  have pts_re_pos : pts_re > 0 := by
    unfold pts_re
    positivity

  have triv_pts_lo_bound : ∀(t : ℝ), pts_re ≤ (pts t).re := by
    intro t
    unfold pts_re
    exact Eq.ge (pts_re_triv t)

  have triv_pts_up_bound : ∀(t : ℝ), (pts t).re ≤ 2 := by
    intro t
    unfold pts
    refine EReal.coe_le_coe_iff.mp ?_
    · simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, mul_inv_rev, gt_iff_lt,
      Complex.norm_div, le_refl, implies_true, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im,
      I_im, mul_one, sub_self, add_zero, EReal.coe_le_coe_iff]
      exact le_of_lt pts_re_le_one

  have pts_re_ge_1 : pts_re > 1 := by
    unfold pts_re
    exact pts_re_ge_one

  have X_pos_triv : 0 < X := by positivity

  let f := fun (t : ℝ) ↦ SmoothedChebyshevIntegrand SmoothingF eps X (pts t)

  have G : ∀(t : ℝ), ‖f t‖ ≤ (K * M) * Real.log X * (eps * ‖pts t‖^2)⁻¹ * X^pts_re := by

    intro t

    let M_bounds_mellin_easy := fun (t : ℝ) ↦ M_bounds_mellin_hard pts_re pts_re_pos (pts t) (triv_pts_lo_bound t) (triv_pts_up_bound t) eps eps_pos eps_less_one

    let zeta_part := (fun (t : ℝ) ↦ -ζ' (pts t) / ζ (pts t))
    let mellin_part := (fun (t : ℝ) ↦ 𝓜 (fun x ↦ ↑(Smooth1 SmoothingF eps x)) (pts t))
    let X_part := (fun (t : ℝ) ↦ (↑X : ℂ) ^ (pts t))

    let g := fun (t : ℝ) ↦ (zeta_part t) * (mellin_part t) * (X_part t)

    have X_part_eq : ∀(t : ℝ), ‖X_part t‖ = X^pts_re := by
      intro t
      have U := Complex.norm_cpow_eq_rpow_re_of_pos (X_pos_triv) (pts t)
      rw [pts_re_triv t] at U
      exact U

    have X_part_bound : ∀(t : ℝ), ‖X_part t‖ ≤ X^pts_re := by
      intro t
      rw [←X_part_eq]

    have mellin_bound : ∀(t : ℝ), ‖mellin_part t‖ ≤ M * (eps * ‖pts t‖ ^ 2)⁻¹ := by
      intro t
      exact M_bounds_mellin_easy t

    have X_part_and_mellin_bound : ∀(t : ℝ),‖mellin_part t * X_part t‖ ≤ M * (eps * ‖pts t‖^2)⁻¹ * X^pts_re := by
      intro t
      exact norm_mul_le_of_le (mellin_bound t) (X_part_bound t)

    have T2 : ∀(t : ℝ), ‖zeta_part t‖ = ‖ζ' (pts t) / ζ (pts t)‖ := by
      intro t
      unfold zeta_part
      simp only [Complex.norm_div, norm_neg]

    have zeta_bound : ∀(t : ℝ), ‖zeta_part t‖ ≤ K * Real.log X := by
      intro t
      unfold zeta_part
      rw [T2]
      exact K_bounds_zeta_at_any_t t

    have g_bound : ∀(t : ℝ), ‖zeta_part t * (mellin_part t * X_part t)‖ ≤ (K * Real.log X) * (M * (eps * ‖pts t‖^2)⁻¹ * X^pts_re) := by
      intro t
      exact norm_mul_le_of_le (zeta_bound t) (X_part_and_mellin_bound t)

    have T1 : f = g := by rfl

    have final_bound_pointwise : ‖f t‖ ≤ K * Real.log X * (M * (eps * ‖pts t‖^2)⁻¹ * X^pts_re) := by
      rw [T1]
      unfold g
      rw [mul_assoc]
      exact g_bound t

    have trivialize : K * Real.log X * (M * (eps * ‖pts t‖^2)⁻¹ * X^pts_re) = (K * M) * Real.log X * (eps * ‖pts t‖^2)⁻¹ * X^pts_re := by
            ring_nf

    rw [trivialize] at final_bound_pointwise
    exact final_bound_pointwise

  have σ₀_gt : 1 < pts_re := by exact pts_re_ge_1
  have σ₀_le_2 : pts_re ≤ 2 := by
    unfold pts_re
           
    exact
      Preorder.le_trans (1 + (Real.log X)⁻¹) (pts (SmoothingF (SmoothingF M))).re 2
        (triv_pts_lo_bound (SmoothingF (SmoothingF M))) (triv_pts_up_bound (SmoothingF (SmoothingF M)))

  have f_integrable := SmoothedChebyshevPull1_aux_integrable eps_pos eps_less_one X_large σ₀_gt σ₀_le_2 suppSmoothingF SmoothingFnonneg mass_one ContDiffSmoothingF

  have S : X^pts_re = rexp 1 * X := by
    unfold pts_re

    calc
      X ^ (1 + (Real.log X)⁻¹) = X * X ^ ((Real.log X)⁻¹) := by
        refine rpow_one_add' ?_ ?_
        · positivity
        · exact Ne.symm (ne_of_lt pts_re_pos)
      _ = X * rexp 1 := by
        refine (mul_right_inj' ?_).mpr ?_
        · exact Ne.symm (ne_of_lt X_pos_triv)
        · refine rpow_inv_log X_pos_triv ?_
          · by_contra h
            simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, mul_inv_rev, gt_iff_lt,
              Complex.norm_div, Nat.not_ofNat_lt_one]
      _ = rexp 1 * X := by ring_nf

  have pts_re_neq_zero : pts_re ≠ 0 := by
    by_contra h
    rw [h] at pts_re_ge_1
    simp only [gt_iff_lt] at pts_re_ge_1
    norm_cast at pts_re_ge_1

  have Z :=
    by
      calc
        ‖∫ (t : ℝ) in Iic (-T), f t‖ ≤ ∫ (t : ℝ) in Iic (-T), ‖f t‖ := MeasureTheory.norm_integral_le_integral_norm f
        _ ≤ ∫ (t : ℝ) in Iic (-T), (K * M) * Real.log X * (eps * ‖pts t‖ ^ 2)⁻¹ * X ^ pts_re := by
            refine integral_mono ?_ ?_ (fun t ↦ G t)
            · refine Integrable.norm ?_
              · unfold f
                exact MeasureTheory.Integrable.restrict f_integrable
            · have equ : ∀(t : ℝ), (K * M) * Real.log X * (eps * ‖pts t‖ ^ 2)⁻¹ * X ^ pts_re = (K * M) * Real.log X * eps⁻¹ * X ^ pts_re * (‖pts t‖^2)⁻¹ := by
                   intro t; ring_nf
              have fun_equ : (fun (t : ℝ) ↦ ((K * M) * Real.log X * (eps * ‖pts t‖ ^ 2)⁻¹ * X ^ pts_re)) = (fun (t : ℝ) ↦ ((K * M) * Real.log X * eps⁻¹ * X ^ pts_re * (‖pts t‖^2)⁻¹)) := by
                   funext t
                   exact equ t

              rw [fun_equ]
              have nonzero := ((K * M) * Real.log X * eps⁻¹ * X ^ pts_re)
              have simple_int : MeasureTheory.Integrable (fun (t : ℝ) ↦ (‖pts t‖^2)⁻¹)
                := by
                   unfold pts
                   exact poisson_kernel_integrable pts_re (pts_re_neq_zero)

              have U := MeasureTheory.Integrable.const_mul simple_int ((K * M) * Real.log X * eps⁻¹ * X ^ pts_re)
              refine MeasureTheory.Integrable.restrict ?_
              exact U
        _ = (K * M) * Real.log X * X ^ pts_re * eps⁻¹ * ∫ (t : ℝ) in Iic (-T), (‖pts t‖ ^ 2)⁻¹ := by
              have simpli : ∀(t : ℝ), (K * M) * Real.log X * (eps * ‖pts t‖ ^ 2)⁻¹ * X ^ pts_re = (K * M) * Real.log X * X ^ pts_re * eps⁻¹ * (‖pts t‖^2)⁻¹ :=
                by intro t; ring_nf
              have simpli_fun : (fun (t : ℝ) ↦ (K * M) * Real.log X * (eps * ‖pts t‖ ^ 2)⁻¹ * X ^ pts_re ) = (fun (t : ℝ) ↦ ((K * M) * Real.log X * X ^ pts_re * eps⁻¹ * (‖pts t‖^2)⁻¹)) :=
                by funext t; ring_nf
              rw [simpli_fun]
              exact MeasureTheory.integral_const_mul ((K * M) * Real.log X * X ^ pts_re * eps⁻¹) (fun (t : ℝ) ↦ (‖pts t‖^2)⁻¹)
        _ ≤ (K * M) * Real.log X * X ^ pts_re * eps⁻¹ * T⁻¹ := by
              have U := integral_evaluation (pts_re) T (T_large)
              unfold pts
              simp only [ge_iff_le]
              have U2 : 0 ≤ (K * M) * Real.log X * X ^ pts_re * eps⁻¹ := by
                simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, mul_inv_rev, gt_iff_lt,
                  Complex.norm_div, le_refl, implies_true, inv_pos, mul_nonneg_iff_of_pos_right]
                refine Left.mul_nonneg ?_ ?_
                · refine Left.mul_nonneg ?_ ?_
                  · exact Left.mul_nonneg (by positivity) (by positivity)
                  · refine log_nonneg ?_
                    · linarith
                · refine Left.mul_nonneg ?_ ?_
                  · exact exp_nonneg 1
                  · exact le_of_lt X_pos_triv
              have U1 := mul_le_mul_of_nonneg_left U U2

              exact U1
        _ = (Real.exp 1 * K * M) * Real.log X * X * eps⁻¹ * T⁻¹ := by
          rw [S]
          ring_nf
        _ = (Real.exp 1 * K * M) * X * Real.log X / (eps * T) := by ring_nf

  unfold I₁
  unfold f at Z
  unfold pts at Z
  have Z3 : (↑pts_re : ℂ) = 1 + (Real.log X)⁻¹ := by unfold pts_re; norm_cast
  rw [Z3] at Z
  rw [Complex.norm_mul (1 / (2 * ↑π * I)) _]
  simp only [one_div, mul_inv_rev, inv_I, neg_mul, norm_neg, Complex.norm_mul, norm_I, norm_inv,
    norm_real, norm_eq_abs, Complex.norm_ofNat, one_mul, ofReal_inv, ge_iff_le]
  have Z2 : 0 ≤ |π|⁻¹ * 2⁻¹ := by positivity
  simp only [ofReal_inv] at Z
  simp only [ge_iff_le]
  have Z4 :=
    mul_le_mul_of_nonneg_left Z Z2
  ring_nf
  ring_nf at Z4
  exact Z4


















open _root_.Filter _root_.Topology


end Erdos970

end

theorem solution : type_of% @Erdos970.I1Bound := @Erdos970.I1Bound
