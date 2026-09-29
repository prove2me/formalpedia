-- Prove2me | solution 1 for CuspForm.peterssonOn_self_re_nonneg_im_eq_zero_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/964b694d-1ca3-50e5-81bb-2bdffa0169fc

import Mathlib
import Definitions.Def_CuspForm_PeterssonOn
import Definitions.Def_AutomorphicForm_FundamentalDomainVolume
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_peterssonOn_self_re_nonneg_im_eq_zero_eq_zero_iff

set_option autoImplicit false

noncomputable section

open MeasureTheory UpperHalfPlane ModularForm Filter
open scoped MatrixGroups ModularForm ComplexConjugate Modular ENNReal Pointwise

namespace PetOnIP2

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {k : ℤ}

local notation "Γᴳᴸ" => ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

scoped instance sl2zContinuousConstSMul : ContinuousConstSMul SL(2, ℤ) ℍ where
  continuous_const_smul γ := by
    have h : (fun z : ℍ => γ • z) =
        fun z : ℍ => (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) • z := by
      funext z
      exact MulAction.compHom_smul_def (Matrix.SpecialLinearGroup.mapGL ℝ) γ z
    rw [h]
    exact continuous_const_smul _

scoped instance fintypeQuot : Fintype (SL(2, ℤ) ⧸ Γ) :=
  haveI : Finite (SL(2, ℤ) ⧸ Γ) := Subgroup.finite_quotient_of_finiteIndex
  Fintype.ofFinite _

def cosum (Φ : ℍ → ℂ) (x : ℍ) : ℂ := ∑ q : SL(2, ℤ) ⧸ Γ, Φ ((q.out⁻¹ : SL(2, ℤ)) • x)

theorem integrand_eq (F G : ℍ → ℂ) :
    CuspForm.peterssonOnIntegrand Γ k F G = cosum (Γ := Γ) (UpperHalfPlane.petersson k F G) := by
  funext x
  unfold CuspForm.peterssonOnIntegrand cosum
  rw [finsum_eq_sum_of_fintype]
  exact Finset.sum_congr rfl fun q _ => UpperHalfPlane.petersson_slash_SL k F G _ x

theorem petersson_add_right (F G H : ℍ → ℂ) (x : ℍ) :
    UpperHalfPlane.petersson k F (G + H) x
      = UpperHalfPlane.petersson k F G x + UpperHalfPlane.petersson k F H x := by
  simp only [UpperHalfPlane.petersson, Pi.add_apply]; ring

theorem petersson_smul_right (F G : ℍ → ℂ) (c : ℂ) (x : ℍ) :
    UpperHalfPlane.petersson k F (c • G) x = c * UpperHalfPlane.petersson k F G x := by
  simp only [UpperHalfPlane.petersson, Pi.smul_apply, smul_eq_mul]; ring

theorem cosum_add (Φ Ψ : ℍ → ℂ) : cosum (Γ := Γ) (Φ + Ψ) = cosum (Γ := Γ) Φ + cosum (Γ := Γ) Ψ := by
  funext x; simp [cosum, Finset.sum_add_distrib]

theorem cosum_const_mul (c : ℂ) (Φ : ℍ → ℂ) :
    cosum (Γ := Γ) (fun x => c * Φ x) = fun x => c * cosum (Γ := Γ) Φ x := by
  funext x; simp [cosum, Finset.mul_sum]

theorem measurable_smul_SL (γ : SL(2, ℤ)) : Measurable (fun x : ℍ => γ • x) :=
  (continuous_const_smul γ).measurable

theorem continuous_cosum {Φ : ℍ → ℂ} (hΦ : Continuous Φ) : Continuous (cosum (Γ := Γ) Φ) :=
  continuous_finsetSum _ fun _ _ => hΦ.comp (continuous_const_smul _)

theorem integrable_cosum {Φ : ℍ → ℂ} (hΦ : Continuous Φ) (hbd : ∃ C, ∀ x, ‖Φ x‖ ≤ C) :
    Integrable (cosum (Γ := Γ) Φ) (volume.restrict (𝒟 : Set ℍ)) := by
  obtain ⟨C, hC⟩ := hbd
  refine Measure.integrableOn_of_bounded (M := ∑ _q : SL(2, ℤ) ⧸ Γ, C)
    FLT.FundamentalDomainVolume.volume_fd_lt_top.ne (continuous_cosum hΦ).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun x => ?_
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => hC _)

theorem petersson_bounded (f g : CuspForm Γᴳᴸ k) :
    ∃ C, ∀ x, ‖UpperHalfPlane.petersson k ⇑f ⇑g x‖ ≤ C :=
  CuspFormClass.petersson_bounded_left k Γᴳᴸ f g

omit [Γ.FiniteIndex] in
theorem petersson_continuous' (f g : CuspForm Γᴳᴸ k) : Continuous (UpperHalfPlane.petersson k ⇑f ⇑g) :=
  UpperHalfPlane.petersson_continuous k (CuspFormClass.holo f).continuous (CuspFormClass.holo g).continuous

theorem integrable_integrand (f g : CuspForm Γᴳᴸ k) :
    Integrable (CuspForm.peterssonOnIntegrand Γ k ⇑f ⇑g) (volume.restrict (𝒟 : Set ℍ)) := by
  rw [integrand_eq]
  exact integrable_cosum (petersson_continuous' f g) (petersson_bounded f g)

def dens (f : CuspForm Γᴳᴸ k) (x : ℍ) : ℝ := ‖f x‖ ^ 2 * x.im ^ k

omit [Γ.FiniteIndex] in
theorem dens_nonneg (f : CuspForm Γᴳᴸ k) (x : ℍ) : 0 ≤ dens f x :=
  mul_nonneg (sq_nonneg _) (zpow_nonneg x.im_pos.le _)

omit [Γ.FiniteIndex] in
theorem petersson_self_eq_dens (f : CuspForm Γᴳᴸ k) (x : ℍ) :
    UpperHalfPlane.petersson k ⇑f ⇑f x = ((dens f x : ℝ) : ℂ) := by
  unfold UpperHalfPlane.petersson dens
  rw [Complex.conj_mul' (f x)]
  push_cast
  ring

omit [Γ.FiniteIndex] in
theorem continuous_dens (f : CuspForm Γᴳᴸ k) : Continuous (dens f) := by
  unfold dens
  refine ((continuous_norm.comp (CuspFormClass.holo f).continuous).pow 2).mul ?_
  exact (UpperHalfPlane.continuous_im.zpow₀ k fun x => Or.inl (x.im_pos.ne'))

def rdens (f : CuspForm Γᴳᴸ k) (x : ℍ) : ℝ := ∑ q : SL(2, ℤ) ⧸ Γ, dens f ((q.out⁻¹ : SL(2, ℤ)) • x)

theorem rdens_nonneg (f : CuspForm Γᴳᴸ k) (x : ℍ) : 0 ≤ rdens f x :=
  Finset.sum_nonneg fun _ _ => dens_nonneg f _

theorem continuous_rdens (f : CuspForm Γᴳᴸ k) : Continuous (rdens f) :=
  continuous_finsetSum _ fun _ _ => (continuous_dens f).comp (continuous_const_smul _)

theorem integrand_self_eq (f : CuspForm Γᴳᴸ k) :
    CuspForm.peterssonOnIntegrand Γ k ⇑f ⇑f = fun x => ((rdens f x : ℝ) : ℂ) := by
  rw [integrand_eq]
  funext x
  simp only [cosum, rdens, petersson_self_eq_dens, Complex.ofReal_sum]

theorem integrable_rdens (f : CuspForm Γᴳᴸ k) : Integrable (rdens f) (volume.restrict (𝒟 : Set ℍ)) := by
  obtain ⟨C, hC⟩ := petersson_bounded f f
  refine Measure.integrableOn_of_bounded (M := ∑ _q : SL(2, ℤ) ⧸ Γ, C)
    FLT.FundamentalDomainVolume.volume_fd_lt_top.ne (continuous_rdens f).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun x => ?_
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
  have := hC ((q.out⁻¹ : SL(2, ℤ)) • x)
  rwa [petersson_self_eq_dens, Complex.norm_real] at this

theorem peterssonOn_self_eq (f : CuspForm Γᴳᴸ k) :
    CuspForm.peterssonOn Γ k f f = ((∫ x in (𝒟 : Set ℍ), rdens f x : ℝ) : ℂ) := by
  rw [CuspForm.peterssonOn_def, integrand_self_eq, integral_complex_ofReal]

theorem peterssonOn_self_re_nonneg (f : CuspForm Γᴳᴸ k) : 0 ≤ (CuspForm.peterssonOn Γ k f f).re := by
  rw [peterssonOn_self_eq, Complex.ofReal_re]
  exact setIntegral_nonneg ModularGroup.isClosed_fd.measurableSet fun x _ => rdens_nonneg f x

theorem peterssonOn_self_im (f : CuspForm Γᴳᴸ k) : (CuspForm.peterssonOn Γ k f f).im = 0 := by
  rw [peterssonOn_self_eq, Complex.ofReal_im]

def w₀ : ℍ := ⟨2 * Complex.I, by simp⟩

theorem w₀_mem_fdo : w₀ ∈ 𝒟ᵒ := by
  refine ⟨?_, ?_⟩
  · show 1 < Complex.normSq (2 * Complex.I)
    simp [Complex.normSq_apply]; norm_num
  · show |(2 * Complex.I).re| < 1 / 2
    simp

theorem rdens_eq_zero_of_integral_eq_zero (f : CuspForm Γᴳᴸ k)
    (h : ∫ x in (𝒟 : Set ℍ), rdens f x = 0) {x : ℍ} (hx : x ∈ 𝒟ᵒ) : rdens f x = 0 := by

  have hae : ∀ᵐ y ∂(volume.restrict (𝒟 : Set ℍ)), rdens f y = 0 := by
    have := (integral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall (rdens_nonneg f))
      (integrable_rdens f)).mp h
    filter_upwards [this] with y hy using hy
  by_contra hne
  have hpos : 0 < rdens f x := lt_of_le_of_ne (rdens_nonneg f x) (Ne.symm hne)

  set U : Set ℍ := 𝒟ᵒ ∩ {y | rdens f x / 2 < rdens f y} with hU
  have hUopen : IsOpen U :=
    ModularGroup.isOpen_fdo.inter (isOpen_lt continuous_const (continuous_rdens f))
  have hxU : x ∈ U := ⟨hx, by show rdens f x / 2 < rdens f x; linarith⟩
  have hUpos : 0 < volume U := FLT.HyperbolicMeasure.volume_pos_of_isOpen hUopen ⟨x, hxU⟩
  have hUfd : U ⊆ 𝒟 := fun y hy => ModularGroup.fdo_subset_fd hy.1

  have hzero : volume.restrict (𝒟 : Set ℍ) U = 0 := by
    refine measure_eq_zero_iff_ae_notMem.mpr ?_
    filter_upwards [hae] with y hy hyU
    have : rdens f x / 2 < rdens f y := hyU.2
    rw [hy] at this
    linarith
  rw [Measure.restrict_apply hUopen.measurableSet, Set.inter_eq_self_of_subset_left hUfd] at hzero
  exact hUpos.ne' hzero

theorem eq_zero_of_peterssonOn_self_eq_zero (f : CuspForm Γᴳᴸ k) (h : CuspForm.peterssonOn Γ k f f = 0) :
    f = 0 := by
  have hint : ∫ x in (𝒟 : Set ℍ), rdens f x = 0 := by
    have := congrArg Complex.re h
    rwa [peterssonOn_self_eq, Complex.ofReal_re, Complex.zero_re] at this

  set q₀ : SL(2, ℤ) ⧸ Γ := QuotientGroup.mk 1 with hq₀
  set σ : SL(2, ℤ) := q₀.out⁻¹ with hσ
  have hvan : ∀ x ∈ 𝒟ᵒ, f (σ • x) = 0 := by
    intro x hx
    have h0 := rdens_eq_zero_of_integral_eq_zero f hint hx
    have hterm : dens f (σ • x) = 0 := by
      have hle : dens f (σ • x) ≤ rdens f x := by
        rw [rdens]
        exact Finset.single_le_sum (f := fun q : SL(2, ℤ) ⧸ Γ => dens f ((q.out⁻¹ : SL(2, ℤ)) • x))
          (fun q _ => dens_nonneg f _) (Finset.mem_univ q₀)
      exact le_antisymm (h0 ▸ hle) (dens_nonneg f _)
    have : ‖f (σ • x)‖ ^ 2 = 0 := by
      rcases mul_eq_zero.mp hterm with h1 | h1
      · exact h1
      · exact absurd h1 (zpow_ne_zero _ (σ • x).im_pos.ne')
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)

  set V : Set ℍ := (fun x : ℍ => σ • x) '' 𝒟ᵒ with hV
  have hVopen : IsOpen V := (Homeomorph.smul σ (α := ℍ)).isOpenMap _ ModularGroup.isOpen_fdo
  have hVne : (σ • w₀) ∈ V := ⟨w₀, w₀_mem_fdo, rfl⟩
  have hfV : ∀ y ∈ V, f y = 0 := by
    rintro _ ⟨x, hx, rfl⟩; exact hvan x hx

  set F : ℂ → ℂ := ⇑f ∘ ofComplex with hF
  have hFdiff : DifferentiableOn ℂ F {z : ℂ | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp (CuspFormClass.holo f)
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hFan : AnalyticOnNhd ℂ F {z : ℂ | 0 < z.im} := hFdiff.analyticOnNhd hopen
  have hconn : IsPreconnected {z : ℂ | 0 < z.im} :=
    (convex_halfSpace_im_gt 0).isPreconnected
  set z₀ : ℂ := ((σ • w₀ : ℍ) : ℂ) with hz₀
  have hz₀mem : z₀ ∈ {z : ℂ | 0 < z.im} := (σ • w₀).im_pos
  have hev : F =ᶠ[nhds z₀] 0 := by

    have hWopen : IsOpen (((↑) : ℍ → ℂ) '' V) := UpperHalfPlane.isOpenEmbedding_coe.isOpenMap _ hVopen
    have hz₀W : z₀ ∈ ((↑) : ℍ → ℂ) '' V := ⟨σ • w₀, hVne, rfl⟩
    filter_upwards [hWopen.mem_nhds hz₀W] with z hz
    obtain ⟨y, hy, rfl⟩ := hz
    simp only [hF, Function.comp_apply, ofComplex_apply, Pi.zero_apply]
    exact hfV y hy
  have hzero := hFan.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hz₀mem hev
  apply DFunLike.ext f 0
  intro y
  have := hzero y.im_pos
  simp only [hF, Function.comp_apply, ofComplex_apply, Pi.zero_apply] at this
  simpa using this

theorem peterssonOn_self_eq_zero_iff (f : CuspForm Γᴳᴸ k) : CuspForm.peterssonOn Γ k f f = 0 ↔ f = 0 := by
  constructor
  · exact eq_zero_of_peterssonOn_self_eq_zero f
  · rintro rfl
    rw [peterssonOn_self_eq]
    have : rdens (0 : CuspForm Γᴳᴸ k) = fun _ => 0 := by
      funext x; simp [rdens, dens]
    rw [this]
    simp

end PetOnIP2
p2m_reactivate "P2MW.S_CuspForm_peterssonOn_self_re_nonneg_im_eq_zero_eq_zero_iff.PetOnIP2"

end
p2m_reactivate "P2MW.S_CuspForm_peterssonOn_self_re_nonneg_im_eq_zero_eq_zero_iff.PetOnIP2"

open scoped MatrixGroups in
theorem solution (Γ : Subgroup SL(2, ℤ))
    [Γ.FiniteIndex] (k : ℤ) (f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) :
    0 ≤ (CuspForm.peterssonOn Γ k f f).re ∧ (CuspForm.peterssonOn Γ k f f).im = 0 ∧
    (CuspForm.peterssonOn Γ k f f = 0 ↔ f = 0) :=
  ⟨PetOnIP2.peterssonOn_self_re_nonneg f, PetOnIP2.peterssonOn_self_im f,
    PetOnIP2.peterssonOn_self_eq_zero_iff f⟩

end S_CuspForm_peterssonOn_self_re_nonneg_im_eq_zero_eq_zero_iff
end P2MW
export P2MW.S_CuspForm_peterssonOn_self_re_nonneg_im_eq_zero_eq_zero_iff (solution)
