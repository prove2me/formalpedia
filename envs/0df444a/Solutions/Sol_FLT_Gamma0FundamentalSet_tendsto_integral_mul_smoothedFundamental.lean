-- Prove2me | solution 1 for FLT.Gamma0FundamentalSet.tendsto_integral_mul_smoothedFundamental
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/45dd091f-4f0f-5833-95d1-0bae980247a5

import Mathlib
import Definitions.Def_AutomorphicForm_Gamma0FundamentalSet
import Definitions.Def_AutomorphicForm_ModularFundamentalDomain
import Definitions.Def_ModularCurve_SmoothedFundamental
import Theorems.Thm_ModularCurve_contDiff_and_finsum_smoothedFundamental_eq_one
import Theorems.Thm_FLT_Gamma0FundamentalSet_integral_gammaFundamentalSet_eq_finsum_integral_fd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FLT_Gamma0FundamentalSet_tendsto_integral_mul_smoothedFundamental

noncomputable section

p2m_open "UpperHalfPlane~I"
open Filter Complex Set MeasureTheory MulAction ModularCurve.SmoothedFundamental
open scoped MatrixGroups Topology Modular Pointwise NNReal ENNReal

namespace FLT
p2m_export "FLT" "Gamma0FundamentalSet.gammaFundamentalSet HyperbolicMeasure.volume_smul_sl2z ModularFundamentalDomain.ne_neg_self ModularFundamentalDomain.goodSet ModularFundamentalDomain.volume_compl_goodSet ModularFundamentalDomain.setOf_smul_mem_fd_eq_pair Gamma0FundamentalSet.integral_gammaFundamentalSet_eq_finsum_integral_fd"
namespace SmoothedUnfolding
p2m_open "FLT"

local notation "𝕌" => UpperHalfPlane.upperHalfPlaneSet

variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]

abbrev hT (T : ℝ) : ℂ → ℝ := ModularCurve.smoothedFundamental Γ T

def HT (T : ℝ) (τ : ℍ) : ℝ := ∑ᶠ γ : Γ, hT Γ T (((γ : SL(2, ℤ)) • τ : ℍ) : ℂ)

theorem hT_continuous (T : ℝ) : Continuous (hT Γ T) :=
  ((ModularCurve.contDiff_and_finsum_smoothedFundamental_eq_one Γ T).1 0).continuous

theorem hT_nonneg (T : ℝ) (z : ℂ) : 0 ≤ hT Γ T z :=
  (ModularCurve.contDiff_and_finsum_smoothedFundamental_eq_one Γ T).2.2.2.1 z

theorem hT_hasCompactSupport (T : ℝ) : HasCompactSupport (hT Γ T) :=
  (ModularCurve.contDiff_and_finsum_smoothedFundamental_eq_one Γ T).2.1

theorem tsupport_hT (T : ℝ) : tsupport (hT Γ T) ⊆ 𝕌 :=
  (ModularCurve.contDiff_and_finsum_smoothedFundamental_eq_one Γ T).2.2.1

theorem hT_eq_zero_of_im_nonpos {T : ℝ} {z : ℂ} (hz : ¬ 0 < z.im) : hT Γ T z = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => hz (tsupport_hT Γ T h)

theorem finite_support (T : ℝ) (τ : ℍ) :
    (Function.support fun γ : Γ => hT Γ T (((γ : SL(2, ℤ)) • τ : ℍ) : ℂ)).Finite :=
  (ModularCurve.contDiff_and_finsum_smoothedFundamental_eq_one Γ T).2.2.2.2.1 τ

theorem HT_le_one (T : ℝ) (τ : ℍ) : HT Γ T τ ≤ 1 :=
  (ModularCurve.contDiff_and_finsum_smoothedFundamental_eq_one Γ T).2.2.2.2.2.1 τ

theorem HT_nonneg (T : ℝ) (τ : ℍ) : 0 ≤ HT Γ T τ :=
  finsum_nonneg fun _ => hT_nonneg Γ T _

theorem HT_eq_one {T : ℝ} {τ : ℍ} (h : max τ.im τ.im⁻¹ ≤ T) : HT Γ T τ = 1 :=
  (ModularCurve.contDiff_and_finsum_smoothedFundamental_eq_one Γ T).2.2.2.2.2.2.1 τ h

theorem tendsto_HT (τ : ℍ) : Tendsto (fun T : ℝ => HT Γ T τ) atTop (𝓝 1) :=
  tendsto_const_nhds.congr' (by
    filter_upwards [eventually_ge_atTop (max τ.im τ.im⁻¹)] with T hT'
    exact (HT_eq_one Γ hT').symm)

theorem hT_le_one (T : ℝ) (τ : ℍ) : hT Γ T τ ≤ 1 := by
  refine le_trans ?_ (HT_le_one Γ T τ)
  have := single_le_finsum (1 : Γ) (finite_support Γ T τ) fun γ => hT_nonneg Γ T _
  simpa [HT] using this

theorem measurable_HT (T : ℝ) : Measurable (HT Γ T) := by
  have hterm : ∀ γ : Γ, Measurable fun τ : ℍ =>
      ENNReal.ofReal (hT Γ T (((γ : SL(2, ℤ)) • τ : ℍ) : ℂ)) := fun γ =>
    ENNReal.measurable_ofReal.comp
      ((hT_continuous Γ T).measurable.comp (continuous_coe.measurable.comp
        (continuous_const_smul (γ : SL(2, ℤ))).measurable))
  have hsum : Measurable fun τ : ℍ =>
      ∑' γ : Γ, ENNReal.ofReal (hT Γ T (((γ : SL(2, ℤ)) • τ : ℍ) : ℂ)) :=
    Measurable.ennreal_tsum hterm
  have heq : HT Γ T = fun τ =>
      (∑' γ : Γ, ENNReal.ofReal (hT Γ T (((γ : SL(2, ℤ)) • τ : ℍ) : ℂ))).toReal := by
    funext τ
    have hfin := finite_support Γ T τ
    have hfin' : (Function.support fun γ : Γ =>
        ENNReal.ofReal (hT Γ T (((γ : SL(2, ℤ)) • τ : ℍ) : ℂ))).Finite :=
      hfin.subset fun γ hγ h0 => hγ (by
        have h0' : hT Γ T (((γ : SL(2, ℤ)) • τ : ℍ) : ℂ) = 0 := h0
        simp only [h0', ENNReal.ofReal_zero])
    rw [HT, finsum_eq_sum _ hfin, tsum_eq_sum (s := hfin'.toFinset)
        (fun γ hγ => by simpa using hγ), ENNReal.toReal_sum (fun _ _ => ENNReal.ofReal_ne_top)]
    have hsub : hfin.toFinset = hfin'.toFinset := by
      ext γ
      simp only [Set.Finite.mem_toFinset, Function.mem_support, ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact ⟨fun h => lt_of_le_of_ne (hT_nonneg Γ T _) (Ne.symm h), fun h => h.ne'⟩
    rw [hsub]
    exact Finset.sum_congr rfl fun γ _ => (ENNReal.toReal_ofReal (hT_nonneg Γ T _)).symm
  rw [heq]
  exact hsum.ennreal_toReal

theorem integral_plane_eq_integral_uhp (P : ℍ → ℂ) (T : ℝ) :
    ∫ z : ℂ, P (ofComplex z) * (((z.im ^ 2)⁻¹ * hT Γ T z : ℝ) : ℂ) =
      ∫ τ : ℍ, P τ * (hT Γ T τ : ℂ) := by
  have mp : MeasurePreserving UpperHalfPlane.coe (volume.comap UpperHalfPlane.coe)
      (volume.restrict (Set.range UpperHalfPlane.coe)) :=
    ⟨measurable_coe, by rw [measurableEmbedding_coe.map_comap]⟩
  have hmeas : Measurable fun z : ℍ => (1 / NNReal.mk z.im z.im_pos.le : ℝ≥0) ^ 2 := by
    refine Measurable.pow_const (Measurable.const_div ?_ 1) 2
    exact UpperHalfPlane.continuous_im.measurable.subtype_mk
  symm
  calc ∫ τ : ℍ, P τ * (hT Γ T τ : ℂ)
      = ∫ τ : ℍ, (1 / NNReal.mk τ.im τ.im_pos.le : ℝ≥0) ^ 2 • (P τ * (hT Γ T τ : ℂ))
          ∂(volume.comap UpperHalfPlane.coe) := by
        rw [UpperHalfPlane.volume_def]
        exact integral_withDensity_eq_integral_smul hmeas _
    _ = ∫ τ : ℍ, (fun z : ℂ => P (ofComplex z) * (((z.im ^ 2)⁻¹ * hT Γ T z : ℝ) : ℂ)) (τ : ℂ)
          ∂(volume.comap UpperHalfPlane.coe) := by
        refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
        have h0 : (τ.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr τ.im_pos.ne'
        simp only [ofComplex_apply, NNReal.smul_def, Complex.real_smul, UpperHalfPlane.coe_im]
        push_cast
        field_simp
    _ = ∫ z in Set.range UpperHalfPlane.coe,
          P (ofComplex z) * (((z.im ^ 2)⁻¹ * hT Γ T z : ℝ) : ℂ) :=
        mp.integral_comp measurableEmbedding_coe
          (fun z : ℂ => P (ofComplex z) * (((z.im ^ 2)⁻¹ * hT Γ T z : ℝ) : ℂ))
    _ = ∫ z : ℂ, P (ofComplex z) * (((z.im ^ 2)⁻¹ * hT Γ T z : ℝ) : ℂ) := by
        refine setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => ?_
        rw [UpperHalfPlane.range_coe] at hz
        rw [hT_eq_zero_of_im_nonpos Γ hz]
        simp

theorem tendsto_integral_HT (P : ℍ → ℂ) (hPm : AEStronglyMeasurable P volume)
    (hPi : IntegrableOn P (FLT.Gamma0FundamentalSet.gammaFundamentalSet Γ) volume) :
    Tendsto (fun T : ℝ => ∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet Γ,
        P τ * (HT Γ T τ : ℂ)) atTop
      (𝓝 (∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet Γ, P τ)) := by
  refine tendsto_integral_filter_of_dominated_convergence (fun τ => ‖P τ‖) ?_ ?_ hPi.norm ?_
  · refine Eventually.of_forall fun T => ?_
    exact hPm.restrict.mul (Complex.continuous_ofReal.measurable.comp
      (measurable_HT Γ T)).aestronglyMeasurable
  · refine Eventually.of_forall fun T => Eventually.of_forall fun τ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (HT_nonneg Γ T τ)]
    exact mul_le_of_le_one_right (norm_nonneg _) (HT_le_one Γ T τ)
  · refine Eventually.of_forall fun τ => ?_
    have := ((Complex.continuous_ofReal.tendsto 1).comp (tendsto_HT Γ τ)).const_mul (P τ)
    simpa using this

section Unfold

variable (T : ℝ)

scoped instance instFintypeQuot : Fintype (SL(2, ℤ) ⧸ Γ) := Fintype.ofFinite _

theorem finite_moving (K L : Set ℍ) (hK : IsCompact K) (hL : IsCompact L) :
    {γ : SL(2, ℤ) | ((fun τ : ℍ => γ • τ) '' K ∩ L).Nonempty}.Finite := by
  have h := ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := 𝒮ℒ) (T := ℍ) hK hL
  set φ : SL(2, ℤ) →* GL (Fin 2) ℝ := Matrix.SpecialLinearGroup.mapGL ℝ with hφ
  have hinj : Function.Injective φ := by
    intro a b hab
    ext i j
    have := congrArg (fun g : GL (Fin 2) ℝ => (g : Matrix (Fin 2) (Fin 2) ℝ) i j) hab
    simpa [hφ] using this
  refine Finite.of_finite_image ?_ hinj.injOn
  refine (h.image Subtype.val).subset ?_
  rintro _ ⟨g, hg, rfl⟩
  exact ⟨⟨φ g, ⟨g, rfl⟩⟩, hg, rfl⟩

theorem im_smul_le_max (γ : SL(2, ℤ)) (τ : ℍ) : (γ • τ).im ≤ max τ.im τ.im⁻¹ := by
  by_cases hc : (γ 1 0 : ℤ) = 0
  · have hd : (γ 0 0 : ℤ) * γ 1 1 = 1 := by
      have h := γ.det_coe
      rw [Matrix.det_fin_two, hc, mul_zero, sub_zero] at h; exact h
    have hdd : (γ 1 1 : ℤ) * γ 1 1 = 1 := by
      rcases Int.eq_one_or_neg_one_of_mul_eq_one' hd with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] <;> norm_num
    have : (γ • τ).im = τ.im := by
      rw [ModularGroup.im_smul_eq_div_normSq]
      have hden : denom γ τ = ((γ 1 1 : ℤ) : ℂ) := by simp [denom, hc]
      rw [hden]
      have : Complex.normSq (((γ 1 1 : ℤ) : ℂ)) = 1 := by
        rw [← Complex.ofReal_intCast, Complex.normSq_ofReal]; exact_mod_cast hdd
      rw [this, div_one]
    rw [this]; exact le_max_left _ _
  · refine le_trans ?_ (le_max_right _ _)
    rw [ModularGroup.im_smul_eq_div_normSq]
    have h1 := UpperHalfPlane.c_mul_im_sq_le_normSq_denom (g := (γ : GL (Fin 2) ℝ)) (z := τ)
    have hc' : (1 : ℝ) ≤ ((γ 1 0 : ℤ) : ℝ) ^ 2 := by
      have : (1 : ℤ) ≤ (γ 1 0) ^ 2 := by
        have := Int.one_le_abs hc
        nlinarith [sq_abs (γ 1 0)]
      exact_mod_cast this
    have hτ := τ.im_pos
    have hent : ((γ : GL (Fin 2) ℝ) 1 0 : ℝ) = ((γ 1 0 : ℤ) : ℝ) := by simp
    rw [hent] at h1
    have hns : τ.im ^ 2 ≤ Complex.normSq (denom γ τ) := by
      calc τ.im ^ 2 = 1 * τ.im ^ 2 := by ring
        _ ≤ ((γ 1 0 : ℤ) : ℝ) ^ 2 * τ.im ^ 2 := by gcongr
        _ = (((γ 1 0 : ℤ) : ℝ) * τ.im) ^ 2 := by ring
        _ ≤ _ := h1
    have hpos : 0 < Complex.normSq (denom γ τ) := lt_of_lt_of_le (by positivity) hns
    rw [div_le_iff₀ hpos]
    calc τ.im = τ.im⁻¹ * τ.im ^ 2 := by field_simp
      _ ≤ τ.im⁻¹ * Complex.normSq (denom γ τ) := by gcongr

def KH : Set ℍ := ((↑) : ℍ → ℂ) ⁻¹' tsupport (hT Γ T)

theorem isCompact_KH : IsCompact (KH Γ T) := by
  refine isEmbedding_coe.isCompact_iff.2 ?_
  rw [KH, image_preimage_eq_of_subset]
  · exact hT_hasCompactSupport Γ T
  · intro z hz; exact ⟨⟨z, tsupport_hT Γ T hz⟩, rfl⟩

theorem mem_KH_of_ne_zero {τ : ℍ} (h : hT Γ T τ ≠ 0) : τ ∈ KH Γ T := subset_tsupport _ h

theorem exists_height_bound : ∃ C : ℝ, ∀ τ ∈ KH Γ T, max τ.im τ.im⁻¹ ≤ C := by
  have hc : ContinuousOn (fun τ : ℍ => max τ.im τ.im⁻¹) (KH Γ T) :=
    (UpperHalfPlane.continuous_im.max (UpperHalfPlane.continuous_im.inv₀
      fun τ => τ.im_pos.ne')).continuousOn
  obtain ⟨C, hC⟩ := (isCompact_KH Γ T).bddAbove_image hc
  exact ⟨C, fun τ hτ => hC ⟨τ, hτ, rfl⟩⟩

def Dfin : Finset SL(2, ℤ) :=
  (finite_moving (KH Γ T) (ModularGroup.truncatedFundamentalDomain (exists_height_bound Γ T).choose)
    (isCompact_KH Γ T) (ModularGroup.isCompact_truncatedFundamentalDomain _)).toFinset

theorem mem_Dfin {δ : SL(2, ℤ)} {τ : ℍ} (hτ : τ ∈ KH Γ T) (hδ : δ • τ ∈ 𝒟) : δ ∈ Dfin Γ T := by
  simp only [Dfin, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  refine ⟨δ • τ, ⟨τ, hτ, rfl⟩, hδ, ?_⟩
  exact (im_smul_le_max δ τ).trans ((exists_height_bound Γ T).choose_spec τ hτ)

theorem two_mul_eq_sum (P : ℍ → ℂ) {τ : ℍ} (hgood : τ ∈ FLT.ModularFundamentalDomain.goodSet) :
    (2 : ℂ) * (P τ * (hT Γ T τ : ℂ)) =
      ∑ δ ∈ Dfin Γ T, ((δ⁻¹ • (𝒟 : Set ℍ)).indicator (fun τ => P τ * (hT Γ T τ : ℂ)) τ) := by
  classical
  by_cases h0 : hT Γ T τ = 0
  · symm
    refine (Finset.sum_eq_zero fun δ _ => ?_).trans (by simp [h0])
    rw [Set.indicator_apply_eq_zero]
    intro _; simp [h0]
  have hτ : τ ∈ KH Γ T := mem_KH_of_ne_zero Γ T h0
  obtain ⟨δ₀, hpair⟩ := FLT.ModularFundamentalDomain.setOf_smul_mem_fd_eq_pair hgood
  have hmem : ∀ δ : SL(2, ℤ), δ • τ ∈ 𝒟 ↔ δ = δ₀ ∨ δ = -δ₀ := by
    intro δ
    have := Set.ext_iff.1 hpair δ
    simpa using this
  have hind : ∀ δ : SL(2, ℤ), (δ⁻¹ • (𝒟 : Set ℍ)).indicator (fun τ => P τ * (hT Γ T τ : ℂ)) τ =
      if δ • τ ∈ 𝒟 then P τ * (hT Γ T τ : ℂ) else 0 := by
    intro δ
    rw [Set.indicator_apply]
    simp only [Set.mem_inv_smul_set_iff]
  simp_rw [hind]
  rw [← Finset.sum_filter]
  have hfilter : (Dfin Γ T).filter (fun δ => δ • τ ∈ 𝒟) = {δ₀, -δ₀} := by
    ext δ
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · exact fun h => (hmem δ).1 h.2
    · intro h
      have hδ : δ • τ ∈ 𝒟 := (hmem δ).2 h
      exact ⟨mem_Dfin Γ T hτ hδ, hδ⟩
  rw [hfilter, Finset.sum_pair (FLT.ModularFundamentalDomain.ne_neg_self δ₀)]
  ring

theorem measurableSet_smul_fd (γ : SL(2, ℤ)) : MeasurableSet (γ • (𝒟 : Set ℍ)) :=
  (ModularGroup.isClosed_fd.smul γ).measurableSet

theorem measurePreserving_smul (γ : SL(2, ℤ)) :
    MeasurePreserving (fun w : ℍ => γ • w) volume volume := by
  have hemb : MeasurableEmbedding (fun w : ℍ => γ • w) :=
    (Homeomorph.smul γ (α := ℍ)).measurableEmbedding
  exact ⟨hemb.measurable, by
    ext s hs
    rw [Measure.map_apply hemb.measurable hs, Set.preimage_smul,
      FLT.HyperbolicMeasure.volume_smul_sl2z]⟩

theorem setIntegral_smul_fd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (γ : SL(2, ℤ)) (f : ℍ → E) :
    ∫ u in γ • (𝒟 : Set ℍ), f u = ∫ w in (𝒟 : Set ℍ), f (γ • w) := by
  rw [← Set.image_smul]
  exact (measurePreserving_smul γ).setIntegral_image_emb
    (Homeomorph.smul γ (α := ℍ)).measurableEmbedding f _

variable {Γ}
variable (hΓ : (-1 : SL(2, ℤ)) ∈ Γ) (P : ℍ → ℂ) (hP : ∀ γ ∈ Γ, ∀ τ : ℍ, P (γ • τ) = P τ)
  (hPm : AEStronglyMeasurable P volume)
  (hPi : IntegrableOn P (FLT.Gamma0FundamentalSet.gammaFundamentalSet Γ) volume)

include hP hPi in

theorem integrableOn_translate (γ : SL(2, ℤ)) (hγ : γ ∈ Γ) (q : SL(2, ℤ) ⧸ Γ) :
    IntegrableOn P (γ • ((Quotient.out q)⁻¹ • (𝒟 : Set ℍ))) volume := by
  have h1 : IntegrableOn P ((Quotient.out q)⁻¹ • (𝒟 : Set ℍ)) volume :=
    hPi.mono_set (Set.subset_iUnion (fun q : SL(2, ℤ) ⧸ Γ => (Quotient.out q)⁻¹ • (𝒟 : Set ℍ)) q)
  have hemb : MeasurableEmbedding (fun w : ℍ => γ • w) :=
    (Homeomorph.smul γ (α := ℍ)).measurableEmbedding
  have key := (measurePreserving_smul γ).integrableOn_comp_preimage hemb (f := P)
    (s := γ • ((Quotient.out q)⁻¹ • (𝒟 : Set ℍ)))
  rw [Set.preimage_smul, inv_smul_smul] at key
  have hfun : (P ∘ fun w : ℍ => γ • w) = P := funext fun w => hP γ hγ w
  rw [hfun] at key
  exact key.1 h1

theorem inv_eq_mul_out_inv (δ : SL(2, ℤ)) :
    ∃ γ ∈ Γ, δ⁻¹ = γ * (Quotient.out (QuotientGroup.mk δ : SL(2, ℤ) ⧸ Γ))⁻¹ := by
  refine ⟨δ⁻¹ * Quotient.out (QuotientGroup.mk δ : SL(2, ℤ) ⧸ Γ), ?_, by group⟩
  have h : (QuotientGroup.mk (Quotient.out (QuotientGroup.mk δ : SL(2, ℤ) ⧸ Γ)) : SL(2, ℤ) ⧸ Γ) =
      QuotientGroup.mk δ := QuotientGroup.out_eq' _
  exact QuotientGroup.eq.1 h.symm

include hP hPi in
theorem integrableOn_P_tile (δ : SL(2, ℤ)) : IntegrableOn P (δ⁻¹ • (𝒟 : Set ℍ)) volume := by
  obtain ⟨γ, hγ, hδ⟩ := inv_eq_mul_out_inv (Γ := Γ) δ
  rw [hδ, mul_smul]
  exact integrableOn_translate P hP hPi γ hγ _

include hP hPi in
theorem integrableOn_PhT_tile (δ : SL(2, ℤ)) :
    IntegrableOn (fun τ => P τ * (hT Γ T τ : ℂ)) (δ⁻¹ • (𝒟 : Set ℍ)) volume := by
  refine (integrableOn_P_tile P hP hPi δ).mul_bdd (c := 1) ?_ ?_
  · exact (Complex.continuous_ofReal.comp ((hT_continuous Γ T).comp continuous_coe)).aestronglyMeasurable
  · refine Eventually.of_forall fun τ => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hT_nonneg Γ T _)]
    exact hT_le_one Γ T τ

theorem measurableSet_fd' : MeasurableSet (𝒟 : Set ℍ) := ModularGroup.isClosed_fd.measurableSet

open scoped Classical in

theorem fiber_sum (q : SL(2, ℤ) ⧸ Γ) {w : ℍ} (hw : w ∈ 𝒟) :
    ∑ δ ∈ (Dfin Γ T).filter (fun δ => (QuotientGroup.mk δ : SL(2, ℤ) ⧸ Γ) = q),
        hT Γ T ((δ⁻¹ • w : ℍ) : ℂ) =
      HT Γ T ((Quotient.out q)⁻¹ • w) := by
  classical
  set σ : SL(2, ℤ) := Quotient.out q with hσ
  have hfin := finite_support Γ T (σ⁻¹ • w)
  rw [HT, finsum_eq_sum _ hfin, ← Finset.sum_filter_ne_zero]
  refine Finset.sum_bij' (fun δ hδ => (⟨δ⁻¹ * σ, ?_⟩ : Γ)) (fun γ _ => σ * ((γ : SL(2, ℤ)))⁻¹)
    ?_ ?_ ?_ ?_ ?_
  ·
    have hq' : (QuotientGroup.mk δ : SL(2, ℤ) ⧸ Γ) = q :=
      (Finset.mem_filter.1 (Finset.mem_filter.1 hδ).1).2
    have hq : (QuotientGroup.mk δ : SL(2, ℤ) ⧸ Γ) = QuotientGroup.mk σ := by
      rw [hq', hσ, QuotientGroup.out_eq']
    exact QuotientGroup.eq.1 hq
  · intro δ hδ
    have hne := (Finset.mem_filter.1 hδ).2
    simp only [Set.Finite.mem_toFinset, Function.mem_support]
    rw [smul_smul, mul_inv_cancel_right]
    exact hne
  · intro γ hγ
    simp only [Set.Finite.mem_toFinset, Function.mem_support] at hγ
    refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨?_, ?_⟩, ?_⟩
    · refine mem_Dfin Γ T (mem_KH_of_ne_zero Γ T hγ) ?_
      rw [smul_smul, smul_smul]
      simpa using hw
    · rw [QuotientGroup.mk_mul_of_mem _ (Γ.inv_mem γ.2), hσ, QuotientGroup.out_eq']
    · rw [mul_inv_rev, inv_inv, mul_smul]
      exact hγ
  · intro δ hδ
    simp only [mul_inv_rev, inv_inv]
    group
  · intro γ hγ
    ext
    simp only [mul_inv_rev, inv_inv]
    group
  · intro δ hδ
    rw [smul_smul, mul_inv_cancel_right]

include hΓ hP hPm hPi in

theorem two_mul_integral_eq :
    2 * ∫ τ : ℍ, P τ * (hT Γ T τ : ℂ) =
      ∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet Γ, P τ * (HT Γ T τ : ℂ) := by
  classical

  have hint : ∀ δ : SL(2, ℤ), Integrable (fun τ : ℍ =>
      (δ⁻¹ • (𝒟 : Set ℍ)).indicator (fun τ => P τ * (hT Γ T τ : ℂ)) τ) := fun δ =>
    (integrableOn_PhT_tile T P hP hPi δ).integrable_indicator (measurableSet_smul_fd _)
  have hae : ∀ᵐ τ : ℍ, τ ∈ FLT.ModularFundamentalDomain.goodSet :=
    mem_ae_iff.2 FLT.ModularFundamentalDomain.volume_compl_goodSet
  have hA : 2 * ∫ τ : ℍ, P τ * (hT Γ T τ : ℂ) =
      ∑ δ ∈ Dfin Γ T, ∫ τ : ℍ, (δ⁻¹ • (𝒟 : Set ℍ)).indicator (fun τ => P τ * (hT Γ T τ : ℂ)) τ := by
    rw [← integral_const_mul, ← integral_finset_sum _ fun δ _ => hint δ]
    refine integral_congr_ae ?_
    filter_upwards [hae] with τ hτ
    rw [two_mul_eq_sum Γ T P hτ]

  have hB : ∀ δ : SL(2, ℤ),
      ∫ τ : ℍ, (δ⁻¹ • (𝒟 : Set ℍ)).indicator (fun τ => P τ * (hT Γ T τ : ℂ)) τ =
        ∫ w in (𝒟 : Set ℍ), P ((Quotient.out (QuotientGroup.mk δ : SL(2, ℤ) ⧸ Γ))⁻¹ • w) *
          (hT Γ T ((δ⁻¹ • w : ℍ) : ℂ) : ℂ) := by
    intro δ
    rw [integral_indicator (measurableSet_smul_fd _), setIntegral_smul_fd]
    refine setIntegral_congr_fun measurableSet_fd' fun w _ => ?_
    obtain ⟨γ, hγ, hδ⟩ := inv_eq_mul_out_inv (Γ := Γ) δ
    congr 1
    conv_lhs => rw [hδ, mul_smul, hP γ hγ]

  have hC : ∑ δ ∈ Dfin Γ T, ∫ w in (𝒟 : Set ℍ),
        P ((Quotient.out (QuotientGroup.mk δ : SL(2, ℤ) ⧸ Γ))⁻¹ • w) *
          (hT Γ T ((δ⁻¹ • w : ℍ) : ℂ) : ℂ) =
      ∑ q : SL(2, ℤ) ⧸ Γ, ∫ w in (𝒟 : Set ℍ),
        P ((Quotient.out q)⁻¹ • w) * (HT Γ T ((Quotient.out q)⁻¹ • w) : ℂ) := by
    rw [← Finset.sum_fiberwise (Dfin Γ T) (fun δ => (QuotientGroup.mk δ : SL(2, ℤ) ⧸ Γ))]
    refine Finset.sum_congr rfl fun q _ => ?_
    have hintq : ∀ δ ∈ (Dfin Γ T).filter (fun δ => (QuotientGroup.mk δ : SL(2, ℤ) ⧸ Γ) = q),
        Integrable (fun w => P ((Quotient.out (QuotientGroup.mk δ : SL(2, ℤ) ⧸ Γ))⁻¹ • w) *
          (hT Γ T ((δ⁻¹ • w : ℍ) : ℂ) : ℂ)) (volume.restrict (𝒟 : Set ℍ)) := by
      intro δ hδ
      rw [(Finset.mem_filter.1 hδ).2]
      have h1 : IntegrableOn (fun w => P ((Quotient.out q)⁻¹ • w)) (𝒟 : Set ℍ) volume := by
        have hemb : MeasurableEmbedding (fun w : ℍ => (Quotient.out q)⁻¹ • w) :=
          (Homeomorph.smul (Quotient.out q)⁻¹ (α := ℍ)).measurableEmbedding
        have key := (measurePreserving_smul (Quotient.out q)⁻¹).integrableOn_comp_preimage hemb
          (f := P) (s := (Quotient.out q)⁻¹ • (𝒟 : Set ℍ))
        rw [Set.preimage_smul, inv_smul_smul] at key
        exact key.2 (integrableOn_translate P hP hPi 1 Γ.one_mem q |>.congr_set_ae
          (by rw [one_smul]))
      refine h1.mul_bdd (c := 1) ?_ ?_
      · exact (Complex.continuous_ofReal.comp ((hT_continuous Γ T).comp
          (continuous_coe.comp (continuous_const_smul δ⁻¹)))).aestronglyMeasurable
      · refine Eventually.of_forall fun w => ?_
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hT_nonneg Γ T _)]
        exact hT_le_one Γ T _
    rw [← integral_finset_sum _ hintq]
    refine setIntegral_congr_fun measurableSet_fd' fun w hw => ?_
    have hrew : ∀ δ ∈ (Dfin Γ T).filter (fun δ => (QuotientGroup.mk δ : SL(2, ℤ) ⧸ Γ) = q),
        P ((Quotient.out (QuotientGroup.mk δ : SL(2, ℤ) ⧸ Γ))⁻¹ • w) *
          (hT Γ T ((δ⁻¹ • w : ℍ) : ℂ) : ℂ) =
        P ((Quotient.out q)⁻¹ • w) * (hT Γ T ((δ⁻¹ • w : ℍ) : ℂ) : ℂ) := by
      intro δ hδ; rw [(Finset.mem_filter.1 hδ).2]
    rw [Finset.sum_congr rfl hrew, ← Finset.mul_sum, ← fiber_sum T q hw]
    push_cast
    rfl

  have hD : ∑ q : SL(2, ℤ) ⧸ Γ, ∫ w in (𝒟 : Set ℍ),
        P ((Quotient.out q)⁻¹ • w) * (HT Γ T ((Quotient.out q)⁻¹ • w) : ℂ) =
      ∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet Γ, P τ * (HT Γ T τ : ℂ) := by
    have hi : IntegrableOn (fun τ => P τ * (HT Γ T τ : ℂ))
        (FLT.Gamma0FundamentalSet.gammaFundamentalSet Γ) volume := by
      refine hPi.mul_bdd (c := 1) ?_ ?_
      · exact (Complex.continuous_ofReal.measurable.comp (measurable_HT Γ T)).aestronglyMeasurable
      · refine Eventually.of_forall fun τ => ?_
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (HT_nonneg Γ T _)]
        exact HT_le_one Γ T _
    rw [FLT.Gamma0FundamentalSet.integral_gammaFundamentalSet_eq_finsum_integral_fd hΓ _ hi,
      finsum_eq_sum_of_fintype]
  rw [hA, Finset.sum_congr rfl fun δ _ => hB δ, hC, hD]

end Unfold

theorem main {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] (hΓ : (-1 : SL(2, ℤ)) ∈ Γ)
    (P : ℍ → ℂ) (hP : ∀ γ ∈ Γ, ∀ τ : ℍ, P (γ • τ) = P τ)
    (hPm : AEStronglyMeasurable P volume)
    (hPi : IntegrableOn P (FLT.Gamma0FundamentalSet.gammaFundamentalSet Γ) volume) :
    Tendsto (fun T : ℝ => ∫ z : ℂ, P (ofComplex z) *
        ((z.im ^ 2)⁻¹ * ModularCurve.smoothedFundamental Γ T z : ℝ)) atTop
      (𝓝 ((1 / 2 : ℂ) * ∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet Γ, P τ)) := by
  have heq : ∀ T : ℝ, ∫ z : ℂ, P (ofComplex z) *
      ((z.im ^ 2)⁻¹ * ModularCurve.smoothedFundamental Γ T z : ℝ) =
      (1 / 2 : ℂ) * ∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet Γ, P τ * (HT Γ T τ : ℂ) := by
    intro T
    rw [integral_plane_eq_integral_uhp Γ P T, ← two_mul_integral_eq T hΓ P hP hPm hPi]
    ring
  simp_rw [heq]
  exact (tendsto_integral_HT Γ P hPm hPi).const_mul _

end FLT.SmoothedUnfolding
p2m_reactivate "P2MW.S_FLT_Gamma0FundamentalSet_tendsto_integral_mul_smoothedFundamental.FLT P2MW.S_FLT_Gamma0FundamentalSet_tendsto_integral_mul_smoothedFundamental.FLT.SmoothedUnfolding"
p2m_reactivate "P2MW.S_FLT_Gamma0FundamentalSet_tendsto_integral_mul_smoothedFundamental.FLT"

theorem solution
    {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] (hΓ : (-1 : SL(2, ℤ)) ∈ Γ)
    (P : ℍ → ℂ) (hP : ∀ γ ∈ Γ, ∀ τ : ℍ, P (γ • τ) = P τ)
    (hPm : AEStronglyMeasurable P volume)
    (hPi : IntegrableOn P (FLT.Gamma0FundamentalSet.gammaFundamentalSet Γ) volume) :
    Tendsto (fun T : ℝ => ∫ z : ℂ, P (ofComplex z) *
        ((z.im ^ 2)⁻¹ * ModularCurve.smoothedFundamental Γ T z : ℝ)) atTop
      (𝓝 ((1 / 2 : ℂ) * ∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet Γ, P τ)) :=
  FLT.SmoothedUnfolding.main hΓ P hP hPm hPi

end
p2m_reactivate "P2MW.S_FLT_Gamma0FundamentalSet_tendsto_integral_mul_smoothedFundamental.FLT P2MW.S_FLT_Gamma0FundamentalSet_tendsto_integral_mul_smoothedFundamental.FLT.SmoothedUnfolding"

end S_FLT_Gamma0FundamentalSet_tendsto_integral_mul_smoothedFundamental
end P2MW
export P2MW.S_FLT_Gamma0FundamentalSet_tendsto_integral_mul_smoothedFundamental (solution)
