-- Prove2me | solution 1 for FaulhuberTFA.stft_fundamental_identity
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T20:33:03.771038+00:00
-- url     : https://prove2.me/submissions/fc1d09ad-1d63-4acd-b073-3196af3db979

import Mathlib
import Definitions.Def_FaulhuberTFA_Basic

open MeasureTheory Complex
open scoped InnerProductSpace

set_option autoImplicit false

open scoped FourierTransform SchwartzMap

namespace FaulhuberTFA

lemma fi_ePhase_add (a b : ℝ) : ePhase (a + b) = ePhase a * ePhase b := by
  unfold ePhase; rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma fi_conj_ePhase (s : ℝ) : starRingEnd ℂ (ePhase s) = ePhase (-s) := by
  unfold ePhase; rw [← Complex.exp_conj]; congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]; push_cast; ring

lemma fi_norm_ePhase (s : ℝ) : ‖ePhase s‖ = 1 := by
  unfold ePhase
  rw [show (2 * Real.pi * Complex.I * (s : ℂ)) = ((2 * Real.pi * s : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

lemma fi_continuous_ePhase : Continuous ePhase := by
  unfold ePhase; fun_prop

lemma fi_fourierChar_eq (s : ℝ) : ((𝐞 s : Circle) : ℂ) = ePhase s := by
  rw [Real.fourierChar_apply]; unfold ePhase; congr 1; push_cast; ring

variable {d : ℕ}

lemma fi_pair_fourier (U : Lp ℂ 2 (volume : Measure (Rd d))) (φ : 𝓢(Rd d, ℂ)) :
    ∫ t, φ t * (𝓕 U : Lp ℂ 2 (volume : Measure (Rd d))) t = ∫ t, (𝓕 φ) t * U t := by
  have h := congrArg (fun T : 𝓢'(Rd d, ℂ) => T φ) (Lp.fourier_toTemperedDistribution_eq U)
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply, smul_eq_mul] at h
  exact h.symm

lemma fi_pair_fourierInv (U : Lp ℂ 2 (volume : Measure (Rd d))) (φ : 𝓢(Rd d, ℂ)) :
    ∫ t, φ t * (𝓕⁻ U : Lp ℂ 2 (volume : Measure (Rd d))) t = ∫ t, (𝓕⁻ φ) t * U t := by
  have h := congrArg (fun T : 𝓢'(Rd d, ℂ) => T φ) (Lp.fourierInv_toTemperedDistribution_eq U)
  simp only [TemperedDistribution.fourierInv_apply, Lp.toTemperedDistribution_apply,
    smul_eq_mul] at h
  exact h.symm

lemma fi_ext (A B : Lp ℂ 2 (volume : Measure (Rd d)))
    (h : ∀ φ : 𝓢(Rd d, ℂ), ∫ t, φ t * A t = ∫ t, φ t * B t) : A = B := by
  have hk := Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ)
    (μ := (volume : Measure (Rd d))) (p := 2)
  have hT : Lp.toTemperedDistributionCLM ℂ (volume : Measure (Rd d)) 2 A =
      Lp.toTemperedDistributionCLM ℂ (volume : Measure (Rd d)) 2 B := by
    ext φ
    simpa using h φ
  have hmem : A - B ∈ (↑(Lp.toTemperedDistributionCLM ℂ (volume : Measure (Rd d)) 2) :
      Lp ℂ 2 (volume : Measure (Rd d)) →ₗ[ℂ] 𝓢'(Rd d, ℂ)).ker := by
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_sub, hT, sub_self]
  rw [hk] at hmem
  exact sub_eq_zero.mp ((Submodule.mem_bot ℂ).mp hmem)

lemma fi_fourier_transl (f : Rd d → ℂ) (a ξ : Rd d) :
    𝓕 (fun t => f (t - a)) ξ = ePhase (-⟪a, ξ⟫_ℝ) * 𝓕 f ξ := by
  have : (fun t => f (t - a)) = f ∘ fun v => v + (-a) := by
    funext t; simp [sub_eq_add_neg]
  rw [this]
  show VectorFourier.fourierIntegral 𝐞 volume (innerₗ (Rd d)) (f ∘ fun v => v + (-a)) ξ = _
  rw [VectorFourier.fourierIntegral_comp_add_right]
  simp only [Circle.smul_def, smul_eq_mul, innerₗ_apply_apply, inner_neg_left, fi_fourierChar_eq]
  rfl

lemma fi_fourierInv_transl (f : Rd d → ℂ) (a ξ : Rd d) :
    𝓕⁻ (fun t => f (t - a)) ξ = ePhase ⟪a, ξ⟫_ℝ * 𝓕⁻ f ξ := by
  rw [Real.fourierInv_eq_fourier_neg, Real.fourierInv_eq_fourier_neg, fi_fourier_transl]
  simp


lemma fi_memLp_tr (a : Rd d) (U : Lp ℂ 2 (volume : Measure (Rd d))) :
    MemLp (fun t => U (t - a)) 2 volume :=
  (Lp.memLp U).comp_measurePreserving (measurePreserving_sub_right volume a)

lemma fi_memLp_mo (b : Rd d) (U : Lp ℂ 2 (volume : Measure (Rd d))) :
    MemLp (fun t => ePhase ⟪b, t⟫_ℝ * U t) 2 volume := by
  refine (Lp.memLp U).congr_norm ?_ (ae_of_all _ fun t => ?_)
  · exact ((fi_continuous_ePhase.comp (continuous_const.inner continuous_id)).aestronglyMeasurable).mul
      (Lp.aestronglyMeasurable U)
  · simp [fi_norm_ePhase]

/-- translation `T_a` on `L²` -/
noncomputable def fi_tr (a : Rd d) (U : Lp ℂ 2 (volume : Measure (Rd d))) : Lp ℂ 2 (volume : Measure (Rd d)) :=
  (fi_memLp_tr a U).toLp _

/-- modulation `M_b` on `L²` -/
noncomputable def fi_mo (b : Rd d) (U : Lp ℂ 2 (volume : Measure (Rd d))) : Lp ℂ 2 (volume : Measure (Rd d)) :=
  (fi_memLp_mo b U).toLp _

lemma fi_tr_ae (a : Rd d) (U : Lp ℂ 2 (volume : Measure (Rd d))) :
    (fi_tr a U : Rd d → ℂ) =ᵐ[volume] fun t => U (t - a) := (fi_memLp_tr a U).coeFn_toLp

lemma fi_mo_ae (b : Rd d) (U : Lp ℂ 2 (volume : Measure (Rd d))) :
    (fi_mo b U : Rd d → ℂ) =ᵐ[volume] fun t => ePhase ⟪b, t⟫_ℝ * U t := (fi_memLp_mo b U).coeFn_toLp

lemma fi_fourier_mo (b : Rd d) (U : Lp ℂ 2 (volume : Measure (Rd d))) :
    𝓕 (fi_mo b U) = fi_tr b (𝓕 U) := by
  apply fi_ext
  intro φ
  rw [fi_pair_fourier]
  have e1 : ∫ t, (𝓕 φ) t * (fi_mo b U) t = ∫ t, (𝓕 φ) t * (ePhase ⟪b, t⟫_ℝ * U t) :=
    integral_congr_ae ((fi_mo_ae b U).mono fun t ht => by simp only [ht])
  have e2 : ∫ t, φ t * (fi_tr b (𝓕 U)) t = ∫ t, φ t * (𝓕 U : Lp ℂ 2 (volume : Measure (Rd d))) (t - b) :=
    integral_congr_ae ((fi_tr_ae b (𝓕 U)).mono fun t ht => by simp only [ht])
  rw [e1, e2]
  set ψ : 𝓢(Rd d, ℂ) := SchwartzMap.compSubConstCLM ℂ (-b) φ
  have e3 : ∫ t, φ t * (𝓕 U : Lp ℂ 2 (volume : Measure (Rd d))) (t - b)
      = ∫ t, ψ t * (𝓕 U : Lp ℂ 2 (volume : Measure (Rd d))) t := by
    rw [← integral_add_right_eq_self (μ := volume) _ b]
    congr 1; funext t
    simp [ψ]
  rw [e3, fi_pair_fourier]
  congr 1; funext t
  have : (𝓕 ψ) t = ePhase (-⟪-b, t⟫_ℝ) * (𝓕 φ) t := by
    rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe]
    have hψ : (ψ : Rd d → ℂ) = fun s => φ (s - -b) := by funext s; simp [ψ]
    rw [hψ, fi_fourier_transl]
  rw [this]; simp only [inner_neg_left, neg_neg]; ring

lemma fi_fourier_tr (a : Rd d) (U : Lp ℂ 2 (volume : Measure (Rd d))) :
    𝓕 (fi_tr a U) = fi_mo (-a) (𝓕 U) := by
  have key : fi_tr a U = 𝓕⁻ (fi_mo (-a) (𝓕 U)) := by
    apply fi_ext
    intro φ
    rw [fi_pair_fourierInv]
    have e1 : ∫ t, (𝓕⁻ φ) t * (fi_mo (-a) (𝓕 U)) t
        = ∫ t, (𝓕⁻ φ) t * (ePhase ⟪-a, t⟫_ℝ * (𝓕 U : Lp ℂ 2 (volume : Measure (Rd d))) t) :=
      integral_congr_ae ((fi_mo_ae (-a) (𝓕 U)).mono fun t ht => by simp only [ht])
    have e2 : ∫ t, φ t * (fi_tr a U) t = ∫ t, φ t * U (t - a) :=
      integral_congr_ae ((fi_tr_ae a U).mono fun t ht => by simp only [ht])
    rw [e1, e2]
    set ψ : 𝓢(Rd d, ℂ) := SchwartzMap.compSubConstCLM ℂ (-a) φ
    have e3 : ∫ t, φ t * U (t - a) = ∫ t, ψ t * U t := by
      rw [← integral_add_right_eq_self (μ := volume) _ a]
      congr 1; funext t
      simp [ψ]
    have hU : U = 𝓕⁻ (𝓕 U) := (FourierTransform.fourierInv_fourier_eq U).symm
    rw [e3]
    conv_lhs => rw [hU]
    rw [fi_pair_fourierInv]
    congr 1; funext t
    have : (𝓕⁻ ψ) t = ePhase ⟪-a, t⟫_ℝ * (𝓕⁻ φ) t := by
      rw [SchwartzMap.fourierInv_coe, SchwartzMap.fourierInv_coe]
      have hψ : (ψ : Rd d → ℂ) = fun s => φ (s - -a) := by funext s; simp [ψ]
      rw [hψ, fi_fourierInv_transl]
    rw [this]; ring
  rw [key, FourierTransform.fourier_fourierInv_eq]


lemma fi_fourierL2_eq {f : Rd d → ℂ} (hf : MemLp f 2 volume) :
    fourierL2 f = ⇑(𝓕 (hf.toLp f) : Lp ℂ 2 (volume : Measure (Rd d))) := by
  unfold fourierL2; rw [dif_pos hf]

lemma fi_comp_sub_ae {u v : Rd d → ℂ} (h : u =ᵐ[volume] v) (a : Rd d) :
    (fun t => u (t - a)) =ᵐ[volume] fun t => v (t - a) :=
  (measurePreserving_sub_right volume a).quasiMeasurePreserving.ae_eq_comp h

theorem fi_stft_fundamental_identity {f g : Rd d → ℂ} (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) (x ω : Rd d) :
    stft g f x ω = ePhase (-⟪x, ω⟫_ℝ) * stft (fourierL2 g) (fourierL2 f) ω (-x) := by
  set F := hf.toLp f
  set G := hg.toLp g
  set W := fi_mo ω (fi_tr x G)
  have hW : (W : Rd d → ℂ) =ᵐ[volume] fun t => ePhase ⟪ω, t⟫_ℝ * g (t - x) := by
    filter_upwards [fi_mo_ae ω (fi_tr x G), fi_tr_ae x G, fi_comp_sub_ae hg.coeFn_toLp x]
      with t h1 h2 h3
    rw [h1, h2, h3]
  have step1 : stft g f x ω = inner ℂ W F := by
    rw [MeasureTheory.L2.inner_def]
    unfold stft
    apply integral_congr_ae
    filter_upwards [hW, hf.coeFn_toLp] with t h1 h2
    rw [h1, h2, RCLike.inner_apply, map_mul, fi_conj_ePhase]
    ring
  have hFW : ((𝓕 W : Lp ℂ 2 (volume : Measure (Rd d))) : Rd d → ℂ) =ᵐ[volume]
      fun ξ => ePhase ⟪-x, ξ - ω⟫_ℝ * (𝓕 G : Lp ℂ 2 (volume : Measure (Rd d))) (ξ - ω) := by
    rw [fi_fourier_mo, fi_fourier_tr]
    filter_upwards [fi_tr_ae ω (fi_mo (-x) (𝓕 G)), fi_comp_sub_ae (fi_mo_ae (-x) (𝓕 G)) ω]
      with t h1 h2
    rw [h1, h2]
  rw [step1, ← Lp.inner_fourier_eq, MeasureTheory.L2.inner_def, fi_fourierL2_eq hf,
    fi_fourierL2_eq hg]
  unfold stft
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hFW] with t h1
  rw [h1, RCLike.inner_apply, map_mul, fi_conj_ePhase]
  have : -⟪-x, t - ω⟫_ℝ = -⟪x, ω⟫_ℝ + -⟪-x, t⟫_ℝ := by
    simp only [inner_neg_left, inner_sub_right]; ring
  rw [this, fi_ePhase_add]
  ring

end FaulhuberTFA

open FaulhuberTFA in
theorem solution {d : ℕ} {f g : Rd d → ℂ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (x ω : Rd d) :
    stft g f x ω = ePhase (-⟪x, ω⟫_ℝ) * stft (fourierL2 g) (fourierL2 f) ω (-x) :=
  fi_stft_fundamental_identity hf hg x ω
