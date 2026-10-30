-- Prove2me | solution 1 for FragileBandit.CauchyTail.eq_47
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T13:20:54.449995+00:00
-- url     : https://prove2.me/submissions/32ad4fa9-dae0-448e-a1f9-b18c6d9201d7

import Mathlib
import Definitions.Def_FragileBandit_CauchyTail_Setting
import Theorems.Thm_FragileBandit_CauchyTail_change_of_measure
import Theorems.Thm_FragileBandit_CauchyTail_theorem_4
import Theorems.Thm_FragileBandit_CauchyTail_remark_3
import Theorems.Thm_FragileBandit_CauchyTail_dinf_eq_dP
import Theorems.Thm_FragileBandit_CauchyTail_random_index_wlln
import Theorems.Thm_FragileBandit_CauchyTail_markov_tail_bound

open MeasureTheory ProbabilityTheory Filter BanditAlgorithm FragileBandit.CauchyTail
open scoped ENNReal Topology

namespace CTExpFam

variable {P : Measure ℝ} [IsProbabilityMeasure P]

/-- The normalizer `Z(s) = ∫ e^{s x} dP`. -/
noncomputable def Z (P : Measure ℝ) (s : ℝ) : ℝ := ∫ x, Real.exp (s * x) ∂P

/-- The tilted mean. -/
noncomputable def mn (P : Measure ℝ) (s : ℝ) : ℝ := ∫ x, x ∂(tilt P s)

instance tilt_isFinite (s : ℝ) : IsFiniteMeasure (tilt P s) := by
  unfold tilt; infer_instance

lemma Z_pos {s : ℝ} (hs : s ∈ natParamSet P) : 0 < Z P s := integral_exp_pos hs

lemma tilt_isProb {s : ℝ} (hs : s ∈ natParamSet P) : IsProbabilityMeasure (tilt P s) :=
  isProbabilityMeasure_tilted hs

lemma tilt_ac (s : ℝ) : tilt P s ≪ P := tilted_absolutelyContinuous _ _

lemma ac_tilt {s : ℝ} (hs : s ∈ natParamSet P) : P ≪ tilt P s := absolutelyContinuous_tilted hs

lemma llr_tilt {s s' : ℝ} (hs : s ∈ natParamSet P) (hs' : s' ∈ natParamSet P) :
    llr (tilt P s) (tilt P s') =ᵐ[P]
      fun x => (s - s') * x - Real.log (Z P s) + Real.log (Z P s') := by
  have h1 := llr_tilted_left (μ := P) (ν := tilt P s') (f := fun x => s * x) (ac_tilt hs') hs
    (measurable_const.mul measurable_id).aemeasurable
  have h2 := llr_tilted_right (μ := P) (ν := P) (f := fun x => s' * x)
    Measure.AbsolutelyContinuous.rfl hs'
  have h3 := llr_self P
  unfold tilt at h1 ⊢
  filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
  rw [hx1, hx2, hx3]
  simp only [Z, Pi.zero_apply]
  ring

lemma tilt_ac_tilt {s s' : ℝ} (hs' : s' ∈ natParamSet P) : tilt P s ≪ tilt P s' :=
  (tilt_ac s).trans (ac_tilt hs')

lemma integrable_llr_tilt {s s' : ℝ} (hs : s ∈ natParamSet P) (hs' : s' ∈ natParamSet P)
    (hint : Integrable id (tilt P s)) : Integrable (llr (tilt P s) (tilt P s')) (tilt P s) := by
  have := tilt_isProb hs
  have hae : llr (tilt P s) (tilt P s') =ᵐ[tilt P s]
      fun x => (s - s') * x - Real.log (Z P s) + Real.log (Z P s') :=
    (tilt_ac s).ae_le (llr_tilt hs hs')
  refine Integrable.congr ?_ hae.symm
  exact ((hint.const_mul (s - s')).sub (integrable_const _)).add (integrable_const _)

lemma integral_llr_tilt {s s' : ℝ} (hs : s ∈ natParamSet P) (hs' : s' ∈ natParamSet P)
    (hint : Integrable id (tilt P s)) :
    ∫ x, llr (tilt P s) (tilt P s') x ∂(tilt P s) =
      (s - s') * mn P s - Real.log (Z P s) + Real.log (Z P s') := by
  have := tilt_isProb hs
  have hae : llr (tilt P s) (tilt P s') =ᵐ[tilt P s]
      fun x => (s - s') * x - Real.log (Z P s) + Real.log (Z P s') :=
    (tilt_ac s).ae_le (llr_tilt hs hs')
  rw [integral_congr_ae hae]
  rw [integral_add, integral_sub, integral_const_mul, integral_const, integral_const]
  · simp [mn]
  · exact hint.const_mul _
  · exact integrable_const _
  · exact (hint.const_mul _).sub (integrable_const _)
  · exact integrable_const _

/-- The real KL divergence between tilts is nonnegative. -/
lemma kl_real_nonneg {s s' : ℝ} (hs : s ∈ natParamSet P) (hs' : s' ∈ natParamSet P)
    (hint : Integrable id (tilt P s)) :
    0 ≤ (s - s') * mn P s - Real.log (Z P s) + Real.log (Z P s') := by
  have := tilt_isProb hs
  have := tilt_isProb hs'
  have := InformationTheory.integral_llr_add_sub_measure_univ_nonneg (tilt_ac_tilt (s := s) hs')
    (integrable_llr_tilt hs hs' hint)
  rw [integral_llr_tilt hs hs' hint] at this
  simpa using this

lemma kl_tilt {s s' : ℝ} (hs : s ∈ natParamSet P) (hs' : s' ∈ natParamSet P)
    (hint : Integrable id (tilt P s)) :
    InformationTheory.klDiv (tilt P s) (tilt P s') =
      ENNReal.ofReal ((s - s') * mn P s - Real.log (Z P s) + Real.log (Z P s')) := by
  have := tilt_isProb hs
  have := tilt_isProb hs'
  rw [InformationTheory.klDiv_of_ac_of_integrable (tilt_ac_tilt hs')
    (integrable_llr_tilt hs hs' hint), integral_llr_tilt hs hs' hint]
  simp

lemma mn_mono {s s' : ℝ} (hs : s ∈ natParamSet P) (hs' : s' ∈ natParamSet P)
    (hint : Integrable id (tilt P s)) (hint' : Integrable id (tilt P s')) (hss : s ≤ s') :
    mn P s ≤ mn P s' := by
  have h1 := kl_real_nonneg hs hs' hint
  have h2 := kl_real_nonneg hs' hs hint'
  rcases eq_or_lt_of_le hss with h | h
  · rw [h]
  · have : 0 ≤ (s' - s) * (mn P s' - mn P s) := by nlinarith
    have hpos : 0 < s' - s := by linarith
    nlinarith

lemma tilt_eq_of_mn_eq {s s' : ℝ} (hs : s ∈ natParamSet P) (hs' : s' ∈ natParamSet P)
    (hint : Integrable id (tilt P s)) (hint' : Integrable id (tilt P s'))
    (heq : mn P s = mn P s') : tilt P s = tilt P s' := by
  have := tilt_isProb hs
  have := tilt_isProb hs'
  have h1 := kl_real_nonneg hs hs' hint
  have h2 := kl_real_nonneg hs' hs hint'
  have h0 : (s - s') * mn P s - Real.log (Z P s) + Real.log (Z P s') = 0 := by
    rw [heq] at h1 ⊢; nlinarith
  have hkl := kl_tilt hs hs' hint
  rw [h0, ENNReal.ofReal_zero] at hkl
  exact InformationTheory.klDiv_eq_zero_iff.1 hkl


lemma mn_const_of_tilt_eq {s s' : ℝ} (hs : s ∈ natParamSet P) (hs' : s' ∈ natParamSet P)
    (hss : s ≠ s') (heq : tilt P s = tilt P s') :
    ∀ u ∈ natParamSet P, mn P u = mn P s := by
  have h1 := rnDeriv_tilted_left_self (μ := P) (f := fun x => s * x)
    (measurable_const.mul measurable_id).aemeasurable
  have h2 := rnDeriv_tilted_left_self (μ := P) (f := fun x => s' * x)
    (measurable_const.mul measurable_id).aemeasurable
  have heq' : P.tilted (fun x => s * x) = P.tilted (fun x => s' * x) := heq
  rw [heq'] at h1
  have hZs := Z_pos hs
  have hZs' := Z_pos hs'
  set c : ℝ := Real.log (Z P s' / Z P s) / (s' - s) with hc
  have hsub : s' - s ≠ 0 := sub_ne_zero.2 (Ne.symm hss)
  have hx : ∀ᵐ x ∂P, x = c := by
    filter_upwards [h1, h2] with x hx1 hx2
    rw [hx2] at hx1
    have hr := (ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)).1 hx1
    change Real.exp (s' * x) / Z P s' = Real.exp (s * x) / Z P s at hr
    -- exp(s' x)/Z s' = exp(s x)/Z s
    have hr' : Real.exp ((s' - s) * x) = Z P s' / Z P s := by
      rw [div_eq_div_iff hZs'.ne' hZs.ne'] at hr
      rw [eq_div_iff hZs.ne', sub_mul, Real.exp_sub]
      field_simp
      simpa [mul_comm] using hr
    have := congrArg Real.log hr'
    rw [Real.log_exp] at this
    rw [hc, ← this]
    field_simp
  have hmn : ∀ u ∈ natParamSet P, mn P u = c := by
    intro u hu
    have hZu : Z P u = Real.exp (u * c) := by
      unfold Z
      have hae : (fun x => Real.exp (u * x)) =ᵐ[P] fun _ => Real.exp (u * c) :=
        hx.mono (fun x hx => by rw [hx])
      rw [integral_congr_ae hae]
      simp
    unfold mn tilt
    rw [integral_tilted]
    have hae : (fun x => (Real.exp (u * x) / ∫ x, Real.exp (u * x) ∂P) • x) =ᵐ[P]
        fun _ => (Real.exp (u * c) / Z P u) • c := by
      filter_upwards [hx] with x hx
      rw [hx]; rfl
    rw [integral_congr_ae hae, hZu]
    simp only [integral_const, probReal_univ, one_smul, smul_eq_mul]
    field_simp
  intro u hu
  rw [hmn u hu, hmn s hs]

lemma natParamSet_eq (P : Measure ℝ) : natParamSet P = integrableExpSet id P := by
  ext t; rfl

lemma integrable_id_of_interior {s : ℝ} (hs : s ∈ interior (natParamSet P)) :
    Integrable id (tilt P s) := by
  have hs' : s ∈ natParamSet P := interior_subset hs
  unfold tilt
  rw [integrable_tilted_iff hs']
  rw [natParamSet_eq] at hs
  have := integrable_pow_mul_exp_of_mem_interior_integrableExpSet (X := id) (μ := P) hs 1
  refine this.congr (Eventually.of_forall (fun x => ?_))
  simp [mul_comm]

lemma continuousAt_logZ {s : ℝ} (hs : s ∈ interior (natParamSet P)) :
    ContinuousAt (fun u => Real.log (Z P u)) s := by
  have hZ : (fun u => Z P u) = mgf id P := by
    funext u; rfl
  have hc : ContinuousAt (fun u => Z P u) s := by
    rw [hZ]
    rw [natParamSet_eq] at hs
    exact continuousOn_mgf.continuousAt (isOpen_interior.mem_nhds hs)
  exact hc.log (Z_pos (interior_subset hs)).ne'

lemma theta_spec {z : ℝ} (hz : z ∈ meanSet P) :
    thetaOf P z ∈ natParamSet P ∧ Integrable id (tilt P (thetaOf P z)) ∧
      mn P (thetaOf P z) = z := by
  have hz' : ∃ θ ∈ natParamSet P, Integrable id (tilt P θ) ∧ ∫ x, x ∂(tilt P θ) = z := hz
  unfold thetaOf
  rw [dif_pos hz']
  exact ⟨hz'.choose_spec.1, hz'.choose_spec.2.1, hz'.choose_spec.2.2⟩

end CTExpFam


namespace CTExpFam

variable {P : Measure ℝ} [IsProbabilityMeasure P]

lemma exp_mul_le_of_mem_Icc {s0 s1 u x : ℝ} (hu : u ∈ Set.Icc s0 s1) :
    Real.exp (u * x) ≤ Real.exp (s0 * x) + Real.exp (s1 * x) := by
  by_cases hx : 0 ≤ x
  · have : u * x ≤ s1 * x := mul_le_mul_of_nonneg_right hu.2 hx
    have := Real.exp_le_exp.2 this
    linarith [Real.exp_pos (s0 * x)]
  · push Not at hx
    have : u * x ≤ s0 * x := mul_le_mul_of_nonpos_right hu.1 hx.le
    have := Real.exp_le_exp.2 this
    linarith [Real.exp_pos (s1 * x)]

lemma continuousOn_Z {s0 s1 : ℝ} (hs0 : s0 ∈ natParamSet P) (hs1 : s1 ∈ natParamSet P) :
    ContinuousOn (fun u => Z P u) (Set.Icc s0 s1) := by
  unfold Z
  refine continuousOn_of_dominated (bound := fun x => Real.exp (s0 * x) + Real.exp (s1 * x))
    ?_ ?_ ?_ ?_
  · intro u _
    exact (Real.continuous_exp.measurable.comp (measurable_const.mul measurable_id)).aestronglyMeasurable
  · intro u hu
    refine Eventually.of_forall (fun x => ?_)
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact exp_mul_le_of_mem_Icc hu
  · exact hs0.add hs1
  · exact Eventually.of_forall (fun x => (by fun_prop : Continuous fun u : ℝ => Real.exp (u * x)).continuousOn)

lemma integrable_exp_mul_id {s : ℝ} (hs : s ∈ natParamSet P) (hint : Integrable id (tilt P s)) :
    Integrable (fun x => Real.exp (s * x) * x) P := by
  unfold tilt at hint
  rw [integrable_tilted_iff hs] at hint
  simpa [smul_eq_mul] using hint

lemma continuousOn_G {s0 s1 : ℝ} (hs0 : s0 ∈ natParamSet P) (hs1 : s1 ∈ natParamSet P)
    (hi0 : Integrable id (tilt P s0)) (hi1 : Integrable id (tilt P s1)) :
    ContinuousOn (fun u => ∫ x, Real.exp (u * x) * x ∂P) (Set.Icc s0 s1) := by
  refine continuousOn_of_dominated
    (bound := fun x => Real.exp (s0 * x) * |x| + Real.exp (s1 * x) * |x|) ?_ ?_ ?_ ?_
  · intro u _
    exact ((Real.continuous_exp.measurable.comp (measurable_const.mul measurable_id)).mul
      measurable_id).aestronglyMeasurable
  · intro u hu
    refine Eventually.of_forall (fun x => ?_)
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_eq_abs, ← add_mul]
    exact mul_le_mul_of_nonneg_right (exp_mul_le_of_mem_Icc hu) (abs_nonneg x)
  · have h0 := (integrable_exp_mul_id hs0 hi0).norm
    have h1 := (integrable_exp_mul_id hs1 hi1).norm
    refine (h0.add h1).congr (Eventually.of_forall (fun x => ?_))
    simp [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_eq_abs]
  · exact Eventually.of_forall (fun x =>
      (by fun_prop : Continuous fun u : ℝ => Real.exp (u * x) * x).continuousOn)

lemma mn_eq {u : ℝ} (hu : u ∈ natParamSet P) :
    mn P u = (∫ x, Real.exp (u * x) * x ∂P) / Z P u := by
  unfold mn tilt
  rw [integral_tilted]
  simp only [smul_eq_mul]
  rw [← integral_div]
  congr 1; funext x; unfold Z; ring

lemma continuousOn_mn {s0 s1 : ℝ} (hs0 : s0 ∈ natParamSet P) (hs1 : s1 ∈ natParamSet P)
    (hi0 : Integrable id (tilt P s0)) (hi1 : Integrable id (tilt P s1))
    (hsub : Set.Icc s0 s1 ⊆ natParamSet P) :
    ContinuousOn (fun u => mn P u) (Set.Icc s0 s1) := by
  have h := (continuousOn_G hs0 hs1 hi0 hi1).div (continuousOn_Z hs0 hs1)
    (fun u hu => (Z_pos (hsub hu)).ne')
  refine h.congr (fun u hu => ?_)
  exact mn_eq (hsub hu)

lemma mn_strict {s s' : ℝ} (hs : s ∈ natParamSet P) (hs' : s' ∈ natParamSet P)
    (hint : Integrable id (tilt P s)) (hint' : Integrable id (tilt P s')) (hlt : s < s')
    {v v' : ℝ} (hv : v ∈ natParamSet P) (hv' : v' ∈ natParamSet P) (hne : mn P v ≠ mn P v') :
    mn P s < mn P s' := by
  refine lt_of_le_of_ne (mn_mono hs hs' hint hint' hlt.le) (fun heq => ?_)
  have ht := tilt_eq_of_mn_eq hs hs' hint hint' heq
  have hc := mn_const_of_tilt_eq hs hs' hlt.ne ht
  exact hne (by rw [hc v hv, hc v' hv'])

/-- Real KL divergence between tilts. -/
noncomputable def Kr (P : Measure ℝ) (u s' : ℝ) : ℝ :=
  (u - s') * mn P u - Real.log (Z P u) + Real.log (Z P s')

lemma dP_eq_Kr {z y : ℝ} (hz : z ∈ meanSet P) (hy : y ∈ meanSet P) :
    dP P z y = ENNReal.ofReal (Kr P (thetaOf P z) (thetaOf P y)) := by
  obtain ⟨hs, hint, _⟩ := theta_spec hz
  obtain ⟨hs', _, _⟩ := theta_spec hy
  unfold dP expFam Kr
  exact kl_tilt hs hs' hint

end CTExpFam

namespace CTExpFam

variable {P : Measure ℝ} [IsProbabilityMeasure P]

lemma continuousOn_Kr {s0 s1 s' : ℝ} (hs0 : s0 ∈ natParamSet P) (hs1 : s1 ∈ natParamSet P)
    (hi0 : Integrable id (tilt P s0)) (hi1 : Integrable id (tilt P s1))
    (hsub : Set.Icc s0 s1 ⊆ natParamSet P) :
    ContinuousOn (fun u => Kr P u s') (Set.Icc s0 s1) := by
  unfold Kr
  have h0 : ContinuousOn (fun u : ℝ => u - s') (Set.Icc s0 s1) :=
    continuousOn_id.sub continuousOn_const
  have h1 := h0.mul (continuousOn_mn hs0 hs1 hi0 hi1 hsub)
  have h2 := (continuousOn_Z hs0 hs1).log (fun u hu => (Z_pos (hsub hu)).ne')
  exact (h1.sub h2).add continuousOn_const

/-- Perturbation: the infimum defining `tailRatio` can be approached by means avoiding any
finite set. -/
lemma perturb (y w : ℝ) (hy : y ∈ meanSet P) (hw : w ∈ meanSet P) (hwy : w < y)
    (F : Finset ℝ) (c : ℝ≥0∞) (hc : tailRatio P y w < c) :
    ∃ z ∈ meanSet P, z < w ∧ z ∉ F ∧ dP P z y / dP P z w < c := by
  unfold tailRatio at hc
  simp only [iInf_lt_iff] at hc
  obtain ⟨z0, ⟨hz0, hz0w⟩, hrat⟩ := hc
  have hz0w' : z0 < w := hz0w
  obtain ⟨hs0, hi0, hm0⟩ := theta_spec hz0
  obtain ⟨hsw, hiw, hmw⟩ := theta_spec hw
  obtain ⟨hsy, hiy, hmy⟩ := theta_spec hy
  set s0 := thetaOf P z0 with hs0def
  set sw := thetaOf P w with hswdef
  set sy := thetaOf P y with hsydef
  have hs0w : s0 < sw := by
    by_contra h; push Not at h
    have := mn_mono hsw hs0 hiw hi0 h; linarith
  have hconv : Convex ℝ (natParamSet P) := by
    rw [natParamSet_eq]; exact convex_integrableExpSet
  have hIcc : Set.Icc s0 sw ⊆ natParamSet P := fun u hu => hconv.ordConnected.out hs0 hsw hu
  have hIoo : Set.Ioo s0 sw ⊆ interior (natParamSet P) :=
    interior_maximal (fun u hu => hIcc ⟨hu.1.le, hu.2.le⟩) isOpen_Ioo
  have hne : mn P sw ≠ mn P sy := by rw [hmw, hmy]; exact hwy.ne
  set s1 := (s0 + sw) / 2 with hs1def
  have hs01 : s0 < s1 := by rw [hs1def]; linarith
  have hs1w : s1 < sw := by rw [hs1def]; linarith
  have hs1int : s1 ∈ interior (natParamSet P) := hIoo ⟨hs01, hs1w⟩
  have hs1 : s1 ∈ natParamSet P := interior_subset hs1int
  have hi1 : Integrable id (tilt P s1) := integrable_id_of_interior hs1int
  have hsub : Set.Icc s0 s1 ⊆ natParamSet P := fun u hu => hIcc ⟨hu.1, hu.2.trans hs1w.le⟩
  set A : ℝ → ℝ := fun u => Kr P u sy with hA
  set B : ℝ → ℝ := fun u => Kr P u sw with hB
  have hAc : ContinuousOn A (Set.Icc s0 s1) := continuousOn_Kr hs0 hs1 hi0 hi1 hsub
  have hBc : ContinuousOn B (Set.Icc s0 s1) := continuousOn_Kr hs0 hs1 hi0 hi1 hsub
  have hrat0 : dP P z0 y / dP P z0 w = ENNReal.ofReal (A s0) / ENNReal.ofReal (B s0) := by
    rw [dP_eq_Kr hz0 hy, dP_eq_Kr hz0 hw]
  have hB0 : ENNReal.ofReal (B s0) ≠ 0 := by
    intro h0
    have hkl : InformationTheory.klDiv (tilt P s0) (tilt P sw) = 0 := by
      rw [kl_tilt hs0 hsw hi0]; exact h0
    haveI := tilt_isProb hs0
    haveI := tilt_isProb hsw
    have ht := InformationTheory.klDiv_eq_zero_iff.1 hkl
    have : mn P s0 = mn P sw := by unfold mn; rw [ht]
    rw [hm0, hmw] at this; linarith
  have hmemI : s0 ∈ Set.Icc s0 s1 := ⟨le_rfl, hs01.le⟩
  have hR : Tendsto (fun u => ENNReal.ofReal (A u) / ENNReal.ofReal (B u))
      (𝓝[Set.Icc s0 s1] s0) (𝓝 (ENNReal.ofReal (A s0) / ENNReal.ofReal (B s0))) := by
    apply ENNReal.Tendsto.div
    · exact ENNReal.tendsto_ofReal (hAc s0 hmemI)
    · exact Or.inr hB0
    · exact ENNReal.tendsto_ofReal (hBc s0 hmemI)
    · exact Or.inl ENNReal.ofReal_ne_top
  rw [hrat0] at hrat
  have hev := hR.eventually (gt_mem_nhds hrat)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hε, hball⟩ := hev
  set t := min (s0 + ε) s1 with ht
  have hs0t : s0 < t := lt_min (by linarith) hs01
  have hinj : Set.InjOn (fun u => mn P u) (Set.Ioo s0 t) := by
    intro u hu u' hu' heq
    have hut : Set.Ioo s0 t ⊆ Set.Ioo s0 sw := fun v hv =>
      ⟨hv.1, lt_of_lt_of_le hv.2 ((min_le_right _ _).trans hs1w.le)⟩
    have huint := hIoo (hut hu)
    have hu'int := hIoo (hut hu')
    by_contra hne'
    rcases lt_or_gt_of_ne hne' with hlt | hlt
    · have := mn_strict (interior_subset huint) (interior_subset hu'int)
        (integrable_id_of_interior huint) (integrable_id_of_interior hu'int) hlt hsw hsy hne
      exact absurd heq this.ne
    · have := mn_strict (interior_subset hu'int) (interior_subset huint)
        (integrable_id_of_interior hu'int) (integrable_id_of_interior huint) hlt hsw hsy hne
      exact absurd heq.symm this.ne
  have hinf : ((fun u => mn P u) '' Set.Ioo s0 t).Infinite :=
    (Set.Ioo_infinite hs0t).image hinj
  obtain ⟨z, hzimg, hzF⟩ := hinf.exists_notMem_finset F
  obtain ⟨u, huI, rfl⟩ := hzimg
  have huw : u ∈ Set.Ioo s0 sw :=
    ⟨huI.1, lt_of_lt_of_le huI.2 ((min_le_right _ _).trans hs1w.le)⟩
  have huint := hIoo huw
  have hu := interior_subset huint
  have hiu := integrable_id_of_interior huint
  have hzmem : mn P u ∈ meanSet P := ⟨u, hu, hiu, rfl⟩
  refine ⟨mn P u, hzmem, ?_, hzF, ?_⟩
  · rw [← hmw]
    exact mn_strict hu hsw hiu hiw huw.2 hsw hsy hne
  · obtain ⟨hθ, hθi, hθm⟩ := theta_spec hzmem
    have htilt : tilt P (thetaOf P (mn P u)) = tilt P u := tilt_eq_of_mn_eq hθ hu hθi hiu hθm
    have h1 : dP P (mn P u) y = ENNReal.ofReal (A u) := by
      unfold dP expFam; rw [htilt]; exact kl_tilt hu hsy hiu
    have h2 : dP P (mn P u) w = ENNReal.ofReal (B u) := by
      unfold dP expFam; rw [htilt]; exact kl_tilt hu hsw hiu
    rw [h1, h2]
    have hu1 : u ∈ Set.Icc s0 s1 := ⟨huI.1.le, (huI.2.le.trans (min_le_right _ _))⟩
    have hdist : dist u s0 < ε := by
      rw [Real.dist_eq, abs_of_pos (by linarith [huI.1])]
      have := huI.2.trans_le (min_le_left _ _)
      linarith
    exact hball hdist hu1

end CTExpFam

namespace CTE47Aux

variable {K : ℕ}

open Classical


lemma armPullCount_eq_sum {K n : ℕ} (i : Fin K) (h : BanditHistory K n) :
    armPullCount i h = ∑ t : Fin n, if (h t).1 = i then 1 else 0 := by
  unfold armPullCount
  rw [Set.toFinset_ofPred, Finset.card_filter]

lemma armPullCount_le {K n : ℕ} (i : Fin K) (h : BanditHistory K n) :
    armPullCount i h ≤ n := by
  rw [armPullCount_eq_sum]
  calc (∑ t : Fin n, if (h t).1 = i then 1 else 0) ≤ ∑ _t : Fin n, 1 :=
        Finset.sum_le_sum (fun t _ => by split_ifs <;> simp)
    _ = n := by simp

lemma measurable_armPullCount {K n : ℕ} (i : Fin K) :
    Measurable (fun h : BanditHistory K n => armPullCount i h) := by
  have hF : Measurable (fun h : BanditHistory K n => fun t => (h t).1) := by
    rw [measurable_pi_iff]
    intro t
    exact measurable_fst.comp (measurable_pi_apply t)
  have : (fun h : BanditHistory K n => armPullCount i h) =
      (fun a : Fin n → Fin K => ∑ t : Fin n, if a t = i then 1 else 0) ∘
        (fun h : BanditHistory K n => fun t => (h t).1) := by
    funext h; simp [armPullCount_eq_sum]
  rw [this]
  exact (measurable_of_countable _).comp hF


/-- Integral against the step: unfold the step kernel. -/
lemma lintegral_step (ν : StochasticBandit K) (π : BanditPolicy K) (T : ℕ)
    (h : BanditHistory K T) {F : Fin K × ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ p, F p ∂(banditStepKernel ν π T h) = ∫⁻ a, ∫⁻ x, F (a, x) ∂(ν.P a) ∂(π.select T h) := by
  unfold banditStepKernel
  rw [Kernel.lintegral_compProd _ _ _ hF]
  rfl

/-- Unfold the integral over `banditMeasure (T+1)`. -/
lemma lintegral_succ (ν : StochasticBandit K) (π : BanditPolicy K) (T : ℕ)
    {g : BanditHistory K (T + 1) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ h, g h ∂(banditMeasure ν π (T + 1)) =
      ∫⁻ h, ∫⁻ p, g (Fin.snoc (α := fun _ ↦ Fin K × ℝ) h p) ∂(banditStepKernel ν π T h)
        ∂(banditMeasure ν π T) := by
  rw [banditMeasure.eq_2, lintegral_map hg measurable_banditHistorySnoc,
    Measure.lintegral_compProd (f := fun a => g (Fin.snoc (α := fun _ ↦ Fin K × ℝ) a.1 a.2))
      (hg.comp measurable_banditHistorySnoc)]

/-- Number of plays of arm `j` strictly before round `t`. -/
def cntBefore (j : Fin K) {T : ℕ} (h : BanditHistory K T) (t : Fin T) : ℕ :=
  ∑ s : Fin T, if s < t ∧ (h s).1 = j then 1 else 0

/-- Number of rounds `t` in which arm `j` is played for the `≤ m`-th time with reward in `B`. -/
noncomputable def Wc (j : Fin K) (m : ℕ) (B : Set ℝ) {T : ℕ} (h : BanditHistory K T) : ℝ≥0∞ :=
  ∑ t : Fin T, if (h t).1 = j ∧ cntBefore j h t < m ∧ (h t).2 ∈ B then 1 else 0

/-- `min (N_j) m`. -/
noncomputable def Mc (j : Fin K) (m : ℕ) {T : ℕ} (h : BanditHistory K T) : ℝ≥0∞ :=
  ((min (armPullCount j h) m : ℕ) : ℝ≥0∞)

lemma cntBefore_snoc_castSucc (j : Fin K) {T : ℕ} (h : BanditHistory K T) (p : Fin K × ℝ)
    (t : Fin T) :
    cntBefore j (Fin.snoc (α := fun _ ↦ Fin K × ℝ) h p) (Fin.castSucc t) = cntBefore j h t := by
  unfold cntBefore
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.castSucc_lt_castSucc_iff, Fin.snoc_last]
  have : ¬ (Fin.last T < Fin.castSucc t) := not_lt.2 (Fin.le_last _)
  simp [this]

lemma cntBefore_snoc_last (j : Fin K) {T : ℕ} (h : BanditHistory K T) (p : Fin K × ℝ) :
    cntBefore j (Fin.snoc (α := fun _ ↦ Fin K × ℝ) h p) (Fin.last T) = armPullCount j h := by
  unfold cntBefore
  rw [Fin.sum_univ_castSucc, armPullCount_eq_sum]
  simp [Fin.snoc_castSucc, Fin.castSucc_lt_last]

lemma Wc_snoc (j : Fin K) (m : ℕ) (B : Set ℝ) {T : ℕ} (h : BanditHistory K T) (p : Fin K × ℝ) :
    Wc j m B (Fin.snoc (α := fun _ ↦ Fin K × ℝ) h p) =
      Wc j m B h + (if p.1 = j ∧ armPullCount j h < m ∧ p.2 ∈ B then 1 else 0) := by
  classical
  unfold Wc
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, cntBefore_snoc_castSucc, cntBefore_snoc_last]

lemma Mc_snoc (j : Fin K) (m : ℕ) {T : ℕ} (h : BanditHistory K T) (p : Fin K × ℝ) :
    Mc j m (Fin.snoc (α := fun _ ↦ Fin K × ℝ) h p) =
      Mc j m h + (if p.1 = j ∧ armPullCount j h < m then 1 else 0) := by
  unfold Mc
  have hN : armPullCount j (Fin.snoc (α := fun _ ↦ Fin K × ℝ) h p) =
      armPullCount j h + (if p.1 = j then 1 else 0) := by
    rw [armPullCount_eq_sum, armPullCount_eq_sum, Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
  rw [hN]
  by_cases hp : p.1 = j
  · by_cases hm : armPullCount j h < m
    · simp only [hp, hm, and_self, if_true]
      rw [min_eq_left (by omega), min_eq_left (by omega)]
      push_cast; ring
    · simp only [hp, hm, and_false, if_false, if_true, add_zero]
      rw [min_eq_right (by omega), min_eq_right (by omega)]
  · simp [hp]

lemma measurable_arms {T : ℕ} :
    Measurable (fun h : BanditHistory K T => fun t => (h t).1) := by
  rw [measurable_pi_iff]
  intro t
  exact measurable_fst.comp (measurable_pi_apply t)

lemma measurable_Wc (j : Fin K) (m : ℕ) {B : Set ℝ} (hB : MeasurableSet B) (T : ℕ) :
    Measurable (fun h : BanditHistory K T => Wc j m B h) := by
  classical
  unfold Wc
  refine Finset.measurable_sum _ (fun t _ => ?_)
  refine Measurable.ite ?_ measurable_const measurable_const
  have h1 : MeasurableSet {h : BanditHistory K T | (h t).1 = j ∧ cntBefore j h t < m} := by
    have : {h : BanditHistory K T | (h t).1 = j ∧ cntBefore j h t < m} =
        (fun h : BanditHistory K T => fun t => (h t).1) ⁻¹'
          {a : Fin T → Fin K | a t = j ∧
            (∑ s : Fin T, if s < t ∧ a s = j then 1 else 0) < m} := by
      ext h; simp [cntBefore]
    rw [this]
    exact measurable_arms (Set.to_countable _).measurableSet
  have h2 : MeasurableSet {h : BanditHistory K T | (h t).2 ∈ B} :=
    (measurable_snd.comp (measurable_pi_apply t)) hB
  have : {h : BanditHistory K T | (h t).1 = j ∧ cntBefore j h t < m ∧ (h t).2 ∈ B} =
      {h : BanditHistory K T | (h t).1 = j ∧ cntBefore j h t < m} ∩
        {h : BanditHistory K T | (h t).2 ∈ B} := by
    ext h; simp [and_assoc]
  rw [this]; exact h1.inter h2

lemma measurable_Mc (j : Fin K) (m : ℕ) (T : ℕ) :
    Measurable (fun h : BanditHistory K T => Mc j m h) := by
  unfold Mc
  exact (measurable_from_nat (f := fun n : ℕ => ((min n m : ℕ) : ℝ≥0∞))).comp
    (measurable_armPullCount j)

lemma lintegral_sel_ite (μ : Measure (Fin K)) (j : Fin K) (c : ℝ≥0∞) :
    ∫⁻ a, (if a = j then c else 0) ∂μ = c * μ {j} := by
  rw [lintegral_fintype]
  simp [Finset.sum_ite_eq']

lemma step_inc_W (ν : StochasticBandit K) (π : BanditPolicy K) (T : ℕ) (j : Fin K)
    (P : Prop) {B : Set ℝ} (hB : MeasurableSet B) (h : BanditHistory K T) :
    ∫⁻ p, (if p.1 = j ∧ P ∧ p.2 ∈ B then (1 : ℝ≥0∞) else 0) ∂(banditStepKernel ν π T h) =
      (if P then ν.P j B else 0) * π.select T h {j} := by
  classical
  have hm : Measurable (fun p : Fin K × ℝ =>
      (if p.1 = j ∧ P ∧ p.2 ∈ B then (1 : ℝ≥0∞) else 0)) := by
    refine Measurable.ite ?_ measurable_const measurable_const
    have : {p : Fin K × ℝ | p.1 = j ∧ P ∧ p.2 ∈ B} = ({j} ×ˢ {x | P ∧ x ∈ B}) := by
      ext p; simp
    rw [this]
    refine (MeasurableSet.singleton j).prod ?_
    by_cases hP : P
    · simpa [hP] using hB
    · simp [hP]
  rw [lintegral_step ν π T h hm]
  have : ∀ a : Fin K, ∫⁻ x, (if (a, x).1 = j ∧ P ∧ (a, x).2 ∈ B then (1 : ℝ≥0∞) else 0) ∂(ν.P a)
      = if a = j then (if P then ν.P j B else 0) else 0 := by
    intro a
    by_cases ha : a = j
    · subst ha
      by_cases hP : P
      · simp only [hP, true_and, if_true]
        rw [show (fun x : ℝ => if x ∈ B then (1 : ℝ≥0∞) else 0) = B.indicator 1 from by
          ext x; simp [Set.indicator_apply]]
        exact lintegral_indicator_one hB
      · simp [hP]
    · simp [ha]
  simp_rw [this]
  rw [lintegral_sel_ite]

lemma step_inc_M (ν : StochasticBandit K) (π : BanditPolicy K) (T : ℕ) (j : Fin K)
    (P : Prop) (h : BanditHistory K T) :
    ∫⁻ p, (if p.1 = j ∧ P then (1 : ℝ≥0∞) else 0) ∂(banditStepKernel ν π T h) =
      (if P then 1 else 0) * π.select T h {j} := by
  have := step_inc_W ν π T j P MeasurableSet.univ h
  simpa using this

lemma lintegral_Wc (ν : StochasticBandit K) (π : BanditPolicy K) (j : Fin K) (m : ℕ)
    {B : Set ℝ} (hB : MeasurableSet B) (T : ℕ) :
    ∫⁻ h, Wc j m B h ∂(banditMeasure ν π T) = ν.P j B * ∫⁻ h, Mc j m h ∂(banditMeasure ν π T) := by
  classical
  induction T with
  | zero =>
    simp [Wc, Mc, armPullCount, banditMeasure.eq_1]
  | succ T ih =>
    rw [lintegral_succ ν π T (measurable_Wc j m hB (T + 1)),
      lintegral_succ ν π T (measurable_Mc j m (T + 1))]
    simp_rw [Wc_snoc, Mc_snoc]
    have hW : ∀ h : BanditHistory K T,
        ∫⁻ p, (Wc j m B h + if p.1 = j ∧ armPullCount j h < m ∧ p.2 ∈ B then 1 else 0)
          ∂(banditStepKernel ν π T h) =
        Wc j m B h + (if armPullCount j h < m then ν.P j B else 0) * π.select T h {j} := by
      intro h
      rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
      congr 1
      convert step_inc_W ν π T j (armPullCount j h < m) hB h
    have hM : ∀ h : BanditHistory K T,
        ∫⁻ p, (Mc j m h + if p.1 = j ∧ armPullCount j h < m then 1 else 0)
          ∂(banditStepKernel ν π T h) =
        Mc j m h + (if armPullCount j h < m then 1 else 0) * π.select T h {j} := by
      intro h
      rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
      congr 1
      convert step_inc_M ν π T j (armPullCount j h < m) h
    simp_rw [hW, hM]
    have hsel : Measurable (fun h : BanditHistory K T => π.select T h {j}) :=
      (π.select T).measurable_coe (MeasurableSet.singleton j)
    have hind : Measurable (fun h : BanditHistory K T =>
        (if armPullCount j h < m then (1 : ℝ≥0∞) else 0)) := by
      refine Measurable.ite ?_ measurable_const measurable_const
      exact measurable_armPullCount j (t := {n : ℕ | n < m}) MeasurableSet.of_discrete
    have heq : ∀ h : BanditHistory K T,
        (if armPullCount j h < m then ν.P j B else 0) * π.select T h {j} =
          ν.P j B * ((if armPullCount j h < m then 1 else 0) * π.select T h {j}) := by
      intro h; split_ifs <;> simp
    simp_rw [heq]
    rw [lintegral_add_left (measurable_Wc j m hB T), lintegral_add_left (measurable_Mc j m T),
      lintegral_const_mul (ν.P j B)
        (f := fun h => (if armPullCount j h < m then (1 : ℝ≥0∞) else 0) * π.select T h {j})
        (hind.mul hsel), ih, mul_add]

/-- Union bound over the first `m` plays of arm `j`. -/
lemma first_plays_bound (ν : StochasticBandit K) (π : BanditPolicy K) (j : Fin K) (m : ℕ)
    {B : Set ℝ} (hB : MeasurableSet B) (T : ℕ) :
    banditMeasure ν π T {h | ∃ t, (h t).1 = j ∧ cntBefore j h t < m ∧ (h t).2 ∈ B} ≤
      m * ν.P j B := by
  classical
  calc banditMeasure ν π T {h | ∃ t, (h t).1 = j ∧ cntBefore j h t < m ∧ (h t).2 ∈ B}
      ≤ ∫⁻ h, Wc j m B h ∂(banditMeasure ν π T) := by
        rw [← lintegral_indicator_one₀ ?_]
        · apply lintegral_mono
          intro h
          by_cases hh : h ∈ {h : BanditHistory K T | ∃ t, (h t).1 = j ∧ cntBefore j h t < m ∧ (h t).2 ∈ B}
          · rw [Set.indicator_of_mem hh]
            obtain ⟨t, ht⟩ := hh
            unfold Wc
            calc (1 : BanditHistory K T → ℝ≥0∞) h = (if (h t).1 = j ∧ cntBefore j h t < m ∧ (h t).2 ∈ B then 1 else 0) := by
                  simp [ht]
              _ ≤ _ := Finset.single_le_sum (f := fun t => (if (h t).1 = j ∧ cntBefore j h t < m ∧ (h t).2 ∈ B then (1 : ℝ≥0∞) else 0))
                    (fun _ _ => bot_le) (Finset.mem_univ t)
          · rw [Set.indicator_of_notMem hh]; exact bot_le
        · refine (MeasurableSet.nullMeasurableSet ?_)
          have : {h : BanditHistory K T | ∃ t, (h t).1 = j ∧ cntBefore j h t < m ∧ (h t).2 ∈ B} =
              ⋃ t, {h | (h t).1 = j ∧ cntBefore j h t < m ∧ (h t).2 ∈ B} := by ext h; simp
          rw [this]
          refine MeasurableSet.iUnion (fun t => ?_)
          have hmeas := measurable_Wc j m hB T
          have h1 : MeasurableSet {h : BanditHistory K T | (h t).1 = j ∧ cntBefore j h t < m} := by
            have : {h : BanditHistory K T | (h t).1 = j ∧ cntBefore j h t < m} =
                (fun h : BanditHistory K T => fun t => (h t).1) ⁻¹'
                  {a : Fin T → Fin K | a t = j ∧
                    (∑ s : Fin T, if s < t ∧ a s = j then 1 else 0) < m} := by
              ext h; simp [cntBefore]
            rw [this]
            exact measurable_arms (Set.to_countable _).measurableSet
          have h2 : MeasurableSet {h : BanditHistory K T | (h t).2 ∈ B} :=
            (measurable_snd.comp (measurable_pi_apply t)) hB
          have : {h : BanditHistory K T | (h t).1 = j ∧ cntBefore j h t < m ∧ (h t).2 ∈ B} =
              {h : BanditHistory K T | (h t).1 = j ∧ cntBefore j h t < m} ∩
                {h : BanditHistory K T | (h t).2 ∈ B} := by
            ext h; simp [and_assoc]
          rw [this]; exact h1.inter h2
    _ = ν.P j B * ∫⁻ h, Mc j m h ∂(banditMeasure ν π T) := lintegral_Wc ν π j m hB T
    _ ≤ ν.P j B * m := by
        gcongr
        calc ∫⁻ h, Mc j m h ∂(banditMeasure ν π T) ≤ ∫⁻ _h, (m : ℝ≥0∞) ∂(banditMeasure ν π T) := by
              apply lintegral_mono; intro h; unfold Mc; show _ ≤ (m : ℝ≥0∞); exact_mod_cast min_le_right (armPullCount j h) m
          _ = m := by simp
    _ = m * ν.P j B := mul_comm _ _

end CTE47Aux

namespace CTE47Aux

variable {K : ℕ}

open Classical

lemma cntBefore_lt (j : Fin K) {T : ℕ} (h : BanditHistory K T) (t : Fin T) (ht : (h t).1 = j) :
    cntBefore j h t < armPullCount j h := by
  rw [armPullCount_eq_sum]
  unfold cntBefore
  have key : ∀ s : Fin T, (if s < t ∧ (h s).1 = j then 1 else 0) + (if s = t then 1 else 0) ≤
      (if (h s).1 = j then 1 else 0) := by
    intro s
    by_cases hs : s = t
    · subst hs; simp [ht]
    · by_cases h1 : (h s).1 = j
      · simp only [hs, h1, and_true, if_false, add_zero, if_true]
        split_ifs <;> omega
      · simp [hs, h1]
  have hsum := Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) => key s)
  rw [Finset.sum_add_distrib] at hsum
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at hsum
  omega

lemma sum_pulls {T : ℕ} (h : BanditHistory K T) : ∑ a : Fin K, armPullCount a h = T := by
  simp_rw [armPullCount_eq_sum]
  rw [Finset.sum_comm]
  simp

lemma prod_ite_pow {T : ℕ} (p : Fin T → Prop) (a : ℝ≥0∞) :
    ∏ t, (if p t then a else 1) = a ^ (Finset.univ.filter p).card := by
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]

end CTE47Aux


namespace CTE47Aux

variable {K : ℕ}

open Classical

lemma cntBefore_le {T : ℕ} (j : Fin K) (h : BanditHistory K T) (t : Fin T) : cntBefore j h t ≤ T := by
  unfold cntBefore
  calc (∑ s : Fin T, if s < t ∧ (h s).1 = j then 1 else 0) ≤ ∑ _s : Fin T, 1 :=
        Finset.sum_le_sum (fun s _ => by split_ifs <;> simp)
    _ = T := by simp

lemma measurable_rewardSum {T : ℕ} (j : Fin K) {φ : ℝ → ℝ} (hφ : Measurable φ) :
    Measurable (fun h : BanditHistory K T =>
      ∑ t ∈ Finset.univ.filter (fun t : Fin T => (h t).1 = j), φ (h t).2) := by
  have : (fun h : BanditHistory K T =>
      ∑ t ∈ Finset.univ.filter (fun t : Fin T => (h t).1 = j), φ (h t).2) =
      fun h => ∑ t : Fin T, if (h t).1 = j then φ (h t).2 else 0 := by
    funext h; rw [Finset.sum_filter]
  rw [this]
  refine Finset.measurable_sum _ (fun t _ => Measurable.ite ?_ ?_ measurable_const)
  · exact (measurable_fst.comp (measurable_pi_apply t)) (MeasurableSet.singleton j)
  · exact hφ.comp (measurable_snd.comp (measurable_pi_apply t))

end CTE47Aux


namespace CTE47

open CTExpFam CTE47Aux

variable {K : ℕ}

lemma expFam_isProb (P : Measure ℝ) [IsProbabilityMeasure P] {z : ℝ} (hz : z ∈ meanSet P) :
    IsProbabilityMeasure (expFam P z) :=
  tilt_isProb (theta_spec hz).1

lemma mean_expFam (P : Measure ℝ) [IsProbabilityMeasure P] {z : ℝ} (hz : z ∈ meanSet P) :
    ∫ x, x ∂(expFam P z) = z := (theta_spec hz).2.2

lemma model_eq (P : Measure ℝ) [IsProbabilityMeasure P] {ν : StochasticBandit K}
    (hν : IsModelEnv P ν) (j : Fin K) :
    banditArmMean ν j ∈ meanSet P ∧ ν.P j = expFam P (banditArmMean ν j) := by
  obtain ⟨z, hz, hzeq⟩ := hν j
  have hm : banditArmMean ν j = z := by
    unfold banditArmMean; rw [← hzeq]; exact mean_expFam P hz
  rw [hm]; exact ⟨hz, hzeq.symm⟩

lemma optMean_mem (P : Measure ℝ) [IsProbabilityMeasure P] {ν : StochasticBandit K}
    (hν : IsModelEnv P ν) (hK : 0 < K) :
    ∃ j, banditOptimalMean ν = banditArmMean ν j := by
  haveI : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  obtain ⟨j, hj⟩ := exists_eq_ciSup_of_finite (f := banditArmMean ν)
  exact ⟨j, hj.symm⟩

lemma dP_pos_fin (P : Measure ℝ) [IsProbabilityMeasure P] {z y : ℝ} (hz : z ∈ meanSet P)
    (hy : y ∈ meanSet P) (hzy : z ≠ y) :
    0 < (dP P z y).toReal ∧ dP P z y ≠ ⊤ := by
  have hfin : dP P z y ≠ ⊤ := by rw [dP_eq_Kr hz hy]; exact ENNReal.ofReal_ne_top
  refine ⟨ENNReal.toReal_pos ?_ hfin, hfin⟩
  intro h0
  haveI := expFam_isProb P hz
  haveI := expFam_isProb P hy
  have := InformationTheory.klDiv_eq_zero_iff.1 h0
  have h1 := mean_expFam P hz
  rw [this, mean_expFam P hy] at h1
  exact hzy h1.symm

lemma le_optMean {ν : StochasticBandit K} (j : Fin K) : banditArmMean ν j ≤ banditOptimalMean ν :=
  le_ciSup (Set.finite_range _).bddAbove j

/-- Lemma 2 (two-sided WLLN for the pull counts of an `M_P`-optimized algorithm) and
divergence to infinity, from Theorem 4, Remark 3 and the `D_inf` identity. -/
lemma lemma2 (P : Measure ℝ) [IsProbabilityMeasure P]
    (hP : (0 : ℝ) ∈ interior (natParamSet P)) (π : BanditPolicy K) (hπ : IsOptimized P π)
    (ν : StochasticBandit K) (hν : IsModelEnv P ν) (hd : DistinctMeans ν) (j : Fin K)
    (hj : 0 < banditGap ν j) (habove : ∃ z ∈ meanSet P, banditOptimalMean ν < z) :
    0 < (dP P (banditArmMean ν j) (banditOptimalMean ν)).toReal ∧
    (∀ δ : ℝ, 0 < δ → Tendsto (fun T : ℕ => banditMeasure ν π T
      {h | δ < |(armPullCount j h : ℝ) / Real.log T -
        1 / (dP P (banditArmMean ν j) (banditOptimalMean ν)).toReal|}) atTop (𝓝 0)) ∧
    (∀ m : ℕ, Tendsto (fun T : ℕ => banditMeasure ν π T {h | armPullCount j h ≤ m})
      atTop (𝓝 0)) := by
  have hK : 0 < K := Fin.pos j
  obtain ⟨hmj, hPj⟩ := model_eq P hν j
  obtain ⟨i0, hi0⟩ := optMean_mem P hν hK
  have hmstar : banditOptimalMean ν ∈ meanSet P := by rw [hi0]; exact (model_eq P hν i0).1
  have hlt : banditArmMean ν j < banditOptimalMean ν := by unfold banditGap at hj; linarith
  set d := dP P (banditArmMean ν j) (banditOptimalMean ν) with hddef
  obtain ⟨hdpos, hdtop⟩ := dP_pos_fin P hmj hmstar hlt.ne
  set c : ℝ := 1 / d.toReal with hcdef
  have hcpos : 0 < c := by rw [hcdef]; positivity
  -- the class `𝓔` and the hypotheses of Theorem 4
  set 𝓔 : Set (StochasticBandit K) := {ν' | IsModelEnv P ν' ∧ DistinctMeans ν'} with h𝓔
  have hM : ∀ Q ∈ model P, IsProbabilityMeasure Q ∧ Integrable id Q := by
    rintro Q ⟨z, hz, rfl⟩
    exact ⟨expFam_isProb P hz, (theta_spec hz).2.1⟩
  have h31 : ∀ ν' ∈ 𝓔, ∀ i, 0 < banditGap ν' i → ∀ a : ℝ, a < 1 → ∀ᶠ T : ℕ in atTop,
      banditMeasure ν' π T {h | (T : ℝ) / K < (armPullCount i h : ℝ)} ≤
        ENNReal.ofReal (Real.exp (-(a * Real.log T))) := by
    rintro ν' ⟨hν', hd'⟩ i hi a ha
    have := FragileBandit.CauchyTail.markov_tail_bound P hP π hπ ν' hν' hd' i hi 1
      ⟨one_pos, le_rfl⟩ (1 / K) (by positivity) a ha
    filter_upwards [this, eventually_gt_atTop 0] with T hT hT0
    have hT0' : (0 : ℝ) < T := by exact_mod_cast hT0
    have hset : {h : BanditHistory K T | (T : ℝ) / K < (armPullCount i h : ℝ)} =
        {h | 1 / (K : ℝ) * (T : ℝ) ^ (1 : ℝ) < (armPullCount i h : ℝ)} := by
      ext h; simp [Real.rpow_one, div_eq_inv_mul]
    rw [hset]
    refine hT.trans (le_of_eq ?_)
    congr 1
    rw [Real.rpow_one, Real.rpow_def_of_pos hT0']
    ring_nf
  have hclosed : ∀ (Q : Measure ℝ) (hQ : IsProbabilityMeasure Q), Q ∈ model P →
      banditOptimalMean ν < ∫ x, x ∂Q → replaceArm ν j Q hQ ∈ 𝓔 := by
    rintro Q hQ ⟨z, hz, rfl⟩ hzlt
    rw [mean_expFam P hz] at hzlt
    have hmean : ∀ i, banditArmMean (replaceArm ν j (expFam P z) hQ) i =
        if i = j then z else banditArmMean ν i := by
      intro i
      unfold banditArmMean replaceArm
      by_cases hij : i = j
      · subst hij; simp [mean_expFam P hz]
      · simp [hij, Function.update_of_ne hij]
    refine ⟨fun i => ?_, fun i i' hii' => ?_⟩
    · by_cases hij : i = j
      · subst hij; simp only [replaceArm, Function.update_self]; exact ⟨z, hz, rfl⟩
      · simp only [replaceArm, Function.update_of_ne hij]; exact hν i
    · rw [hmean i, hmean i'] at hii'
      by_cases hij : i = j <;> by_cases hi'j : i' = j
      · rw [hij, hi'j]
      · simp only [hij, hi'j, if_true, if_false] at hii'
        exfalso; have := le_optMean (ν := ν) i'; linarith
      · simp only [hij, hi'j, if_true, if_false] at hii'
        exfalso; have := le_optMean (ν := ν) i; linarith
      · simp only [hij, hi'j, if_false] at hii'
        exact hd hii'
  have hlog_pos : ∀ t : ℝ, 1 < t → 0 < Real.log t := fun t ht => Real.log_pos ht
  have hlog_mono : MonotoneOn Real.log (Set.Ioi 1) := fun s hs t _ hst =>
    Real.log_le_log (by linarith [hs.out]) hst
  have hlog_log : ∀ a : ℝ, a < 1 → ∀ᶠ t : ℝ in atTop, a * Real.log t ≤ Real.log t := by
    intro a ha
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have := Real.log_nonneg ht
    nlinarith
  have hlog_o : Tendsto (fun t : ℝ => Real.log t / t) atTop (𝓝 0) := by
    have := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
    simpa using this
  have hν𝓔 : ν ∈ 𝓔 := ⟨hν, hd⟩
  have hT4 := FragileBandit.CauchyTail.theorem_4 (model P) hM Real.log hlog_pos hlog_mono hlog_log
    hlog_o π 𝓔 (fun ν' hν' i => hν'.1 i) h31 ν hν𝓔 j hj hclosed
  have hDinf : banditDInf (model P) (ν.P j) (banditOptimalMean ν) = d := by
    rw [hPj, hddef]
    exact FragileBandit.CauchyTail.dinf_eq_dP P hP _ _ hmj hmstar hlt habove
  have hdeq : d = ENNReal.ofReal d.toReal := (ENNReal.ofReal_toReal hdtop).symm
  -- (32) in the form needed
  have h32 : ∀ c' : ℝ, c' < c → Tendsto (fun T : ℕ => banditMeasure ν π T
      {h | c' * Real.log T ≤ (armPullCount j h : ℝ)}) atTop (𝓝 1) := by
    intro c' hc'
    apply hT4.1 c'
    rw [hDinf]
    by_cases hc'0 : c' ≤ 0
    · rw [ENNReal.ofReal_of_nonpos hc'0, zero_mul]; exact one_pos
    push Not at hc'0
    rw [hdeq, ← ENNReal.ofReal_mul hc'0.le, ← ENNReal.ofReal_one]
    refine (ENNReal.ofReal_lt_ofReal_iff one_pos).2 ?_
    rw [hcdef, lt_div_iff₀ hdpos] at hc'
    exact hc'
  refine ⟨hdpos, ?_, ?_⟩
  · -- Remark 3
    have hE := hπ ν hν hd j hj
    refine FragileBandit.CauchyTail.remark_3 ν π j c hcpos.le hE ?_
    intro ε hε
    have := h32 ((1 - ε) * c) (by nlinarith [hε.1])
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with T hT
    have hT' : (1 : ℝ) < T := by
      have : (2 : ℝ) ≤ T := by exact_mod_cast hT
      linarith
    have hl := Real.log_pos hT'
    congr 1
    ext h
    simp only [Set.mem_ofPred_eq]
    rw [le_div_iff₀ hl]
  · intro m
    have := h32 (c / 2) (by linarith)
    have hc2 : Tendsto (fun T : ℕ => 1 - banditMeasure ν π T
        {h | c / 2 * Real.log T ≤ (armPullCount j h : ℝ)}) atTop (𝓝 0) := by
      have := ENNReal.Tendsto.sub tendsto_const_nhds this (Or.inl ENNReal.one_ne_top)
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hc2
      (Eventually.of_forall (fun _ => bot_le)) ?_
    have hlogT : Tendsto (fun T : ℕ => c / 2 * Real.log T) atTop atTop :=
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop (by positivity)
    filter_upwards [hlogT.eventually (eventually_gt_atTop (m : ℝ))] with T hT
    have hAm : MeasurableSet {h : BanditHistory K T | c / 2 * Real.log T ≤ (armPullCount j h : ℝ)} :=
      measurable_armPullCount j (t := {n : ℕ | c / 2 * Real.log T ≤ (n : ℝ)})
        MeasurableSet.of_discrete
    rw [← prob_compl_eq_one_sub hAm]
    apply measure_mono
    intro h hh
    simp only [Set.mem_ofPred_eq] at hh
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]
    have : (armPullCount j h : ℝ) ≤ m := by exact_mod_cast hh
    linarith

end CTE47

namespace CTE47

open CTExpFam CTE47Aux

variable {K : ℕ}

lemma choose_distinct (S : Finset (Fin K)) (F0 : Finset ℝ) (good : Fin K → ℝ → Prop)
    (h : ∀ j ∈ S, ∀ F : Finset ℝ, ∃ z, z ∉ F ∧ good j z) :
    ∃ z : Fin K → ℝ, (∀ j ∈ S, good j (z j) ∧ z j ∉ F0) ∧ Set.InjOn z S := by
  classical
  revert h
  refine Finset.induction_on S ?_ ?_
  · intro _
    exact ⟨fun _ => 0, by simp, by simp⟩
  · intro a S ha ih h
    obtain ⟨z, hz, hinj⟩ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    obtain ⟨za, hzaF, hgood⟩ := h a (Finset.mem_insert_self a S) (F0 ∪ S.image z)
    refine ⟨Function.update z a za, ?_, ?_⟩
    · intro j hj
      rcases Finset.mem_insert.1 hj with rfl | hjS
      · rw [Function.update_self]
        exact ⟨hgood, fun h' => hzaF (Finset.mem_union_left _ h')⟩
      · have hja : j ≠ a := fun h' => ha (h' ▸ hjS)
        rw [Function.update_of_ne hja]; exact hz j hjS
    · intro i hi i' hi' heq
      have hi2 := Finset.mem_insert.1 (Finset.mem_coe.1 hi)
      have hi'2 := Finset.mem_insert.1 (Finset.mem_coe.1 hi')
      rcases hi2 with rfl | hiS <;> rcases hi'2 with rfl | hi'S
      · rfl
      · exfalso
        have hi'a : i' ≠ i := fun h' => ha (h' ▸ hi'S)
        rw [Function.update_self, Function.update_of_ne hi'a] at heq
        exact hzaF (Finset.mem_union_right _ (Finset.mem_image.2 ⟨i', hi'S, heq.symm⟩))
      · exfalso
        have hia : i ≠ i' := fun h' => ha (h' ▸ hiS)
        rw [Function.update_self, Function.update_of_ne hia] at heq
        exact hzaF (Finset.mem_union_right _ (Finset.mem_image.2 ⟨i, hiS, heq⟩))
      · have hia : i ≠ a := fun h' => ha (h' ▸ hiS)
        have hi'a : i' ≠ a := fun h' => ha (h' ▸ hi'S)
        rw [Function.update_of_ne hia, Function.update_of_ne hi'a] at heq
        exact hinj hiS hi'S heq

open Classical in
/-- The alternative environment: arms in `S` get the laws `P^{z_j}`. -/
noncomputable def altEnv (P : Measure ℝ) [IsProbabilityMeasure P] (ν : StochasticBandit K)
    (S : Finset (Fin K)) (z : Fin K → ℝ) (hz : ∀ j ∈ S, z j ∈ meanSet P) : StochasticBandit K where
  P := fun j => if j ∈ S then expFam P (z j) else ν.P j
  prob := fun j => by
    by_cases hj : j ∈ S
    · simp only [hj, if_true]; exact expFam_isProb P (hz j hj)
    · simp only [hj, if_false]; exact ν.prob j

lemma altEnv_P_mem (P : Measure ℝ) [IsProbabilityMeasure P] (ν : StochasticBandit K)
    (S : Finset (Fin K)) (z : Fin K → ℝ) (hz : ∀ j ∈ S, z j ∈ meanSet P) {j : Fin K}
    (hj : j ∈ S) : (altEnv P ν S z hz).P j = expFam P (z j) := by
  simp [altEnv, hj]

lemma altEnv_P_not_mem (P : Measure ℝ) [IsProbabilityMeasure P] (ν : StochasticBandit K)
    (S : Finset (Fin K)) (z : Fin K → ℝ) (hz : ∀ j ∈ S, z j ∈ meanSet P) {j : Fin K}
    (hj : j ∉ S) : (altEnv P ν S z hz).P j = ν.P j := by
  simp [altEnv, hj]

lemma altEnv_mean (P : Measure ℝ) [IsProbabilityMeasure P] (ν : StochasticBandit K)
    (S : Finset (Fin K)) (z : Fin K → ℝ) (hz : ∀ j ∈ S, z j ∈ meanSet P) (j : Fin K) :
    banditArmMean (altEnv P ν S z hz) j = if j ∈ S then z j else banditArmMean ν j := by
  by_cases hj : j ∈ S
  · rw [if_pos hj]; unfold banditArmMean; rw [altEnv_P_mem P ν S z hz hj, mean_expFam P (hz j hj)]
  · rw [if_neg hj]; unfold banditArmMean; rw [altEnv_P_not_mem P ν S z hz hj]

end CTE47

namespace CTE47

open CTExpFam CTE47Aux

variable {K : ℕ}

/-- (43)–(46): the change-of-measure lower bound for a fixed alternative environment `ν'` in
which arm `k` is optimal and only the arms above `k` are changed. -/
lemma fixedAlt (P : Measure ℝ) [IsProbabilityMeasure P]
    (hP : (0 : ℝ) ∈ interior (natParamSet P)) (π : BanditPolicy K) (hπ : IsOptimized P π)
    (ν : StochasticBandit K) (hν : IsModelEnv P ν) (hd : DistinctMeans ν) (k : Fin K)
    (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1)
    (ν' : StochasticBandit K) (hν' : IsModelEnv P ν') (hd' : DistinctMeans ν')
    (hS' : ∀ j, ¬ (banditArmMean ν k < banditArmMean ν j) → ν'.P j = ν.P j)
    (hopt' : banditOptimalMean ν' = banditArmMean ν k)
    (hlt' : ∀ j, j ≠ k → banditArmMean ν' j < banditArmMean ν k)
    (b : ℝ)
    (hb : ∑ j ∈ Finset.univ.filter (fun j => banditArmMean ν k < banditArmMean ν j),
      (dP P (banditArmMean ν' j) (banditArmMean ν j)).toReal *
        (1 / (dP P (banditArmMean ν' j) (banditArmMean ν k)).toReal) < b)
    (a : ℝ) (hab : b < a) :
    ∀ᶠ T : ℕ in atTop, ENNReal.ofReal ((T : ℝ) ^ (-a)) ≤
      banditMeasure ν π T {h | (1 - γ) * (T : ℝ) < (armPullCount k h : ℝ)} := by
  classical
  set μ := banditArmMean ν with hμdef
  set S := Finset.univ.filter (fun j => μ k < μ j) with hSdef
  have hK : 0 < K := Fin.pos k
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  obtain ⟨hγ0, hγ1⟩ := hγ
  have hmem : ∀ j, μ j ∈ meanSet P := fun j => (model_eq P hν j).1
  have hmem' : ∀ j, banditArmMean ν' j ∈ meanSet P := fun j => (model_eq P hν' j).1
  have hjS : ∀ j ∈ S, μ k < μ j := fun j hj => (Finset.mem_filter.1 hj).2
  have hjk : ∀ j ∈ S, j ≠ k := fun j hj h => by have := hjS j hj; rw [h] at this; linarith
  have hgap' : ∀ j, j ≠ k → 0 < banditGap ν' j := by
    intro j hj; unfold banditGap; rw [hopt']; linarith [hlt' j hj]
  -- constants
  set κ : Fin K → ℝ := fun j => (dP P (banditArmMean ν' j) (μ j)).toReal with hκ
  set cS : Fin K → ℝ := fun j => 1 / (dP P (banditArmMean ν' j) (μ k)).toReal with hcS
  have hκ0 : ∀ j, 0 ≤ κ j := fun j => ENNReal.toReal_nonneg
  have hcS0 : ∀ j, 0 ≤ cS j := fun j => by simp only [hcS]; positivity
  set e : ℝ → ℝ := fun δ => ∑ j ∈ S, (κ j + δ) * (cS j + δ) with he
  have hec : Continuous e := by
    simp only [he]; fun_prop
  have he0 : e 0 < b := by
    show ∑ j ∈ S, (κ j + 0) * (cS j + 0) < b
    simp only [add_zero]; exact hb
  obtain ⟨ε0, hε0, hball⟩ := Metric.eventually_nhds_iff.1 (hec.tendsto 0 |>.eventually (gt_mem_nhds he0))
  set δ : ℝ := ε0 / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have heδ : e δ < b := hball (by rw [Real.dist_eq, sub_zero, abs_of_pos hδ]; linarith)
  -- Lemma 2 for each changed arm
  have hL2 : ∀ j ∈ S, 0 < (dP P (banditArmMean ν' j) (banditOptimalMean ν')).toReal ∧
      (∀ δ : ℝ, 0 < δ → Tendsto (fun T : ℕ => banditMeasure ν' π T
        {h | δ < |(armPullCount j h : ℝ) / Real.log T -
          1 / (dP P (banditArmMean ν' j) (banditOptimalMean ν')).toReal|}) atTop (𝓝 0)) ∧
      (∀ m : ℕ, Tendsto (fun T : ℕ => banditMeasure ν' π T {h | armPullCount j h ≤ m})
        atTop (𝓝 0)) := fun j hj =>
    lemma2 P hP π hπ ν' hν' hd' j (hgap' j (hjk j hj)) ⟨μ j, hmem j, by rw [hopt']; exact hjS j hj⟩
  -- log-likelihood ratios
  set ρ : Fin K → ℝ → ℝ≥0∞ := fun j => (ν.P j).rnDeriv (ν'.P j) with hρ
  set φ : Fin K → ℝ → ℝ := fun j x => Real.log (ρ j x).toReal with hφ
  have hφm : ∀ j, Measurable (φ j) := fun j =>
    Real.measurable_log.comp (ENNReal.measurable_toReal.comp (Measure.measurable_rnDeriv _ _))
  have hPj : ∀ j, ν.P j = expFam P (μ j) := fun j => (model_eq P hν j).2
  have hP'j : ∀ j, ν'.P j = expFam P (banditArmMean ν' j) := fun j => (model_eq P hν' j).2
  have hac : ∀ j, ν'.P j ≪ ν.P j := by
    intro j
    rw [hPj, hP'j]
    exact tilt_ac_tilt (theta_spec (hmem j)).1
  have hKL : ∀ j, InformationTheory.klDiv (ν'.P j) (ν.P j) = dP P (banditArmMean ν' j) (μ j) := by
    intro j; rw [hPj, hP'j]; rfl
  have hKLfin : ∀ j, InformationTheory.klDiv (ν'.P j) (ν.P j) ≠ ⊤ := by
    intro j; rw [hKL, dP_eq_Kr (hmem' j) (hmem j)]; exact ENNReal.ofReal_ne_top
  have hllr : ∀ j, Integrable (llr (ν'.P j) (ν.P j)) (ν'.P j) := fun j =>
    (InformationTheory.klDiv_ne_top_iff.1 (hKLfin j)).2
  have hφeq : ∀ j, φ j =ᵐ[ν'.P j] fun x => -(llr (ν'.P j) (ν.P j) x) := by
    intro j
    filter_upwards [Measure.inv_rnDeriv (hac j)] with x hx
    simp only [hφ, hρ, llr_def]
    rw [← hx, Pi.inv_apply, ENNReal.toReal_inv, Real.log_inv]
  have hφint : ∀ j, Integrable (φ j) (ν'.P j) := fun j => (hllr j).neg.congr (hφeq j).symm
  have hφmean : ∀ j, ∫ y, φ j y ∂(ν'.P j) = -κ j := by
    intro j
    rw [integral_congr_ae (hφeq j), integral_neg,
      ← InformationTheory.toReal_klDiv_of_measure_eq (hac j) (by simp), hKL]
  have hW : ∀ j ∈ S, Tendsto (fun T : ℕ => banditMeasure ν' π T
      {h | δ < |(∑ t ∈ Finset.univ.filter (fun t : Fin T => (h t).1 = j), φ j (h t).2) /
          (armPullCount j h : ℝ) - -κ j|}) atTop (𝓝 0) := by
    intro j hj
    have := FragileBandit.CauchyTail.random_index_wlln ν' π j (φ j) (hφm j) (hφint j)
      (hL2 j hj).2.2 δ hδ
    rwa [hφmean j] at this
  have hD : ∀ j ∈ S, Tendsto (fun T : ℕ => banditMeasure ν' π T
      {h | δ < |(armPullCount j h : ℝ) / Real.log T - cS j|}) atTop (𝓝 0) := by
    intro j hj
    have := (hL2 j hj).2.1 δ hδ
    rwa [hopt'] at this
  -- null sets of bad rewards
  set Null : Fin K → Set ℝ := fun j => {x | ρ j x = 0} ∪ {x | ρ j x = ⊤} with hNull
  have hNullm : ∀ j, MeasurableSet (Null j) := fun j =>
    (measurableSet_eq_fun (Measure.measurable_rnDeriv _ _) measurable_const).union
      (measurableSet_eq_fun (Measure.measurable_rnDeriv _ _) measurable_const)
  have hNull0 : ∀ j, (ν'.P j) (Null j) = 0 := by
    intro j
    have h1 : ∀ᵐ x ∂(ν'.P j), 0 < ρ j x := Measure.rnDeriv_pos' (hac j)
    have h2 : ∀ᵐ x ∂(ν'.P j), ρ j x < ⊤ := Measure.rnDeriv_lt_top (ν.P j) (ν'.P j)
    have : ∀ᵐ x ∂(ν'.P j), x ∉ Null j := by
      filter_upwards [h1, h2] with x hx1 hx2
      simp only [hNull, Set.mem_union, Set.mem_ofPred_eq, not_or]
      exact ⟨hx1.ne', hx2.ne⟩
    exact measure_mono_null (fun x hx => not_not.2 hx) (ae_iff.1 this)
  -- Markov bounds for all arms other than `k`
  have hMk : ∀ j, j ≠ k → Tendsto (fun T : ℕ => banditMeasure ν' π T
      {h | γ / K * (T : ℝ) < (armPullCount j h : ℝ)}) atTop (𝓝 0) := by
    intro j hj
    have hm := FragileBandit.CauchyTail.markov_tail_bound P hP π hπ ν' hν' hd' j (hgap' j hj) 1
      ⟨one_pos, le_rfl⟩ (γ / K) (by positivity) (1 / 2) (by norm_num)
    have hlim : Tendsto (fun T : ℕ => ENNReal.ofReal (((T : ℝ) ^ (1 : ℝ)) ^ (-(1 / 2 : ℝ))))
        atTop (𝓝 0) := by
      have h1 := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
        tendsto_natCast_atTop_atTop
      rw [← ENNReal.ofReal_zero]
      refine ENNReal.tendsto_ofReal (h1.congr (fun T => ?_))
      simp [Real.rpow_one]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall (fun _ => bot_le)) ?_
    filter_upwards [hm] with T hT
    simpa [Real.rpow_one] using hT
  -- the bad-event probability tends to zero
  set u : ℕ → ℝ≥0∞ := fun T =>
    (∑ j ∈ Finset.univ.erase k, banditMeasure ν' π T {h | γ / K * (T : ℝ) < (armPullCount j h : ℝ)}) +
    ∑ j ∈ S, (banditMeasure ν' π T {h | δ < |(armPullCount j h : ℝ) / Real.log T - cS j|} +
      banditMeasure ν' π T {h | δ < |(∑ t ∈ Finset.univ.filter (fun t : Fin T => (h t).1 = j),
        φ j (h t).2) / (armPullCount j h : ℝ) - -κ j|}) with hu
  have hu0 : Tendsto u atTop (𝓝 0) := by
    have h1 : Tendsto (fun T : ℕ => ∑ j ∈ Finset.univ.erase k,
        banditMeasure ν' π T {h | γ / K * (T : ℝ) < (armPullCount j h : ℝ)}) atTop (𝓝 0) := by
      rw [show (0 : ℝ≥0∞) = ∑ j ∈ Finset.univ.erase k, (0 : ℝ≥0∞) by simp]
      exact tendsto_finsetSum _ (fun j hj => hMk j (Finset.ne_of_mem_erase hj))
    have h2 : Tendsto (fun T : ℕ => ∑ j ∈ S, (banditMeasure ν' π T
        {h | δ < |(armPullCount j h : ℝ) / Real.log T - cS j|} +
        banditMeasure ν' π T {h | δ < |(∑ t ∈ Finset.univ.filter (fun t : Fin T => (h t).1 = j),
          φ j (h t).2) / (armPullCount j h : ℝ) - -κ j|})) atTop (𝓝 0) := by
      rw [show (0 : ℝ≥0∞) = ∑ j ∈ S, ((0 : ℝ≥0∞) + 0) by simp]
      exact tendsto_finsetSum _ (fun j hj => (hD j hj).add (hW j hj))
    have := h1.add h2
    rw [add_zero] at this
    exact this
  have hev1 := (tendsto_order.1 hu0).2 (1 / 2) (by norm_num)
  have hpow : Tendsto (fun T : ℕ => (T : ℝ) ^ (a - b)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hev1, hpow.eventually (eventually_ge_atTop 2), eventually_ge_atTop 2]
    with T hTu hTpow hT2
  have hT2' : (2 : ℝ) ≤ T := by exact_mod_cast hT2
  have hTpos : (0 : ℝ) < T := by linarith
  have hlogT : 0 < Real.log T := Real.log_pos (by linarith)
  -- the events
  set Mset : Fin K → Set (BanditHistory K T) :=
    fun j => {h | γ / K * (T : ℝ) < (armPullCount j h : ℝ)} with hMset
  set Dset : Fin K → Set (BanditHistory K T) :=
    fun j => {h | δ < |(armPullCount j h : ℝ) / Real.log T - cS j|} with hDset
  set Wset : Fin K → Set (BanditHistory K T) :=
    fun j => {h | δ < |(∑ t ∈ Finset.univ.filter (fun t : Fin T => (h t).1 = j),
        φ j (h t).2) / (armPullCount j h : ℝ) - -κ j|} with hWset
  set Gset : Fin K → Set (BanditHistory K T) :=
    fun j => {h | ∀ t, (h t).1 = j → (h t).2 ∉ Null j} with hGset
  set H : Set (BanditHistory K T) := (⋂ j ∈ Finset.univ.erase k, (Mset j)ᶜ) ∩
    ⋂ j ∈ S, ((Dset j)ᶜ ∩ (Wset j)ᶜ ∩ Gset j) with hH
  have hNm : ∀ j, Measurable (fun h : BanditHistory K T => (armPullCount j h : ℝ)) := fun j =>
    (measurable_from_nat (f := fun n : ℕ => (n : ℝ))).comp (measurable_armPullCount j)
  have hMm : ∀ j, MeasurableSet (Mset j) := fun j =>
    measurable_armPullCount j (t := {n : ℕ | γ / K * (T : ℝ) < (n : ℝ)}) MeasurableSet.of_discrete
  have hDm : ∀ j, MeasurableSet (Dset j) := fun j =>
    measurableSet_lt measurable_const ((((hNm j).div_const _).sub measurable_const).abs)
  have hWm : ∀ j, MeasurableSet (Wset j) := fun j =>
    measurableSet_lt measurable_const
      ((((measurable_rewardSum (T := T) j (hφm j)).div (hNm j)).sub measurable_const).abs)
  have hGm : ∀ j, MeasurableSet (Gset j) := by
    intro j
    have : Gset j = ⋂ t : Fin T, ({h : BanditHistory K T | (h t).1 = j}ᶜ ∪
        {h | (h t).2 ∉ Null j}) := by
      ext h; simp only [hGset, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_union, Set.mem_compl_iff]
      constructor
      · intro hh t; by_cases ht : (h t).1 = j
        · exact Or.inr (hh t ht)
        · exact Or.inl ht
      · intro hh t ht; rcases hh t with h1 | h1
        · exact absurd ht h1
        · exact h1
    rw [this]
    refine MeasurableSet.iInter (fun t => ?_)
    refine MeasurableSet.union (MeasurableSet.compl ?_) ?_
    · exact (measurable_fst.comp (measurable_pi_apply t)) (MeasurableSet.singleton j)
    · exact ((measurable_snd.comp (measurable_pi_apply t)) (hNullm j)).compl
  have hHm : MeasurableSet H := by
    refine MeasurableSet.inter ?_ ?_
    · exact MeasurableSet.biInter (Finset.countable_toSet _) (fun j _ => (hMm j).compl)
    · exact MeasurableSet.biInter (Finset.countable_toSet _)
        (fun j _ => ((hDm j).compl.inter (hWm j).compl).inter (hGm j))
  have hG0 : ∀ j, banditMeasure ν' π T (Gset j)ᶜ = 0 := by
    intro j
    refine le_antisymm ?_ bot_le
    calc banditMeasure ν' π T (Gset j)ᶜ ≤ banditMeasure ν' π T
          {h | ∃ t, (h t).1 = j ∧ cntBefore j h t < T + 1 ∧ (h t).2 ∈ Null j} := by
          apply measure_mono
          intro h hh
          simp only [hGset, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_not] at hh
          obtain ⟨t, ht, hn⟩ := hh
          exact ⟨t, ht, Nat.lt_succ_of_le (cntBefore_le j h t), hn⟩
      _ ≤ (T + 1 : ℕ) * ν'.P j (Null j) := first_plays_bound ν' π j (T + 1) (hNullm j) T
      _ = 0 := by rw [hNull0 j, mul_zero]
  -- `P_ν'(H) ≥ 1/2`
  have hHc : banditMeasure ν' π T Hᶜ ≤ u T := by
    have hsub : Hᶜ ⊆ (⋃ j ∈ Finset.univ.erase k, Mset j) ∪
        ((⋃ j ∈ S, (Dset j ∪ Wset j)) ∪ ⋃ j ∈ S, (Gset j)ᶜ) := by
      intro h hh
      simp only [hH, Set.compl_inter, Set.compl_iInter, Set.mem_union, Set.mem_iUnion,
        compl_compl] at hh
      rcases hh with ⟨j, hj, hmj⟩ | ⟨j, hj, hh⟩
      · exact Or.inl (Set.mem_biUnion hj hmj)
      · rcases hh with (h1 | h1) | h1
        · exact Or.inr (Or.inl (Set.mem_biUnion hj (Or.inl h1)))
        · exact Or.inr (Or.inl (Set.mem_biUnion hj (Or.inr h1)))
        · exact Or.inr (Or.inr (Set.mem_biUnion hj h1))
    calc banditMeasure ν' π T Hᶜ ≤ banditMeasure ν' π T ((⋃ j ∈ Finset.univ.erase k, Mset j) ∪
          ((⋃ j ∈ S, (Dset j ∪ Wset j)) ∪ ⋃ j ∈ S, (Gset j)ᶜ)) := measure_mono hsub
      _ ≤ banditMeasure ν' π T (⋃ j ∈ Finset.univ.erase k, Mset j) +
          (banditMeasure ν' π T (⋃ j ∈ S, (Dset j ∪ Wset j)) +
            banditMeasure ν' π T (⋃ j ∈ S, (Gset j)ᶜ)) :=
          (measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _))
      _ ≤ (∑ j ∈ Finset.univ.erase k, banditMeasure ν' π T (Mset j)) +
          ((∑ j ∈ S, banditMeasure ν' π T (Dset j ∪ Wset j)) +
            ∑ j ∈ S, banditMeasure ν' π T (Gset j)ᶜ) := by
          gcongr
          · exact measure_biUnion_finset_le _ _
          · exact measure_biUnion_finset_le _ _
          · exact measure_biUnion_finset_le _ _
      _ ≤ u T := by
          simp only [hG0, Finset.sum_const_zero, add_zero, hu]
          gcongr with j hj
          exact measure_union_le _ _
  have hHhalf : 1 / 2 ≤ banditMeasure ν' π T H := by
    by_contra hcon
    push Not at hcon
    have h1 : banditMeasure ν' π T H + banditMeasure ν' π T Hᶜ = 1 := by
      rw [measure_add_measure_compl hHm, measure_univ]
    have h2 : banditMeasure ν' π T H + banditMeasure ν' π T Hᶜ < 1 / 2 + 1 / 2 :=
      ENNReal.add_lt_add hcon (lt_of_le_of_lt hHc hTu)
    rw [ENNReal.add_halves, h1] at h2
    exact lt_irrefl _ h2
  -- `H` forces many plays of arm `k`
  have hHE : H ⊆ {h | (1 - γ) * (T : ℝ) < (armPullCount k h : ℝ)} := by
    intro h hh
    have hM : ∀ j ∈ Finset.univ.erase k, (armPullCount j h : ℝ) ≤ γ / K * T := by
      intro j hj
      have := (Set.mem_iInter₂.1 hh.1) j hj
      simp only [hMset, Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt] at this
      exact this
    have hsum := sum_pulls h
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)] at hsum
    have hsumR : (armPullCount k h : ℝ) + ∑ j ∈ Finset.univ.erase k, (armPullCount j h : ℝ) = T := by
      exact_mod_cast hsum
    have hle2 : (∑ j ∈ Finset.univ.erase k, (armPullCount j h : ℝ)) ≤
        ∑ _j ∈ Finset.univ.erase k, γ / K * (T : ℝ) := Finset.sum_le_sum hM
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at hle2
    have hK1 : ((K - 1 : ℕ) : ℝ) = (K : ℝ) - 1 := by
      rw [Nat.cast_sub (Fin.pos k)]; simp
    rw [hK1] at hle2
    have h3 : ((K : ℝ) - 1) * (γ / K * T) = γ * T - γ / K * T := by field_simp
    rw [h3] at hle2
    show (1 - γ) * (T : ℝ) < (armPullCount k h : ℝ)
    have : 0 < γ / K * T := by positivity
    nlinarith
  -- lower bound on the likelihood ratio over `H`
  have hlow : ENNReal.ofReal ((T : ℝ) ^ (-b)) * banditMeasure ν' π T H ≤
      ∫⁻ h in H, ∏ t : Fin T,
        (if (h t).1 ∈ S then (ν.P (h t).1).rnDeriv (ν'.P (h t).1) (h t).2 else 1)
        ∂(banditMeasure ν' π T) := by
    rw [← setLIntegral_const]
    apply setLIntegral_mono' hHm
    intro h hh
    have hhS : ∀ j ∈ S, h ∈ (Dset j)ᶜ ∩ (Wset j)ᶜ ∩ Gset j := fun j hj =>
      (Set.mem_iInter₂.1 hh.2) j hj
    have hprod : (∏ t : Fin T,
        (if (h t).1 ∈ S then (ν.P (h t).1).rnDeriv (ν'.P (h t).1) (h t).2 else 1)) =
        ENNReal.ofReal (Real.exp (∑ t : Fin T,
          if (h t).1 ∈ S then φ (h t).1 (h t).2 else 0)) := by
      rw [Real.exp_sum, ENNReal.ofReal_prod_of_nonneg (fun t _ => (Real.exp_pos _).le)]
      apply Finset.prod_congr rfl
      intro t _
      by_cases ht : (h t).1 ∈ S
      · rw [if_pos ht, if_pos ht]
        have hng := (hhS _ ht).2 t rfl
        simp only [hNull, Set.mem_union, Set.mem_ofPred_eq, not_or] at hng
        have hpos : 0 < (ρ (h t).1 (h t).2).toReal := ENNReal.toReal_pos hng.1 hng.2
        simp only [hφ]
        rw [Real.exp_log hpos, ENNReal.ofReal_toReal hng.2]
      · rw [if_neg ht, if_neg ht, Real.exp_zero, ENNReal.ofReal_one]
    rw [hprod]
    apply ENNReal.ofReal_le_ofReal
    rw [Real.rpow_def_of_pos hTpos]
    apply Real.exp_le_exp.2
    -- regroup the sum by arms
    have hregroup : (∑ t : Fin T, if (h t).1 ∈ S then φ (h t).1 (h t).2 else 0) =
        ∑ j ∈ S, ∑ t ∈ Finset.univ.filter (fun t : Fin T => (h t).1 = j), φ j (h t).2 := by
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t _
      rw [Finset.sum_ite_eq]
    rw [hregroup]
    have hj_bound : ∀ j ∈ S, -((κ j + δ) * (cS j + δ)) * Real.log T ≤
        ∑ t ∈ Finset.univ.filter (fun t : Fin T => (h t).1 = j), φ j (h t).2 := by
      intro j hj
      obtain ⟨⟨hDj, hWj⟩, _⟩ := hhS j hj
      simp only [hDset, hWset, Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt] at hDj hWj
      set Sj := ∑ t ∈ Finset.univ.filter (fun t : Fin T => (h t).1 = j), φ j (h t).2 with hSj
      set N : ℝ := (armPullCount j h : ℝ) with hN
      have hN0 : 0 ≤ N := Nat.cast_nonneg _
      have hNle : N ≤ (cS j + δ) * Real.log T := by
        have := (abs_le.1 hDj).2
        have h' : N / Real.log T ≤ cS j + δ := by linarith
        rwa [div_le_iff₀ hlogT] at h'
      have hS1 : -(κ j + δ) * N ≤ Sj := by
        by_cases hNz : N = 0
        · have hcard : armPullCount j h = 0 := by
            have h0 : (armPullCount j h : ℝ) = 0 := hNz
            exact_mod_cast h0
          have hempty : Finset.univ.filter (fun t : Fin T => (h t).1 = j) = ∅ := by
            unfold armPullCount at hcard
            rw [Set.toFinset_ofPred] at hcard
            exact Finset.card_eq_zero.1 (by convert hcard)
          rw [hSj, hempty, Finset.sum_empty, hNz, mul_zero]
        · have hNpos : 0 < N := lt_of_le_of_ne hN0 (Ne.symm hNz)
          have h1 := (abs_le.1 hWj).1
          have h2 : -(κ j + δ) ≤ Sj / N := by linarith
          rw [le_div_iff₀ hNpos] at h2
          linarith
      have hk0 : 0 ≤ κ j + δ := by linarith [hκ0 j]
      have : -(κ j + δ) * ((cS j + δ) * Real.log T) ≤ -(κ j + δ) * N :=
        mul_le_mul_of_nonpos_left hNle (by linarith)
      linarith
    have hsum := Finset.sum_le_sum hj_bound
    have hsum' : ∑ j ∈ S, -((κ j + δ) * (cS j + δ)) * Real.log T = -(e δ * Real.log T) := by
      rw [← Finset.sum_mul, Finset.sum_neg_distrib]; simp only [he]; ring
    rw [hsum'] at hsum
    have : -(b * Real.log T) ≤ -(e δ * Real.log T) := by
      have := mul_le_mul_of_nonneg_right heδ.le hlogT.le
      linarith
    have hfin : Real.log T * -b = -(b * Real.log T) := by ring
    rw [hfin]
    linarith
  have hcom := (FragileBandit.CauchyTail.change_of_measure π ν ν' S
    (fun j hj => (hS' j (by simpa [hSdef] using hj)).symm) T H hHm).1
  -- conclusion
  have hfinal : (T : ℝ) ^ (-a) ≤ (T : ℝ) ^ (-b) * (1 / 2) := by
    have hsplit : (T : ℝ) ^ (-b) = (T : ℝ) ^ (a - b) * (T : ℝ) ^ (-a) := by
      rw [← Real.rpow_add hTpos]; congr 1; ring
    rw [hsplit]
    have hpos : 0 < (T : ℝ) ^ (-a) := Real.rpow_pos_of_pos hTpos _
    nlinarith
  calc ENNReal.ofReal ((T : ℝ) ^ (-a)) ≤ ENNReal.ofReal ((T : ℝ) ^ (-b) * (1 / 2)) :=
        ENNReal.ofReal_le_ofReal hfinal
    _ = ENNReal.ofReal ((T : ℝ) ^ (-b)) * (1 / 2) := by
        rw [ENNReal.ofReal_mul (Real.rpow_pos_of_pos hTpos _).le]
        congr 1
        rw [ENNReal.ofReal_div_of_pos (by norm_num)]
        simp
    _ ≤ ENNReal.ofReal ((T : ℝ) ^ (-b)) * banditMeasure ν' π T H := by gcongr
    _ ≤ _ := hlow
    _ ≤ banditMeasure ν π T H := hcom
    _ ≤ _ := measure_mono hHE
end CTE47

open CTExpFam CTE47Aux CTE47 in
theorem solution {K : ℕ} (P : Measure ℝ) [IsProbabilityMeasure P]
    (hP : (0 : ℝ) ∈ interior (natParamSet P)) (π : BanditPolicy K) (hπ : IsOptimized P π)
    (ν : StochasticBandit K) (hν : IsModelEnv P ν) (hd : DistinctMeans ν) (k : Fin K)
    (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ a : ℝ, tailExponent P ν k < ENNReal.ofReal a → ∀ᶠ T : ℕ in atTop,
      ENNReal.ofReal ((T : ℝ) ^ (-a)) ≤
        banditMeasure ν π T {h | (1 - γ) * (T : ℝ) < (armPullCount k h : ℝ)} := by
  classical
  intro a ha
  set μ := banditArmMean ν with hμdef
  set S := Finset.univ.filter (fun j => μ k < μ j) with hSdef
  have hte_ne : tailExponent P ν k ≠ ⊤ := ne_top_of_lt ha
  set t : ℝ := (tailExponent P ν k).toReal with htdef
  have ht0 : 0 ≤ t := ENNReal.toReal_nonneg
  have hta : t < a := by
    have h1 : ENNReal.ofReal t < ENNReal.ofReal a := by rw [htdef, ENNReal.ofReal_toReal hte_ne]; exact ha
    exact (ENNReal.ofReal_lt_ofReal_iff'.1 h1).1
  have hr_ne : ∀ j ∈ S, tailRatio P (μ j) (μ k) ≠ ⊤ := by
    intro j hj
    apply ne_top_of_le_ne_top hte_ne
    unfold tailExponent
    exact Finset.single_le_sum (f := fun j => tailRatio P (banditArmMean ν j) (banditArmMean ν k))
      (fun _ _ => bot_le) hj
  have hsum_t : ∑ j ∈ S, (tailRatio P (μ j) (μ k)).toReal = t := by
    rw [htdef]; unfold tailExponent; rw [ENNReal.toReal_sum hr_ne]
  set η : ℝ := (a - t) / (4 * ((S.card : ℝ) + 1)) with hηdef
  have hη : 0 < η := by rw [hηdef]; apply div_pos <;> [linarith; positivity]
  have hmem : ∀ j, μ j ∈ meanSet P := fun j => (model_eq P hν j).1
  have hjS : ∀ j ∈ S, μ k < μ j := fun j hj => (Finset.mem_filter.1 hj).2
  obtain ⟨z, hz, hzinj⟩ := choose_distinct S (Finset.univ.image μ)
    (fun j y => y ∈ meanSet P ∧ y < μ k ∧
      dP P y (μ j) / dP P y (μ k) < ENNReal.ofReal ((tailRatio P (μ j) (μ k)).toReal + η))
    (by
      intro j hj F
      have hlt : tailRatio P (μ j) (μ k) <
          ENNReal.ofReal ((tailRatio P (μ j) (μ k)).toReal + η) := by
        calc tailRatio P (μ j) (μ k) = ENNReal.ofReal ((tailRatio P (μ j) (μ k)).toReal) :=
              (ENNReal.ofReal_toReal (hr_ne j hj)).symm
          _ < _ := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith)
      obtain ⟨y, hy, hyk, hyF, hrat⟩ := perturb (μ j) (μ k) (hmem j) (hmem k) (hjS j hj) F _ hlt
      exact ⟨y, hyF, hy, hyk, hrat⟩)
  have hzS : ∀ j ∈ S, z j ∈ meanSet P := fun j hj => (hz j hj).1.1
  set ν' := altEnv P ν S z hzS with hν'def
  have hmean' : ∀ j, banditArmMean ν' j = if j ∈ S then z j else μ j :=
    altEnv_mean P ν S z hzS
  have hkS : k ∉ S := by simp [hSdef]
  have hν' : IsModelEnv P ν' := by
    intro j
    by_cases hj : j ∈ S
    · rw [hν'def, altEnv_P_mem P ν S z hzS hj]; exact ⟨z j, hzS j hj, rfl⟩
    · rw [hν'def, altEnv_P_not_mem P ν S z hzS hj]; exact hν j
  have hd' : DistinctMeans ν' := by
    intro i i' h
    rw [hmean', hmean'] at h
    by_cases hi : i ∈ S <;> by_cases hi' : i' ∈ S
    · simp only [hi, hi', if_true] at h; exact hzinj hi hi' h
    · simp only [hi, hi', if_true, if_false] at h
      exact absurd (Finset.mem_image.2 ⟨i', Finset.mem_univ _, h.symm⟩) (hz i hi).2
    · simp only [hi, hi', if_true, if_false] at h
      exact absurd (Finset.mem_image.2 ⟨i, Finset.mem_univ _, h⟩) (hz i' hi').2
    · simp only [hi, hi', if_false] at h; exact hd h
  have hlt' : ∀ j, j ≠ k → banditArmMean ν' j < μ k := by
    intro j hj
    rw [hmean']
    by_cases hjs : j ∈ S
    · rw [if_pos hjs]; exact (hz j hjs).1.2.1
    · rw [if_neg hjs]
      have h1 : ¬ (μ k < μ j) := by simpa [hSdef] using hjs
      have h2 : μ j ≠ μ k := fun h => hj (hd h)
      exact lt_of_le_of_ne (not_lt.1 h1) h2
  have hk' : banditArmMean ν' k = μ k := by rw [hmean', if_neg hkS]
  have hopt' : banditOptimalMean ν' = μ k := by
    haveI : Nonempty (Fin K) := ⟨k⟩
    apply le_antisymm
    · apply ciSup_le
      intro j
      by_cases hj : j = k
      · rw [hj, hk']
      · exact (hlt' j hj).le
    · rw [← hk']; exact le_ciSup (Set.finite_range _).bddAbove k
  have hS' : ∀ j, ¬ (μ k < μ j) → ν'.P j = ν.P j := by
    intro j hj
    have : j ∉ S := by simpa [hSdef] using hj
    rw [hν'def, altEnv_P_not_mem P ν S z hzS this]
  set b : ℝ := (t + a) / 2 with hbdef
  have hb : ∑ j ∈ S, (dP P (banditArmMean ν' j) (μ j)).toReal *
      (1 / (dP P (banditArmMean ν' j) (μ k)).toReal) < b := by
    have hterm : ∀ j ∈ S, (dP P (banditArmMean ν' j) (μ j)).toReal *
        (1 / (dP P (banditArmMean ν' j) (μ k)).toReal) ≤ (tailRatio P (μ j) (μ k)).toReal + η := by
      intro j hj
      rw [hmean', if_pos hj]
      obtain ⟨⟨hzm, hzk, hrat⟩, _⟩ := hz j hj
      obtain ⟨hdpos, hdtop⟩ := dP_pos_fin P hzm (hmem k) hzk.ne
      have hκtop : dP P (z j) (μ j) ≠ ⊤ := by rw [dP_eq_Kr hzm (hmem j)]; exact ENNReal.ofReal_ne_top
      have heq : dP P (z j) (μ j) / dP P (z j) (μ k) =
          ENNReal.ofReal ((dP P (z j) (μ j)).toReal * (1 / (dP P (z j) (μ k)).toReal)) := by
        rw [← ENNReal.ofReal_toReal hκtop, ← ENNReal.ofReal_toReal hdtop,
          ← ENNReal.ofReal_div_of_pos hdpos]
        congr 1
        rw [ENNReal.toReal_ofReal ENNReal.toReal_nonneg, ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
        ring
      rw [heq] at hrat
      have hnn : 0 ≤ (dP P (z j) (μ j)).toReal * (1 / (dP P (z j) (μ k)).toReal) := by positivity
      exact ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hnn).1 hrat).le
    calc _ ≤ ∑ j ∈ S, ((tailRatio P (μ j) (μ k)).toReal + η) := Finset.sum_le_sum hterm
      _ = t + S.card * η := by rw [Finset.sum_add_distrib, hsum_t, Finset.sum_const, nsmul_eq_mul]
      _ < b := by
          have h1 : (S.card : ℝ) * η < (a - t) / 4 := by
            rw [hηdef]
            have hc0 : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
            rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
            nlinarith
          rw [hbdef]; linarith
  exact fixedAlt P hP π hπ ν hν hd k γ hγ ν' hν' hd' hS' hopt' hlt' b hb a (by rw [hbdef]; linarith)
