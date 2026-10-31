-- Prove2me | solution 1 for ExplodingOffer.Mrl.eq_5_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T23:18:56.843223+00:00
-- url     : https://prove2.me/submissions/d616bcc0-6a1b-41e4-942c-27033bc23fb0

import Mathlib
import Definitions.Def_ExplodingOffer_Mrl_Model
import Theorems.Thm_ExplodingOffer_Mrl_tval_bijection

open MeasureTheory
open ExplodingOffer.Mrl

namespace Eq56Aux

variable {μ : Measure ℝ} {a : ℝ} {b : EReal}

lemma intL (hμ : OfferDist μ a b) (v : ℝ) : Integrable (fun x : ℝ => max (x - v) 0) μ := by
  haveI := hμ.isProb
  exact (hμ.integrable.sub (integrable_const v)).pos_part

lemma L_le_add (hμ : OfferDist μ a b) (v w : ℝ) : Lfun μ v ≤ Lfun μ w + dist v w := by
  haveI := hμ.isProb
  have h : ∀ x : ℝ, max (x - v) 0 ≤ max (x - w) 0 + dist v w := by
    intro x
    rw [Real.dist_eq]
    have := le_abs_self (v - w); have := neg_abs_le (v - w)
    rcases le_total (x - v) 0 with h1 | h1 <;> rcases le_total (x - w) 0 with h2 | h2
    · rw [max_eq_right h1, max_eq_right h2]; positivity
    · rw [max_eq_right h1, max_eq_left h2]; linarith [abs_nonneg (v - w)]
    · rw [max_eq_left h1, max_eq_right h2]; linarith
    · rw [max_eq_left h1, max_eq_left h2]; linarith
  have := integral_mono (μ := μ) (f := fun x => max (x - v) 0)
    (g := fun x => max (x - w) 0 + dist v w) (intL hμ v)
    ((intL hμ w).add (integrable_const (dist v w))) h
  rw [integral_add (intL hμ w) (integrable_const _)] at this
  simpa [Lfun] using this

lemma L_cont (hμ : OfferDist μ a b) : Continuous (Lfun μ) :=
  (LipschitzWith.of_le_add (L_le_add hμ)).continuous

lemma L_anti (hμ : OfferDist μ a b) : Antitone (Lfun μ) := by
  intro v w hvw
  apply integral_mono (intL hμ w) (intL hμ v)
  intro x
  exact max_le_max (by linarith) le_rfl

lemma Ioi_pos (hμ : OfferDist μ a b) (v : ℝ) (hv : (v : EReal) < b) : 0 < μ (Set.Ioi v) := by
  haveI := hμ.isProb
  rcases lt_or_ge v a with hva | hav
  · have h1 : μ (Set.Ici a) = 1 := by
      have := prob_compl_eq_one_sub (μ := μ) (s := Set.Iio a) measurableSet_Iio
      rw [Set.compl_Iio, hμ.below] at this; simpa using this
    have : Set.Ici a ⊆ Set.Ioi v := fun x hx => lt_of_lt_of_le hva hx
    have := measure_mono (μ := μ) this
    rw [h1] at this
    exact lt_of_lt_of_le one_pos this
  · obtain ⟨y, hvy, hyb⟩ : ∃ y : ℝ, v < y ∧ (y : EReal) ≤ b := by
      induction b using EReal.rec with
      | bot => exact absurd hv (by simp)
      | top => exact ⟨v + 1, by linarith, le_top⟩
      | coe r =>
        have hr : v < r := EReal.coe_lt_coe_iff.mp hv
        exact ⟨r, hr, le_rfl⟩
    exact lt_of_lt_of_le (hμ.noGap v y hav hvy hyb) (measure_mono Set.Ioo_subset_Ioi_self)

lemma L_pos (hμ : OfferDist μ a b) (v : ℝ) (hv : (v : EReal) < b) : 0 < Lfun μ v := by
  unfold Lfun
  refine (integral_pos_iff_support_of_nonneg (f := fun x : ℝ => max (x - v) 0)
      (fun x => le_max_right _ _) (intL hμ v)).mpr ?_
  have : Set.Ioi v ⊆ Function.support (fun x : ℝ => max (x - v) 0) := by
    intro x hx
    simp only [Function.mem_support]
    rw [max_eq_left (by linarith [Set.mem_Ioi.mp hx])]
    linarith [Set.mem_Ioi.mp hx]
  exact lt_of_lt_of_le (Ioi_pos hμ v hv) (measure_mono this)


lemma lip_pt (x : ℝ) : LipschitzWith 1 (fun s : ℝ => max (x - s) 0) := by
  apply LipschitzWith.of_le_add
  intro v w
  rw [Real.dist_eq]
  have := le_abs_self (v - w); have := neg_abs_le (v - w)
  rcases le_total (x - v) 0 with h1 | h1 <;> rcases le_total (x - w) 0 with h2 | h2
  · rw [max_eq_right h1, max_eq_right h2]; positivity
  · rw [max_eq_right h1, max_eq_left h2]; linarith [abs_nonneg (v - w)]
  · rw [max_eq_left h1, max_eq_right h2]; linarith
  · rw [max_eq_left h1, max_eq_left h2]; linarith

lemma hasDerivAt_L (hμ : OfferDist μ a b) (t : ℝ) :
    HasDerivAt (Lfun μ) (-(μ (Set.Ioi t)).toReal) t := by
  haveI := hμ.isProb
  haveI := hμ.noAtoms
  have key := hasDerivAt_integral_of_dominated_loc_of_lip (μ := μ)
    (F := fun s x => max (x - s) 0)
    (F' := fun x => -(Set.Ioi t).indicator (1 : ℝ → ℝ) x) (x₀ := t) (s := Set.univ)
    (bound := fun _ => 1) Filter.univ_mem
    (Filter.Eventually.of_forall fun s => (intL hμ s).aestronglyMeasurable)
    (intL hμ t)
    ((aestronglyMeasurable_const.indicator measurableSet_Ioi).neg)
    (Filter.Eventually.of_forall fun x => by
      simpa using (lip_pt x).lipschitzOnWith (s := Set.univ))
    (integrable_const 1)
    (by
      have hne : ∀ᵐ x ∂μ, x ≠ t := by
        rw [ae_iff]
        have : {x : ℝ | ¬ x ≠ t} = {t} := by ext x; simp
        rw [this]; exact measure_singleton t
      filter_upwards [hne] with x hx
      rcases lt_or_gt_of_ne hx with h | h
      · have : (fun s => max (x - s) 0) =ᶠ[nhds t] fun _ => (0:ℝ) := by
          filter_upwards [Ioi_mem_nhds h] with s hs
          exact max_eq_right (by linarith [Set.mem_Ioi.mp hs])
        rw [Set.indicator_of_notMem (by simpa using h.le), neg_zero]
        exact (hasDerivAt_const t (0:ℝ)).congr_of_eventuallyEq this
      · have hev : (fun s => max (x - s) 0) =ᶠ[nhds t] fun s => x - s := by
          filter_upwards [Iio_mem_nhds h] with s hs
          exact max_eq_left (by linarith [Set.mem_Iio.mp hs])
        rw [Set.indicator_of_mem (by simpa using h)]
        have := (hasDerivAt_id t).const_sub x
        simp only [Pi.one_apply]
        exact this.congr_of_eventuallyEq hev)
  have h2 := key.2
  rw [integral_neg, integral_indicator_one measurableSet_Ioi] at h2
  have h3 : HasDerivAt (fun s => ∫ x, max (x - s) 0 ∂μ) (-(μ (Set.Ioi t)).toReal) t := by
    simpa [Measure.real_def] using h2
  exact h3

lemma Tval_hasDerivAt (hμ : OfferDist μ a b) (V : ℝ) (hV0 : 0 ≤ V) (hVb : (V : EReal) < b) :
    HasDerivAt (Tval μ) (1 / Lfun μ V) V := by
  have hLV := L_pos hμ V hVb
  have hcont : ContinuousOn (fun v => 1 / Lfun μ v) (Set.uIcc 0 V) := by
    rw [Set.uIcc_of_le hV0]
    exact ContinuousOn.div continuousOn_const (L_cont hμ).continuousOn
      (fun v hv => (lt_of_lt_of_le hLV (L_anti hμ hv.2)).ne')
  have hmeas : Measurable (fun v => 1 / Lfun μ v) :=
    measurable_const.div (L_cont hμ).measurable
  exact intervalIntegral.integral_hasDerivAt_right hcont.intervalIntegrable
    hmeas.stronglyMeasurable.stronglyMeasurableAtFilter
    (continuousAt_const.div (L_cont hμ).continuousAt hLV.ne')

lemma Fbar_anti (hμ : OfferDist μ a b) : Antitone (fun v : ℝ => (μ (Set.Ioi v)).toReal) := by
  haveI := hμ.isProb
  intro v w hvw
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.Ioi_subset_Ioi hvw))

end Eq56Aux

open Eq56Aux in
theorem solution {μ : Measure ℝ} {a : ℝ} {b : EReal} (hμ : OfferDist μ a b)
    {lam T : ℝ} (hlam : 0 < lam) (hT : 0 < T)
    {s tD : ℝ} (htD0 : 0 ≤ tD) (htDT : tD ≤ T) (hs : minAccept μ b lam T tD ≤ s)
    (hsb : (s : EReal) < b) (u : ℝ) :
    noAcceptProb μ b lam T s tD = Lfun μ (valueToGo μ b lam T s tD 0) / Lfun μ s ∧
    surplus μ b lam T u s tD =
      (u - s) * (Lfun μ (valueToGo μ b lam T s tD 0) / Lfun μ s) := by
  haveI := hμ.isProb
  haveI := hμ.noAtoms
  obtain ⟨hLpos, hmono, hinv, hleft⟩ := tval_bijection hμ
  have hs0 : 0 ≤ s := by
    have := (hinv (lam * (T - tD)) (mul_nonneg hlam.le (by linarith))).1
    unfold minAccept at hs; linarith
  set c := Tval μ s with hcdef
  have h0b : ((0:ℝ) : EReal) < b := lt_of_le_of_lt (EReal.coe_le_coe_iff.mpr hs0) hsb
  have hc0 : 0 ≤ c := by
    have := hmono.monotoneOn ⟨le_refl (0:ℝ), h0b⟩ ⟨hs0, hsb⟩ hs0
    rw [show Tval μ 0 = 0 by simp [Tval]] at this
    exact this
  set W0 := Tinv μ b (c + lam * tD) with hW0def
  obtain ⟨hW00, hW0b, hTW0⟩ := hinv (c + lam * tD) (by positivity)
  have hsW0 : s ≤ W0 := by
    by_contra h
    push Not at h
    have := hmono ⟨hW00, hW0b⟩ ⟨hs0, hsb⟩ h
    rw [hTW0] at this
    have : 0 ≤ lam * tD := by positivity
    linarith
  have hv0 : valueToGo μ b lam T s tD 0 = W0 := by
    unfold valueToGo; rw [if_pos htD0, if_pos hsb, hW0def]; congr 1; ring
  have hLs := hLpos s hs0 hsb
  have hLW0 := hLpos W0 hW00 hW0b
  -- the key identity  λ ∫₀^{t_D} P(X ≥ V(t)) dt = log ℒ(s) − log ℒ(V(0))
  have key : lam * ∫ t in (0:ℝ)..tD, (μ (Set.Ici (valueToGo μ b lam T s tD t))).toReal =
      Real.log (Lfun μ s) - Real.log (Lfun μ W0) := by
    set τ : ℝ → ℝ := fun V => tD - (Tval μ V - c) / lam with hτ
    set g : ℝ → ℝ := fun t => (μ (Set.Ici (Tinv μ b (c + lam * (tD - t))))).toReal with hg
    have hmemb : ∀ V ∈ Set.Icc s W0, 0 ≤ V ∧ (V : EReal) < b := fun V hV =>
      ⟨le_trans hs0 hV.1, lt_of_le_of_lt (EReal.coe_le_coe_iff.mpr hV.2) hW0b⟩
    have step1 : ∫ t in (0:ℝ)..tD, (μ (Set.Ici (valueToGo μ b lam T s tD t))).toReal =
        ∫ t in Set.Icc 0 tD, g t := by
      rw [intervalIntegral.integral_of_le htD0, ← integral_Icc_eq_integral_Ioc]
      apply setIntegral_congr_fun measurableSet_Icc
      intro t ht
      simp only [valueToGo, hg]
      rw [if_pos ht.2, if_pos hsb]
    have step2 : Set.Icc 0 tD = τ '' Set.Icc s W0 := by
      ext t
      constructor
      · intro ht
        set y := c + lam * (tD - t) with hy
        have hy0 : 0 ≤ y := by
          have : 0 ≤ lam * (tD - t) := mul_nonneg hlam.le (by linarith [ht.2])
          linarith
        obtain ⟨hV0, hVb, hTV⟩ := hinv y hy0
        refine ⟨Tinv μ b y, ⟨?_, ?_⟩, ?_⟩
        · by_contra h; push Not at h
          have := hmono ⟨hV0, hVb⟩ ⟨hs0, hsb⟩ h
          rw [hTV] at this
          have : 0 ≤ lam * (tD - t) := mul_nonneg hlam.le (by linarith [ht.2])
          linarith
        · by_contra h; push Not at h
          have := hmono ⟨hW00, hW0b⟩ ⟨hV0, hVb⟩ h
          rw [hTV, hTW0] at this
          have : lam * (tD - t) ≤ lam * tD := by nlinarith [ht.1]
          linarith
        · simp only [hτ]; rw [hTV, hy]; field_simp; ring
      · rintro ⟨V, hV, rfl⟩
        obtain ⟨hV0, hVb⟩ := hmemb V hV
        have h1 : c ≤ Tval μ V := hmono.monotoneOn ⟨hs0, hsb⟩ ⟨hV0, hVb⟩ hV.1
        have h2 : Tval μ V ≤ c + lam * tD := by
          rw [← hTW0]; exact hmono.monotoneOn ⟨hV0, hVb⟩ ⟨hW00, hW0b⟩ hV.2
        constructor
        · simp only [hτ]
          rw [sub_nonneg, div_le_iff₀ hlam]; linarith
        · simp only [hτ]
          have : 0 ≤ (Tval μ V - c) / lam := div_nonneg (by linarith) hlam.le
          linarith
    have hderiv : ∀ V ∈ Set.Icc s W0, HasDerivWithinAt τ (-((1 / Lfun μ V) / lam))
        (Set.Icc s W0) V := by
      intro V hV
      obtain ⟨hV0, hVb⟩ := hmemb V hV
      have := (((Tval_hasDerivAt hμ V hV0 hVb).sub_const c).div_const lam).const_sub tD
      exact this.hasDerivWithinAt
    have hinj : Set.InjOn τ (Set.Icc s W0) := by
      intro V hV V' hV' h
      simp only [hτ] at h
      have : Tval μ V = Tval μ V' := by
        field_simp at h; linarith
      exact hmono.injOn (hmemb V hV) (hmemb V' hV') this
    have step3 := integral_image_eq_integral_abs_deriv_smul measurableSet_Icc hderiv hinj g
    rw [← step2] at step3
    have step4 : ∫ V in Set.Icc s W0, |-((1 / Lfun μ V) / lam)| • g (τ V) =
        ∫ V in Set.Icc s W0, ((μ (Set.Ioi V)).toReal / Lfun μ V) / lam := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro V hV
      obtain ⟨hV0, hVb⟩ := hmemb V hV
      have hLV := hLpos V hV0 hVb
      have harg : c + lam * (tD - τ V) = Tval μ V := by
        simp only [hτ]; field_simp; ring
      simp only [hg, smul_eq_mul]
      rw [harg, hleft V hV0 hVb, measure_congr (Ioi_ae_eq_Ici (μ := μ) (a := V)).symm,
        abs_neg, abs_of_pos (by positivity)]
      field_simp
    rw [step1, step3, step4, integral_div, mul_div_cancel₀ _ hlam.ne',
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hsW0]
    -- fundamental theorem of calculus for `−log ℒ`
    have hpos : ∀ x ∈ Set.uIcc s W0, 0 < Lfun μ x := by
      intro x hx
      rw [Set.uIcc_of_le hsW0] at hx
      obtain ⟨hx0, hxb⟩ := hmemb x hx
      exact hLpos x hx0 hxb
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun x => -Real.log (Lfun μ x))
      (f' := fun x => (μ (Set.Ioi x)).toReal / Lfun μ x)
      (fun x hx => (((hasDerivAt_L hμ x).log (hpos x hx).ne').neg).congr_deriv (by ring))
      (by
        have h1 : IntervalIntegrable (fun x => (μ (Set.Ioi x)).toReal) volume s W0 :=
          ((Fbar_anti hμ).antitoneOn _).intervalIntegrable
        have h2 : ContinuousOn (fun x => 1 / Lfun μ x) (Set.uIcc s W0) :=
          ContinuousOn.div continuousOn_const (L_cont hμ).continuousOn
            (fun x hx => (hpos x hx).ne')
        have := h1.mul_continuousOn h2
        exact this.congr (fun x _ => by simp [div_eq_mul_inv]))
    rw [hFTC]
    ring
  constructor
  · unfold noAcceptProb
    rw [key, hv0, neg_sub, Real.exp_sub, Real.exp_log hLW0, Real.exp_log hLs]
  · unfold surplus noAcceptProb
    rw [key, hv0, neg_sub, Real.exp_sub, Real.exp_log hLW0, Real.exp_log hLs]
