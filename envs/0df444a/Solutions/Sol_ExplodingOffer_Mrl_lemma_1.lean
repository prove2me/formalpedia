-- Prove2me | solution 1 for ExplodingOffer.Mrl.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T23:30:06.581686+00:00
-- url     : https://prove2.me/submissions/d758554c-4cea-4d75-940d-95f233d3ae02

import Mathlib
import Definitions.Def_ExplodingOffer_Mrl_Model
import Theorems.Thm_ExplodingOffer_Mrl_tval_bijection

open MeasureTheory
open ExplodingOffer.Mrl

namespace L1Aux

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

lemma L_nonneg (t : ℝ) : 0 ≤ Lfun μ t :=
  integral_nonneg (fun x => le_max_right _ _)

lemma L_zero (hμ : OfferDist μ a b) (r : ℝ) (hb : b = (r : EReal)) (t : ℝ) (ht : r ≤ t) :
    Lfun μ t = 0 := by
  have hae : ∀ᵐ x ∂μ, max (x - t) 0 = 0 := by
    have h0 : ∀ᵐ x ∂μ, x ≤ r := by
      rw [ae_iff]
      have : {x : ℝ | ¬ x ≤ r} = {x : ℝ | b < (x : EReal)} := by
        ext x; simp [hb, not_le]
      rw [this]; exact hμ.above
    filter_upwards [h0] with x hx
    exact max_eq_right (by linarith)
  unfold Lfun
  rw [integral_congr_ae hae]
  simp

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

lemma L_lip (hμ : OfferDist μ a b) (lam : ℝ) (hlam : 0 < lam) :
    LipschitzWith (Real.toNNReal lam) (fun x => -(lam * Lfun μ x)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.coe_toNNReal _ hlam.le, Real.dist_eq, Real.dist_eq]
  have h1 := L_le_add hμ x y
  have h2 := L_le_add hμ y x
  rw [Real.dist_eq] at h1 h2
  rw [abs_sub_comm y x] at h2
  have : |Lfun μ x - Lfun μ y| ≤ |x - y| := abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
  calc |-(lam * Lfun μ x) - -(lam * Lfun μ y)| = lam * |Lfun μ x - Lfun μ y| := by
        rw [show -(lam * Lfun μ x) - -(lam * Lfun μ y) = lam * (Lfun μ y - Lfun μ x) by ring,
          abs_mul, abs_of_pos hlam, abs_sub_comm]
    _ ≤ lam * |x - y| := mul_le_mul_of_nonneg_left this hlam.le

lemma back_deriv (hμ : OfferDist μ a b) {lam : ℝ} {F : ℝ → ℝ} {p q : ℝ}
    (hF : ContinuousOn F (Set.Icc p q))
    (hF' : ∀ t ∈ Set.Ioo p q, HasDerivAt F (-(lam * Lfun μ (F t))) t) :
    ∀ t ∈ Set.Ioc p q, HasDerivWithinAt F (-(lam * Lfun μ (F t))) (Set.Iic t) t := by
  intro t ht
  rcases lt_or_eq_of_le ht.2 with htq | htq
  · exact (hF' t ⟨ht.1, htq⟩).hasDerivWithinAt
  · subst htq
    apply hasDerivWithinAt_Iic_of_tendsto_deriv (s := Set.Ioo p t)
    · intro x hx; exact (hF' x hx).differentiableAt.differentiableWithinAt
    · exact (hF t ⟨ht.1.le, le_rfl⟩).mono Set.Ioo_subset_Icc_self
    · exact Ioo_mem_nhdsLT ht.1
    · have hev : (fun x => deriv F x) =ᶠ[nhdsWithin t (Set.Iio t)]
          fun x => -(lam * Lfun μ (F x)) := by
        filter_upwards [Ioo_mem_nhdsLT ht.1] with x hx; exact (hF' x hx).deriv
      rw [Filter.tendsto_congr' hev]
      have hc : ContinuousWithinAt F (Set.Iio t) t :=
        (hF t ⟨ht.1.le, le_rfl⟩).mono_of_mem_nhdsWithin
          (Filter.mem_of_superset (Ioo_mem_nhdsLT ht.1) Set.Ioo_subset_Icc_self)
      exact (((L_cont hμ).continuousAt.comp_continuousWithinAt hc).const_mul lam).neg

lemma uniq_back (hμ : OfferDist μ a b) {lam : ℝ} (hlam : 0 < lam) {f g : ℝ → ℝ} {p q : ℝ}
    (hf : ContinuousOn f (Set.Icc p q))
    (hf' : ∀ t ∈ Set.Ioo p q, HasDerivAt f (-(lam * Lfun μ (f t))) t)
    (hg : ContinuousOn g (Set.Icc p q))
    (hg' : ∀ t ∈ Set.Ioo p q, HasDerivAt g (-(lam * Lfun μ (g t))) t)
    (hq : f q = g q) : Set.EqOn f g (Set.Icc p q) :=
  ODE_solution_unique_of_mem_Icc_left (v := fun _ x => -(lam * Lfun μ x))
    (s := fun _ => Set.univ) (K := Real.toNNReal lam)
    (fun _ _ => (L_lip hμ lam hlam).lipschitzOnWith) hf (back_deriv hμ hf hf')
    (fun _ _ => trivial) hg (back_deriv hμ hg hg') (fun _ _ => trivial) hq

lemma Tinv_strictMono (hμ : OfferDist μ a b) : StrictMonoOn (Tinv μ b) (Set.Ici 0) := by
  obtain ⟨_, hmono, hinv, _⟩ := tval_bijection hμ
  intro y hy y' hy' hyy
  obtain ⟨h0, hb, hT⟩ := hinv y hy
  obtain ⟨h0', hb', hT'⟩ := hinv y' hy'
  by_contra h
  push Not at h
  have := hmono.monotoneOn ⟨h0', hb'⟩ ⟨h0, hb⟩ h
  linarith

lemma Tinv_btw (hμ : OfferDist μ a b) (y₀ : ℝ) (hy₀ : 0 ≤ y₀) :
    ∀ B > Tinv μ b y₀, ∃ c ∈ Set.Ioi (0:ℝ), Tinv μ b c ∈ Set.Ioc (Tinv μ b y₀) B := by
  obtain ⟨_, hmono, hinv, hleft⟩ := tval_bijection hμ
  obtain ⟨h0, hb, hT⟩ := hinv y₀ hy₀
  intro B hB
  obtain ⟨t₀, ht₀1, ht₀2⟩ := EReal.lt_iff_exists_real_btwn.mp hb
  have ht₀ : Tinv μ b y₀ < t₀ := EReal.coe_lt_coe_iff.mp ht₀1
  set V := min B t₀ with hV
  have hVgt : Tinv μ b y₀ < V := lt_min hB ht₀
  have hV0 : 0 ≤ V := le_trans h0 hVgt.le
  have hVb : (V : EReal) < b := lt_of_le_of_lt (EReal.coe_le_coe_iff.mpr (min_le_right _ _)) ht₀2
  refine ⟨Tval μ V, ?_, ?_⟩
  · have := hmono ⟨h0, hb⟩ ⟨hV0, hVb⟩ hVgt
    rw [hT] at this
    exact lt_of_le_of_lt hy₀ this
  · rw [hleft V hV0 hVb]; exact ⟨hVgt, min_le_left _ _⟩

lemma Tinv_contWithin (hμ : OfferDist μ a b) (y₀ : ℝ) (hy₀ : 0 ≤ y₀) :
    ContinuousWithinAt (Tinv μ b) (Set.Ici 0) y₀ := by
  obtain ⟨_, hmono, hinv, hleft⟩ := tval_bijection hμ
  rcases lt_or_eq_of_le hy₀ with hpos | hzero
  · apply ContinuousAt.continuousWithinAt
    apply ((Tinv_strictMono hμ).mono Set.Ioi_subset_Ici_self).continuousAt_of_exists_between
      (Ioi_mem_nhds hpos)
    · intro B hB
      obtain ⟨h0, hb, hT⟩ := hinv y₀ hy₀
      have hTpos : 0 < Tinv μ b y₀ := by
        rcases lt_or_eq_of_le h0 with h | h
        · exact h
        · exfalso; rw [← h, show Tval μ 0 = 0 by simp [Tval]] at hT; linarith
      set V := max B (Tinv μ b y₀ / 2) with hV
      have hVlt : V < Tinv μ b y₀ := max_lt hB (by linarith)
      have hV0 : 0 < V := lt_of_lt_of_le (by linarith) (le_max_right _ _)
      have hVb : (V : EReal) < b := lt_trans (EReal.coe_lt_coe_iff.mpr hVlt) hb
      refine ⟨Tval μ V, ?_, ?_⟩
      · have h0b : ((0:ℝ) : EReal) < b := lt_trans (EReal.coe_lt_coe_iff.mpr hV0) hVb
        have := hmono ⟨le_rfl, h0b⟩ ⟨hV0.le, hVb⟩ hV0
        rw [show Tval μ 0 = 0 by simp [Tval]] at this
        exact this
      · rw [hleft V hV0.le hVb]; exact ⟨le_max_left _ _, hVlt⟩
    · intro B hB
      obtain ⟨c, hc, hc'⟩ := Tinv_btw hμ y₀ hy₀ B hB
      exact ⟨c, hc, hc'⟩
  · subst hzero
    apply (Tinv_strictMono hμ).continuousWithinAt_right_of_exists_between self_mem_nhdsWithin
    intro B hB
    obtain ⟨c, hc, hc'⟩ := Tinv_btw hμ 0 le_rfl B hB
    exact ⟨c, Set.mem_Ici.mpr (le_of_lt hc), hc'⟩

lemma Tinv_hasDerivAt (hμ : OfferDist μ a b) (y : ℝ) (hy : 0 < y) :
    HasDerivAt (Tinv μ b) (Lfun μ (Tinv μ b y)) y := by
  obtain ⟨hLpos, _, hinv, _⟩ := tval_bijection hμ
  obtain ⟨h0, hb, hT⟩ := hinv y hy.le
  have hc : ContinuousAt (Tinv μ b) y :=
    (Tinv_contWithin hμ y hy.le).continuousAt (Ici_mem_nhds hy)
  have hd := Tval_hasDerivAt hμ (Tinv μ b y) h0 hb
  have hL := hLpos _ h0 hb
  have := HasDerivAt.of_local_left_inverse hc hd (one_div_ne_zero hL.ne') (by
    filter_upwards [Ioi_mem_nhds hy] with z hz
    exact (hinv z (le_of_lt hz)).2.2)
  simpa [one_div, inv_inv] using this

end L1Aux

open L1Aux in
theorem solution {μ : Measure ℝ} {a : ℝ} {b : EReal} (hμ : OfferDist μ a b)
    {lam T : ℝ} (hlam : 0 < lam) (hT : 0 < T)
    {s tD : ℝ} (htD0 : 0 ≤ tD) (htDT : tD ≤ T) (hs : minAccept μ b lam T tD ≤ s) :
    IsHJB μ lam T s tD (valueToGo μ b lam T s tD) ∧
    (∀ V : ℝ → ℝ, IsHJB μ lam T s tD V →
      ∀ t ∈ Set.Icc 0 T, V t = valueToGo μ b lam T s tD t) ∧
    (minAccept μ b lam T tD : EReal) < b ∧
    (tD < T → Filter.Tendsto (valueToGo μ b lam T s tD) (nhdsWithin tD (Set.Ioi tD))
      (nhds (minAccept μ b lam T tD))) := by
  obtain ⟨hLpos, hmono, hinv, hleft⟩ := tval_bijection hμ
  have hma := hinv (lam * (T - tD)) (mul_nonneg hlam.le (by linarith))
  have hs0 : 0 ≤ s := le_trans hma.1 hs
  have h0b : ((0:ℝ) : EReal) < b :=
    lt_of_le_of_lt (EReal.coe_le_coe_iff.mpr hma.1) hma.2.1
  have hTinv0 : Tinv μ b 0 = 0 := by
    have := hleft 0 le_rfl h0b
    rwa [show Tval μ 0 = 0 by simp [Tval]] at this
  -- the piece after the deadline: `P(t) = 𝒯⁻¹(λ(T − t))`
  set P : ℝ → ℝ := fun t => Tinv μ b (lam * (T - t)) with hP
  have hPcont : ContinuousOn P (Set.Iic T) := by
    intro t ht
    have harg : 0 ≤ lam * (T - t) := mul_nonneg hlam.le (by linarith [Set.mem_Iic.mp ht])
    have hg : Continuous (fun t : ℝ => lam * (T - t)) := by fun_prop
    exact ContinuousWithinAt.comp (g := Tinv μ b) (f := fun t : ℝ => lam * (T - t))
      (t := Set.Ici 0) (Tinv_contWithin hμ _ harg) hg.continuousWithinAt
      (fun x hx => mul_nonneg hlam.le (by linarith [Set.mem_Iic.mp hx]))
  have hPderiv : ∀ t, t < T → HasDerivAt P (-(lam * Lfun μ (P t))) t := by
    intro t ht
    have hy : 0 < lam * (T - t) := mul_pos hlam (by linarith)
    have h1 := Tinv_hasDerivAt hμ _ hy
    have h2 : HasDerivAt (fun t => lam * (T - t)) (lam * (-1)) t :=
      ((hasDerivAt_id t).const_sub T).const_mul lam
    have := h1.comp t h2
    exact this.congr_deriv (by simp only [hP]; ring)
  have hVeq2 : ∀ t, tD < t → valueToGo μ b lam T s tD t = P t := by
    intro t ht; unfold valueToGo; rw [if_neg (not_le.mpr ht)]
  -- the piece before the deadline
  obtain ⟨Q, hQcont, hQderiv, hQtD, hVeq1⟩ : ∃ Q : ℝ → ℝ, ContinuousOn Q (Set.Icc 0 tD) ∧
      (∀ t, t < tD → HasDerivAt Q (-(lam * Lfun μ (Q t))) t) ∧ Q tD = s ∧
      ∀ t, t ≤ tD → valueToGo μ b lam T s tD t = Q t := by
    by_cases hsb : (s : EReal) < b
    · have hc0 : 0 ≤ Tval μ s := by
        have := hmono.monotoneOn ⟨le_rfl, h0b⟩ ⟨hs0, hsb⟩ hs0
        rwa [show Tval μ 0 = 0 by simp [Tval]] at this
      refine ⟨fun t => Tinv μ b (Tval μ s + lam * (tD - t)), ?_, ?_, ?_, ?_⟩
      · intro t ht
        have harg : 0 ≤ Tval μ s + lam * (tD - t) := by
          have := mul_nonneg hlam.le (sub_nonneg.mpr ht.2); linarith
        have hg : Continuous (fun t : ℝ => Tval μ s + lam * (tD - t)) := by fun_prop
        exact ContinuousWithinAt.comp (g := Tinv μ b)
          (f := fun t : ℝ => Tval μ s + lam * (tD - t)) (t := Set.Ici 0)
          (Tinv_contWithin hμ _ harg) hg.continuousWithinAt (fun x (hx : x ∈ Set.Icc 0 tD) => by
          have := mul_nonneg hlam.le (sub_nonneg.mpr hx.2); simp only [Set.mem_Ici]; linarith)
      · intro t ht
        have hy : 0 < Tval μ s + lam * (tD - t) := by
          have := mul_pos hlam (sub_pos.mpr ht); linarith
        have h1 := Tinv_hasDerivAt hμ _ hy
        have h2 : HasDerivAt (fun t => Tval μ s + lam * (tD - t)) (lam * (-1)) t :=
          (((hasDerivAt_id t).const_sub tD).const_mul lam).const_add _
        have := h1.comp t h2
        exact this.congr_deriv (by ring)
      · simp only [sub_self, mul_zero, add_zero]; exact hleft s hs0 hsb
      · intro t ht; unfold valueToGo; rw [if_pos ht, if_pos hsb]
    · push Not at hsb
      have hLs : Lfun μ s = 0 := by
        have htop : b ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top s) hsb
        have hbot : b ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot a) hμ.a_le_b
        have hbr : b = ((b.toReal : ℝ) : EReal) := (EReal.coe_toReal htop hbot).symm
        apply L_zero hμ b.toReal hbr s
        rw [hbr] at hsb; exact EReal.coe_le_coe_iff.mp hsb
      refine ⟨fun _ => s, continuousOn_const, ?_, rfl, ?_⟩
      · intro t _
        simp only [hLs, mul_zero, neg_zero]
        exact hasDerivAt_const t s
      · intro t ht; unfold valueToGo; rw [if_pos ht, if_neg (not_lt.mpr hsb)]
  -- `valueToGo` solves the HJB equations
  have hHJB : IsHJB μ lam T s tD (valueToGo μ b lam T s tD) := by
    refine ⟨by rw [hVeq1 tD le_rfl, hQtD], ?_, ?_, ?_, ?_, ?_⟩
    · intro h
      rw [hVeq2 T h]; simp only [hP, sub_self, mul_zero]; exact hTinv0
    · exact hQcont.congr (fun t ht => hVeq1 t ht.2)
    · exact (hPcont.mono (fun t ht => Set.mem_Iic.mpr ht.2)).congr (fun t ht => hVeq2 t ht.1)
    · intro t ht
      rw [hVeq1 t ht.2.le]
      exact (hQderiv t ht.2).hasDerivWithinAt.congr (fun x hx => hVeq1 x hx.2) (hVeq1 t ht.2.le)
    · intro t ht
      rw [hVeq2 t ht.1]
      apply (hPderiv t ht.2).congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds ht.1] with x hx
      exact hVeq2 x hx
  refine ⟨hHJB, ?_, hma.2.1, ?_⟩
  · intro W hW t ht
    obtain ⟨hW1, hW2, hW3, hW4, hW5, hW6⟩ := hW
    obtain ⟨hV1, hV2, hV3, hV4, hV5, hV6⟩ := hHJB
    by_cases htt : t ≤ tD
    · have := uniq_back hμ hlam (p := 0) (q := tD) hW3
        (fun x hx => (hW5 x ⟨hx.1.le, hx.2⟩).hasDerivAt (Icc_mem_nhds hx.1 hx.2)) hV3
        (fun x hx => (hV5 x ⟨hx.1.le, hx.2⟩).hasDerivAt (Icc_mem_nhds hx.1 hx.2))
        (by rw [hW1, hV1])
      exact this ⟨ht.1, htt⟩
    · push Not at htt
      have hlt : tD < T := lt_of_lt_of_le htt ht.2
      have hsub : Set.Icc t T ⊆ Set.Ioc tD T := fun x hx => ⟨lt_of_lt_of_le htt hx.1, hx.2⟩
      have := uniq_back hμ hlam (p := t) (q := T) (hW4.mono hsub)
        (fun x hx => hW6 x ⟨lt_trans htt hx.1, hx.2⟩) (hV4.mono hsub)
        (fun x hx => hV6 x ⟨lt_trans htt hx.1, hx.2⟩)
        (by rw [hW2 hlt, hV2 hlt])
      exact this ⟨le_rfl, ht.2⟩
  · intro hlt
    have hc : ContinuousWithinAt P (Set.Ioi tD) tD :=
      (hPcont tD (Set.mem_Iic.mpr htDT)).mono_of_mem_nhdsWithin
        (mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds hlt))
    have ht := hc.tendsto
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (hVeq2 x hx).symm
