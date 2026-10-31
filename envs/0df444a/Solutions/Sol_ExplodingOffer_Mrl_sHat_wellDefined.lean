-- Prove2me | solution 1 for ExplodingOffer.Mrl.sHat_wellDefined
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T23:12:36.950893+00:00
-- url     : https://prove2.me/submissions/fb09d8b2-eb74-414c-b875-455e6837de33

import Mathlib
import Definitions.Def_ExplodingOffer_Mrl_Model

open MeasureTheory
open ExplodingOffer.Mrl

namespace SHatAux

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


lemma mean_le_b (hμ : OfferDist μ a b) (r : ℝ)
    (hb : b = (r : EReal)) : mean μ ≤ r := by
  haveI := hμ.isProb
  have hae : ∀ᵐ x ∂μ, x ≤ r := by
    rw [ae_iff]
    have : {x : ℝ | ¬ x ≤ r} = {x : ℝ | b < (x : EReal)} := by
      ext x; simp [hb, not_le]
    rw [this]; exact hμ.above
  have := integral_mono_ae hμ.integrable (integrable_const r) hae
  simpa [mean] using this

lemma a_le_mean (hμ : OfferDist μ a b) : a ≤ mean μ := by
  haveI := hμ.isProb
  have hae : ∀ᵐ x ∂μ, a ≤ x := by
    rw [ae_iff]
    have : {x : ℝ | ¬ a ≤ x} = Set.Iio a := by ext x; simp
    rw [this]; exact hμ.below
  have := integral_mono_ae (integrable_const a) hμ.integrable hae
  simpa [mean] using this

lemma Ici_pos (hμ : OfferDist μ a b) (s : ℝ) (hs : (s : EReal) < b) : 0 < μ.real (Set.Ici s) := by
  haveI := hμ.isProb
  rw [Measure.real_def]
  exact ENNReal.toReal_pos
    (lt_of_lt_of_le (Ioi_pos hμ s hs) (measure_mono Set.Ioi_subset_Ici_self)).ne'
    (measure_ne_top _ _)

lemma cont_tail (hμ : OfferDist μ a b) (g : ℝ → ℝ) (hg : Integrable g μ) :
    Continuous (fun s => ∫ x, (Set.Ici s).indicator g x ∂μ) := by
  haveI := hμ.noAtoms
  rw [continuous_iff_continuousAt]
  intro s₀
  apply continuousAt_of_dominated (bound := fun x => ‖g x‖)
  · exact Filter.Eventually.of_forall fun s => hg.aestronglyMeasurable.indicator measurableSet_Ici
  · exact Filter.Eventually.of_forall fun s => ae_of_all _ fun x => norm_indicator_le_norm_self g x
  · exact hg.norm
  · have hne : ∀ᵐ x ∂μ, x ≠ s₀ := by
      rw [ae_iff]
      have : {x : ℝ | ¬ x ≠ s₀} = {s₀} := by ext x; simp
      rw [this]; exact measure_singleton s₀
    filter_upwards [hne] with x hx
    rcases lt_or_gt_of_ne hx with h | h
    · apply (continuousAt_const (y := (0:ℝ))).congr
      filter_upwards [Ioi_mem_nhds h] with s hs
      rw [Set.indicator_of_notMem]
      simp only [Set.mem_Ici, not_le]; exact hs
    · apply (continuousAt_const (y := g x)).congr
      filter_upwards [Iio_mem_nhds h] with s hs
      rw [Set.indicator_of_mem]
      simp only [Set.mem_Ici]; exact (Set.mem_Iio.mp hs).le

lemma condMean_eq (s : ℝ) : condMean μ s =
    (∫ x, (Set.Ici s).indicator id x ∂μ) / (∫ x, (Set.Ici s).indicator (1 : ℝ → ℝ) x ∂μ) := by
  unfold condMean
  rw [integral_indicator measurableSet_Ici, integral_indicator_one measurableSet_Ici,
    Measure.real_def]
  rfl

lemma condMean_cont (hμ : OfferDist μ a b) (W : ℝ) (hW : (W : EReal) < b) :
    ContinuousOn (condMean μ) (Set.Iic W) := by
  haveI := hμ.isProb
  have : condMean μ = fun s => (∫ x, (Set.Ici s).indicator id x ∂μ) /
      (∫ x, (Set.Ici s).indicator (1 : ℝ → ℝ) x ∂μ) := funext condMean_eq
  rw [this]
  apply ContinuousOn.div (cont_tail hμ id hμ.integrable).continuousOn
    (cont_tail hμ 1 (integrable_const 1)).continuousOn
  intro s hs
  rw [integral_indicator_one measurableSet_Ici]
  exact (Ici_pos hμ s (lt_of_le_of_lt (EReal.coe_le_coe_iff.mpr hs) hW)).ne'

lemma condMean_ge (hμ : OfferDist μ a b) (s : ℝ) (hs : (s : EReal) < b) : s ≤ condMean μ s := by
  haveI := hμ.isProb
  have hq := Ici_pos hμ s hs
  have h : ∫ x in Set.Ici s, s ∂μ ≤ ∫ x in Set.Ici s, x ∂μ :=
    setIntegral_mono_on (integrable_const s).integrableOn hμ.integrable.integrableOn
      measurableSet_Ici (fun x hx => hx)
  rw [setIntegral_const, smul_eq_mul] at h
  unfold condMean
  rw [le_div_iff₀ (by rwa [Measure.real_def] at hq)]
  rw [Measure.real_def] at h
  linarith

lemma condMean_strictMono (hμ : OfferDist μ a b) :
    StrictMonoOn (condMean μ) {s : ℝ | a ≤ s ∧ (s : EReal) < b} := by
  haveI := hμ.isProb
  intro s hs t ht hst
  have hdisj : Disjoint (Set.Ico s t) (Set.Ici t) := by
    rw [Set.disjoint_left]; intro x hx hx'; exact absurd hx.2 (not_lt.mpr hx')
  have hunion : Set.Ici s = Set.Ico s t ∪ Set.Ici t := by
    rw [Set.Ico_union_Ici_eq_Ici hst.le]
  set p := μ.real (Set.Ico s t)
  set q := μ.real (Set.Ici t)
  set A := ∫ x in Set.Ico s t, x ∂μ
  set B := ∫ x in Set.Ici t, x ∂μ
  have hq : 0 < q := Ici_pos hμ t ht.2
  have hpo : 0 < μ (Set.Ioo s t) := hμ.noGap s t hs.1 hst ht.2.le
  have hp : 0 < p := by
    simp only [p, Measure.real_def]
    exact ENNReal.toReal_pos (lt_of_lt_of_le hpo (measure_mono Set.Ioo_subset_Ico_self)).ne'
      (measure_ne_top _ _)
  have hB : t * q ≤ B := by
    have h : ∫ x in Set.Ici t, t ∂μ ≤ B :=
      setIntegral_mono_on (integrable_const t).integrableOn hμ.integrable.integrableOn
        measurableSet_Ici (fun x hx => hx)
    rw [setIntegral_const, smul_eq_mul] at h; linarith
  have hA : A < t * p := by
    have hint : IntegrableOn (fun x : ℝ => t - x) (Set.Ico s t) μ :=
      ((integrable_const t).sub hμ.integrable).integrableOn
    have hpos : 0 < ∫ x in Set.Ico s t, (t - x) ∂μ := by
      rw [integral_pos_iff_support_of_nonneg_ae]
      · rw [Measure.restrict_apply' measurableSet_Ico]
        refine lt_of_lt_of_le hpo (measure_mono ?_)
        intro x hx
        refine ⟨?_, Set.Ioo_subset_Ico_self hx⟩
        simp only [Function.mem_support]; linarith [hx.2]
      · filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
        simp only [Pi.zero_apply]; linarith [hx.2]
      · exact hint
    rw [integral_sub (integrable_const t).integrableOn hμ.integrable.integrableOn,
      setIntegral_const, smul_eq_mul] at hpos
    linarith
  have hsplit_num : ∫ x in Set.Ici s, x ∂μ = A + B := by
    rw [hunion, setIntegral_union hdisj measurableSet_Ici hμ.integrable.integrableOn
      hμ.integrable.integrableOn]
  have hsplit_den : (μ (Set.Ici s)).toReal = p + q := by
    rw [hunion, measure_union hdisj measurableSet_Ici, ENNReal.toReal_add (measure_ne_top _ _)
      (measure_ne_top _ _)]
    rfl
  have hct : condMean μ t = B / q := rfl
  have hcs : condMean μ s = (A + B) / (p + q) := by
    unfold condMean; rw [hsplit_num, hsplit_den]
  rw [hcs, hct, div_lt_div_iff₀ (by linarith) hq]
  have h1 : A * q < t * p * q := mul_lt_mul_of_pos_right hA hq
  have h2 : t * q * p ≤ B * p := mul_le_mul_of_nonneg_right hB hp.le
  nlinarith

lemma condMean_a (hμ : OfferDist μ a b) : condMean μ a = mean μ := by
  haveI := hμ.isProb
  have hae : ∀ᵐ x ∂μ, x ∈ Set.Ici a := by
    rw [ae_iff]
    have : {x : ℝ | ¬ x ∈ Set.Ici a} = Set.Iio a := by ext x; simp
    rw [this]; exact hμ.below
  have h1 : μ (Set.Ici a) = 1 := by
    have := prob_compl_eq_one_sub (μ := μ) (s := Set.Iio a) measurableSet_Iio
    rw [Set.compl_Iio, hμ.below] at this; simpa using this
  unfold condMean mean
  rw [Measure.restrict_eq_self_of_ae_mem hae, h1]
  simp

lemma a_lt_b (hμ : OfferDist μ a b) : (a : EReal) < b := by
  haveI := hμ.isProb
  rcases lt_or_eq_of_le hμ.a_le_b with h | h
  · exact h
  · exfalso
    -- all mass would sit at the atom `a`
    have h1 : μ (Set.Ici a) = 1 := by
      have := prob_compl_eq_one_sub (μ := μ) (s := Set.Iio a) measurableSet_Iio
      rw [Set.compl_Iio, hμ.below] at this; simpa using this
    have h2 : μ (Set.Ioi a) = 0 := by
      have : Set.Ioi a ⊆ {x : ℝ | b < (x : EReal)} := by
        intro x hx; rw [← h]; exact EReal.coe_lt_coe_iff.mpr hx
      exact measure_mono_null this hμ.above
    haveI := hμ.noAtoms
    have h3 : μ (Set.Ici a) ≤ μ {a} + μ (Set.Ioi a) := by
      rw [← Set.Ioi_insert, Set.insert_eq]
      exact measure_union_le _ _
    rw [h1, measure_singleton, h2] at h3
    simp at h3

end SHatAux

open SHatAux in
theorem solution {μ : Measure ℝ} {a : ℝ} {b : EReal} (hμ : OfferDist μ a b) :
    StrictMonoOn (condMean μ) {s : ℝ | a ≤ s ∧ (s : EReal) < b} ∧
    condMean μ a = mean μ ∧
    (∀ u : ℝ, 0 < u → ∃! sh : ℝ, IsSHat μ a b u sh) ∧
    (∀ u sh : ℝ, 0 < u → IsSHat μ a b u sh → sh ≤ u) := by
  have hsm := condMean_strictMono hμ
  refine ⟨hsm, condMean_a hμ, ?_, ?_⟩
  · intro u hu
    by_cases h1 : b ≤ (u : EReal)
    · induction b using EReal.rec with
      | bot => exact absurd hμ.a_le_b (by simp)
      | top => exact absurd h1 (by simp)
      | coe r =>
        have hru : r ≤ u := EReal.coe_le_coe_iff.mp h1
        refine ⟨r, Or.inl ⟨h1, by simp⟩, ?_⟩
        intro y hy
        rcases hy with ⟨_, he⟩ | ⟨_, hub, _⟩ | ⟨hlt, _⟩
        · simpa using he
        · exact absurd (EReal.coe_lt_coe_iff.mp hub) (not_lt.mpr hru)
        · have := mean_le_b hμ r rfl; linarith
    · push Not at h1
      by_cases h2 : mean μ ≤ u
      · have hau : a ≤ u := le_trans (a_le_mean hμ) h2
        have hcont : ContinuousOn (condMean μ) (Set.Icc a u) :=
          (condMean_cont hμ u h1).mono (fun x hx => hx.2)
        obtain ⟨c, hc, hcu⟩ := intermediate_value_Icc hau hcont
          ⟨by rw [condMean_a hμ]; exact h2, condMean_ge hμ u h1⟩
        have hcb : (c : EReal) < b := lt_of_le_of_lt (EReal.coe_le_coe_iff.mpr hc.2) h1
        refine ⟨c, Or.inr (Or.inl ⟨h2, h1, hc.1, hcb, hcu⟩), ?_⟩
        intro y hy
        rcases hy with ⟨hbu, _⟩ | ⟨_, _, hay, hyb, hyu⟩ | ⟨hlt, _⟩
        · exact absurd (lt_of_lt_of_le h1 hbu) (lt_irrefl _)
        · exact hsm.injOn ⟨hay, hyb⟩ ⟨hc.1, hcb⟩ (by rw [hyu, hcu])
        · exact absurd hlt (not_lt.mpr h2)
      · push Not at h2
        refine ⟨0, Or.inr (Or.inr ⟨h2, rfl⟩), ?_⟩
        intro y hy
        rcases hy with ⟨hbu, _⟩ | ⟨hm, _, _, _, _⟩ | ⟨_, he⟩
        · exact absurd (lt_of_lt_of_le h1 hbu) (lt_irrefl _)
        · exact absurd hm (not_le.mpr h2)
        · exact he
  · intro u sh hu hsh
    rcases hsh with ⟨hbu, he⟩ | ⟨_, _, _, hshb, hc⟩ | ⟨_, he⟩
    · induction b using EReal.rec with
      | bot => exact absurd hμ.a_le_b (by simp)
      | top => exact absurd hbu (by simp)
      | coe r => rw [he]; simpa using hbu
    · rw [← hc]; exact condMean_ge hμ sh hshb
    · rw [he]; exact hu.le
