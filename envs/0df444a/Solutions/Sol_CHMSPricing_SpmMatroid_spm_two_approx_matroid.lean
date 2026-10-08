-- Prove2me | solution 1 for CHMSPricing.SpmMatroid.spm_two_approx_matroid
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T07:19:26.236732+00:00
-- url     : https://prove2.me/submissions/4b7e202c-8401-4658-841c-a8df15a03bfd

import Mathlib
import Definitions.Def_CHMSPricing_SpmMatroid_Mechanism
import Definitions.Def_CHMSPricing_SpmMatroid_Spm



namespace CHMSPricing.SpmMatroid

open MeasureTheory Set

namespace RevAux

variable (D : ValueDist)

lemma f_intOn : IntegrableOn D.f (Icc D.lo D.hi) :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le D.lo_lt_hi.le).1 D.f_intervalIntegrable

lemma setInt_f : ∫ x in Icc D.lo D.hi, D.f x = 1 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le D.lo_lt_hi.le,
    D.f_integral]

lemma law_univ : D.law univ = 1 := by
  rw [ValueDist.law, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (f_intOn D), setInt_f]
  · simp
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact (D.f_pos x hx).le

instance law_prob : IsProbabilityMeasure D.law := ⟨law_univ D⟩

lemma law_ac : D.law ≪ volume.restrict (Icc D.lo D.hi) := withDensity_absolutelyContinuous _ _

lemma law_ae_mem : ∀ᵐ x ∂D.law, x ∈ Icc D.lo D.hi :=
  law_ac D (ae_restrict_mem measurableSet_Icc)

lemma law_singleton (t : ℝ) : D.law {t} = 0 :=
  law_ac D (Measure.restrict_le_self.absolutelyContinuous (by simp))

lemma integral_law (g : ℝ → ℝ) :
    ∫ x, g x ∂D.law = ∫ x in Icc D.lo D.hi, D.f x * g x := by
  rw [ValueDist.law, integral_withDensity_eq_integral_toReal_smul
    (by exact ENNReal.measurable_ofReal.comp D.f_measurable) (by simp)]
  refine setIntegral_congr_fun measurableSet_Icc (fun x hx => ?_)
  simp [ENNReal.toReal_ofReal (D.f_pos x hx).le]

lemma integrable_law_iff (g : ℝ → ℝ) :
    Integrable g D.law ↔ IntegrableOn (fun x => D.f x * g x) (Icc D.lo D.hi) := by
  rw [ValueDist.law, integrable_withDensity_iff_integrable_smul'
    (by exact ENNReal.measurable_ofReal.comp D.f_measurable) (by simp)]
  refine integrable_congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  simp [ENNReal.toReal_ofReal (D.f_pos x hx).le]

lemma cdf_mono : Monotone D.cdf := fun x y h => by
  unfold ValueDist.cdf
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Iic_subset_Iic.2 h))

lemma one_sub_cdf (x : ℝ) : 1 - D.cdf x = (D.law (Ioi x)).toReal := by
  unfold ValueDist.cdf
  rw [← compl_Iic, prob_compl_eq_one_sub measurableSet_Iic, ENNReal.toReal_sub_of_le
    prob_le_one ENNReal.one_ne_top]
  simp

lemma vv_measurable : Measurable D.virtualValue := by
  unfold ValueDist.virtualValue
  exact measurable_id.sub ((measurable_const.sub (cdf_mono D).measurable).div D.f_measurable)

lemma vv_mul (x : ℝ) (hx : x ∈ Icc D.lo D.hi) :
    D.f x * D.virtualValue x = x * D.f x - (1 - D.cdf x) := by
  unfold ValueDist.virtualValue
  have := (D.f_pos x hx).ne'
  field_simp

lemma vv_integrable : Integrable D.virtualValue D.law := by
  rw [integrable_law_iff]
  have h1 : IntegrableOn (fun x => x * D.f x) (Icc D.lo D.hi) := by
    exact IntegrableOn.continuousOn_mul continuousOn_id (f_intOn D) isCompact_Icc
  have h2 : IntegrableOn (fun x => 1 - D.cdf x) (Icc D.lo D.hi) := by
    refine IntegrableOn.of_bound (by simp) ?_ 1 ?_
    · exact (measurable_const.sub (cdf_mono D).measurable).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun x => ?_)
      rw [one_sub_cdf, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
  refine (h1.sub h2).congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  rw [vv_mul D x hx]; rfl

lemma fubini_tail (t : ℝ) (ht : D.lo ≤ t) :
    ∫ x in Icc D.lo D.hi, (if t < x then (D.law (Ioi x)).toReal else 0) =
      ∫ u, (if t < u then u - t else 0) ∂D.law := by
  let K : ℝ → ℝ → ℝ := fun x u => if t < x ∧ x < u then 1 else 0
  have hK : Integrable (Function.uncurry K) ((volume.restrict (Icc D.lo D.hi)).prod D.law) := by
    haveI : IsFiniteMeasure (volume.restrict (Icc D.lo D.hi)) := ⟨by simp⟩
    refine Integrable.of_bound ?_ 1 ?_
    · have hm : MeasurableSet {p : ℝ × ℝ | t < p.1 ∧ p.1 < p.2} :=
        (measurableSet_lt measurable_const measurable_fst).inter
          (measurableSet_lt measurable_fst measurable_snd)
      have : Function.uncurry K = {p : ℝ × ℝ | t < p.1 ∧ p.1 < p.2}.indicator (fun _ => 1) := by
        funext p; simp [K, Set.indicator, Function.uncurry]
      rw [this]
      exact (measurable_const.indicator hm).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun p => ?_)
      simp only [Function.uncurry, K]; split_ifs <;> simp
  have h1 : ∀ x, (if t < x then (D.law (Ioi x)).toReal else 0) = ∫ u, K x u ∂D.law := by
    intro x
    by_cases hx : t < x
    · have : (fun u => K x u) = (Ioi x).indicator 1 := by
        funext u; simp [K, hx, Set.indicator]
      rw [if_pos hx, this, integral_indicator_one measurableSet_Ioi, measureReal_def]
    · simp [K, hx]
  simp_rw [h1]
  rw [integral_integral_swap hK]
  refine integral_congr_ae ?_
  filter_upwards [law_ae_mem D] with u hu
  have : (fun x => K x u) = (Ioo t u).indicator 1 := by
    funext x; simp [K, Set.indicator, and_comm]
  simp only [this]
  rw [integral_indicator_one measurableSet_Ioo, measureReal_restrict_apply measurableSet_Ioo]
  by_cases htu : t < u
  · rw [if_pos htu, Set.inter_eq_left.2 (Ioo_subset_Icc_self.trans (Icc_subset_Icc ht hu.2)),
      Real.volume_real_Ioo_of_le htu.le]
  · rw [if_neg htu, Ioo_eq_empty htu]; simp

lemma int_bdd (g : ℝ → ℝ) (hg : Measurable g) (C : ℝ)
    (hC : ∀ u ∈ Icc D.lo D.hi, |g u| ≤ C) : Integrable g D.law := by
  refine Integrable.of_bound hg.aestronglyMeasurable C ?_
  filter_upwards [law_ae_mem D] with u hu
  exact hC u hu

lemma key (t : ℝ) (ht : t ∈ Icc D.lo D.hi) :
    ∫ x, (if t < x then D.virtualValue x else 0) ∂D.law = t * (D.law (Ioi t)).toReal := by
  have hlo := D.lo_nonneg
  have eA : ∫ x in Icc D.lo D.hi, (if t < x then x * D.f x else 0) =
      ∫ u, (if t < u then u else 0) ∂D.law := by
    rw [integral_law]; congr 1; funext x; split_ifs <;> ring
  have iA : IntegrableOn (fun x => if t < x then x * D.f x else 0) (Icc D.lo D.hi) := by
    have h1 : IntegrableOn (fun x => x * D.f x) (Icc D.lo D.hi) :=
      IntegrableOn.continuousOn_mul continuousOn_id (f_intOn D) isCompact_Icc
    have := h1.indicator (measurableSet_Ioi (a := t))
    refine this.congr_fun (fun x _ => ?_) measurableSet_Icc
    simp [Set.indicator]
  have iB : IntegrableOn (fun x => if t < x then (D.law (Ioi x)).toReal else 0)
      (Icc D.lo D.hi) := by
    refine IntegrableOn.of_bound (by simp) ?_ 1 ?_
    · have : (fun x => if t < x then (D.law (Ioi x)).toReal else 0) =
          (Ioi t).indicator (fun x => 1 - D.cdf x) := by
        funext x; simp [Set.indicator, one_sub_cdf]
      rw [this]
      exact ((measurable_const.sub (cdf_mono D).measurable).indicator
        measurableSet_Ioi).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun x => ?_)
      split_ifs
      · rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
        exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
      · simp
  have hL : ∫ x, (if t < x then D.virtualValue x else 0) ∂D.law =
      ∫ x in Icc D.lo D.hi, (if t < x then x * D.f x else 0) -
        (if t < x then (D.law (Ioi x)).toReal else 0) := by
    rw [integral_law]
    refine setIntegral_congr_fun measurableSet_Icc (fun x hx => ?_)
    split_ifs
    · rw [vv_mul D x hx, one_sub_cdf]
    · simp
  rw [hL, integral_sub iA iB, eA, fubini_tail D t ht.1, ← integral_sub]
  · have : (fun u => (if t < u then u else 0) - (if t < u then u - t else 0)) =
        (Ioi t).indicator (fun _ => t) := by
      funext u; simp only [Set.indicator, mem_Ioi]; split_ifs <;> ring
    rw [this, integral_indicator_const _ measurableSet_Ioi, measureReal_def, smul_eq_mul, mul_comm]
  · refine int_bdd D _ (Measurable.ite measurableSet_Ioi measurable_id measurable_const) D.hi ?_
    intro u hu; split_ifs
    · rw [abs_of_nonneg (by linarith [hu.1])]; exact hu.2
    · simp; linarith [hu.1, hu.2]
  · refine int_bdd D _ (Measurable.ite measurableSet_Ioi (measurable_id.sub measurable_const)
      measurable_const) D.hi ?_
    intro u hu; split_ifs with h
    · rw [abs_of_nonneg (by linarith [hu.1])]; linarith [hu.2, ht.1]
    · simp; linarith [hu.1, hu.2]

lemma one_dim (lo hi : ℝ) (hlh : lo ≤ hi) (a : ℝ → Prop) [DecidablePred a] (g : ℝ → ℝ)
    (IC : ∀ x ∈ Icc lo hi, ∀ y ∈ Icc lo hi,
      (if a y then x else 0) - g y ≤ (if a x then x else 0) - g x)
    (hn : (if a lo then lo else 0) - g lo = 0) :
    ∃ t ∈ Icc lo hi, ∀ x ∈ Icc lo hi, x ≠ t → (a x ↔ t < x) ∧ g x = if t < x then t else 0 := by
  have hlo : lo ∈ Icc lo hi := ⟨le_rfl, hlh⟩
  by_cases hal : a lo
  · rw [if_pos hal] at hn
    have hall : ∀ x ∈ Icc lo hi, a x ∧ g x = lo := by
      intro x hx
      have h1 := IC lo hlo x hx
      have h2 := IC x hx lo hlo
      rw [if_pos hal] at h1 h2
      by_cases hax : a x
      · rw [if_pos hax] at h1 h2
        exact ⟨hax, by linarith⟩
      · rw [if_neg hax] at h1 h2
        exfalso
        have : x = lo := le_antisymm (by linarith) hx.1
        exact hax (this ▸ hal)
    refine ⟨lo, hlo, fun x hx hne => ?_⟩
    have hlt : lo < x := lt_of_le_of_ne hx.1 (Ne.symm hne)
    exact ⟨⟨fun _ => hlt, fun _ => (hall x hx).1⟩, by rw [if_pos hlt]; exact (hall x hx).2⟩
  · rw [if_neg hal] at hn
    have hg0 : g lo = 0 := by linarith
    have hna : ∀ y ∈ Icc lo hi, ¬ a y → g y = 0 := by
      intro y hy hay
      have h1 := IC lo hlo y hy
      have h2 := IC y hy lo hlo
      rw [if_neg hay, if_neg hal] at h1 h2
      linarith
    have hconst : ∀ x ∈ Icc lo hi, ∀ y ∈ Icc lo hi, a x → a y → g x = g y := by
      intro x hx y hy hax hay
      have h1 := IC x hx y hy
      have h2 := IC y hy x hx
      rw [if_pos hax, if_pos hay] at h1 h2
      linarith
    have hsep : ∀ x ∈ Icc lo hi, ∀ y ∈ Icc lo hi, a x → ¬ a y → y ≤ g x ∧ g x ≤ x := by
      intro x hx y hy hax hay
      have h1 := IC x hx y hy
      have h2 := IC y hy x hx
      rw [if_pos hax, if_neg hay, hna y hy hay] at h1 h2
      constructor <;> linarith
    by_cases hex : ∃ x0 ∈ Icc lo hi, a x0
    · obtain ⟨x0, hx0, hax0⟩ := hex
      refine ⟨g x0, ⟨(hsep x0 hx0 lo hlo hax0 hal).1, (hsep x0 hx0 lo hlo hax0 hal).2.trans hx0.2⟩,
        fun x hx hne => ?_⟩
      by_cases hax : a x
      · have e := hconst x hx x0 hx0 hax hax0
        have hle := (hsep x hx lo hlo hax hal).2
        have hlt : g x0 < x := lt_of_le_of_ne (e ▸ hle) (Ne.symm hne)
        exact ⟨⟨fun _ => hlt, fun _ => hax⟩, by rw [if_pos hlt, e]⟩
      · have hle := (hsep x0 hx0 x hx hax0 hax).1
        exact ⟨⟨fun h => absurd h hax, fun h => absurd h (not_lt.2 hle)⟩,
          by rw [if_neg (not_lt.2 hle), hna x hx hax]⟩
    · push_neg at hex
      refine ⟨hi, ⟨hlh, le_rfl⟩, fun x hx _ => ?_⟩
      have hn' : ¬ hi < x := not_lt.2 hx.2
      exact ⟨⟨fun h => absurd h (hex x hx), fun h => absurd h hn'⟩,
        by rw [if_neg hn', hna x hx (hex x hx)]⟩

lemma ae_ne (t : ℝ) : ∀ᵐ x ∂D.law, x ≠ t := by
  rw [ae_iff]; simpa using law_singleton D t

end RevAux

section Multi
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

instance prior_prob (D : ι → ValueDist) : IsProbabilityMeasure (prior D) := by
  unfold prior; infer_instance

lemma prior_update (D : ι → ValueDist) (i : ι) :
    ((prior D).prod (D i).law).map (fun p => Function.update p.1 i p.2) = prior D := by
  symm
  refine Measure.pi_eq (fun s hs => ?_)
  rw [Measure.map_apply measurable_update' (MeasurableSet.univ_pi hs)]
  have hpre : (fun p : (ι → ℝ) × ℝ => Function.update p.1 i p.2) ⁻¹' (univ.pi s) =
      (univ.pi (Function.update s i univ)) ×ˢ s i := by
    ext ⟨v, x⟩
    simp only [mem_preimage, mem_pi, mem_univ, true_implies, mem_prod]
    constructor
    · intro h
      refine ⟨fun j => ?_, by simpa using h i⟩
      by_cases hj : j = i
      · subst hj; simp
      · simpa [hj] using h j
    · rintro ⟨h1, h2⟩ j
      by_cases hj : j = i
      · subst hj; simpa using h2
      · simpa [hj] using h1 j
  rw [hpre, Measure.prod_prod, prior, Measure.pi_pi]
  rw [← Finset.mul_prod_erase Finset.univ (fun j => (D j).law (s j)) (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  simp only [Function.update_self, measure_univ, one_mul]
  rw [mul_comm]
  congr 1
  refine Finset.prod_congr rfl (fun j hj => ?_)
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

lemma integral_prior_update (D : ι → ValueDist) (i : ι) (F : (ι → ℝ) → ℝ)
    (hF : Integrable F (prior D)) :
    ∫ v, F v ∂(prior D) = ∫ v, ∫ x, F (Function.update v i x) ∂(D i).law ∂(prior D) := by
  have hmeas : Measurable (fun p : (ι → ℝ) × ℝ => Function.update p.1 i p.2) := measurable_update'
  conv_lhs => rw [← prior_update D i]
  rw [← prior_update D i] at hF
  rw [integral_map hmeas.aemeasurable hF.aestronglyMeasurable]
  exact integral_prod (fun p : (ι → ℝ) × ℝ => F (Function.update p.1 i p.2))
    ((integrable_map_measure hF.aestronglyMeasurable hmeas.aemeasurable).1 hF)

end Multi
end CHMSPricing.SpmMatroid

namespace CHMSPricing.SpmMatroid
open MeasureTheory Set

section Main
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma update_mem_ts (D : ι → ValueDist) (v : ι → ℝ) (hv : v ∈ typeSpace D) (i : ι) (x : ℝ)
    (hx : x ∈ Icc (D i).lo (D i).hi) : Function.update v i x ∈ typeSpace D := by
  intro j _
  by_cases hj : j = i
  · subst hj; simpa using hx
  · rw [Function.update_of_ne hj]; exact hv j trivial

lemma ae_ts (D : ι → ValueDist) : ∀ᵐ v ∂(prior D), v ∈ typeSpace D := by
  have h1 : ∀ i, (D i).law (Icc (D i).lo (D i).hi) = 1 := by
    intro i
    rw [← prob_compl_eq_zero_iff measurableSet_Icc]
    have := RevAux.law_ae_mem (D i)
    rwa [ae_iff] at this
  have h2 : prior D (typeSpace D) = 1 := by
    rw [typeSpace, prior, Measure.pi_pi]; simp [h1]
  have hm : MeasurableSet (typeSpace D) := MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
  rw [ae_iff]
  have := (prob_compl_eq_zero_iff hm).2 h2
  simpa [compl_def] using this


lemma one_dim' (lo hi : ℝ) (hlh : lo ≤ hi) (a : ℝ → Prop) [DecidablePred a] (g : ℝ → ℝ)
    (IC : ∀ x ∈ Icc lo hi, ∀ y ∈ Icc lo hi,
      (if a y then x else 0) - g y ≤ (if a x then x else 0) - g x)
    (hn : 0 ≤ (if a lo then lo else 0) - g lo) :
    ∃ t ∈ Icc lo hi, ∀ x ∈ Icc lo hi, x ≠ t → (a x ↔ t < x) ∧ g x ≤ if t < x then t else 0 := by
  set c := g lo - (if a lo then lo else 0) with hc
  obtain ⟨t, ht, h⟩ := RevAux.one_dim lo hi hlh a (fun x => g x - c)
    (by intro x hx y hy; have := IC x hx y hy; linarith) (by simp [hc])
  refine ⟨t, ht, fun x hx hne => ⟨(h x hx hne).1, ?_⟩⟩
  have := (h x hx hne).2
  linarith

lemma concave_rev (D : ValueDist) (hreg : D.Regular) (t p : ℝ) (ht : t ∈ Icc D.lo D.hi)
    (hp : p ∈ Icc D.lo D.hi) :
    t * (D.law (Ioi t)).toReal ≤ p * (D.law (Ioi p)).toReal +
      D.virtualValue p * ((D.law (Ioi t)).toReal - (D.law (Ioi p)).toReal) := by
  rw [← RevAux.key D t ht, ← RevAux.key D p hp]
  have hI : ∀ s : ℝ, Integrable (fun x => if s < x then D.virtualValue x else 0) D.law := by
    intro s
    have := (RevAux.vv_integrable D).indicator (measurableSet_Ioi (a := s))
    refine this.congr (Filter.Eventually.of_forall (fun x => ?_))
    simp [Set.indicator]
  have hJ : ∀ s : ℝ, (D.law (Ioi s)).toReal = ∫ x, (if s < x then (1:ℝ) else 0) ∂D.law := by
    intro s
    have : (fun x : ℝ => if s < x then (1:ℝ) else 0) = (Ioi s).indicator 1 := by
      funext x; simp [Set.indicator]
    rw [this, integral_indicator_one measurableSet_Ioi, measureReal_def]
  have hK : ∀ s : ℝ, Integrable (fun x : ℝ => if s < x then (1:ℝ) else 0) D.law := by
    intro s
    have : (fun x : ℝ => if s < x then (1:ℝ) else 0) = (Ioi s).indicator 1 := by
      funext x; simp [Set.indicator]
    rw [this]; exact (integrable_const 1).indicator measurableSet_Ioi
  have hint : Integrable (fun a : ℝ => D.virtualValue p *
      ((if t < a then (1:ℝ) else 0) - if p < a then 1 else 0)) D.law :=
    ((hK t).sub (hK p)).const_mul _
  rw [hJ t, hJ p, ← integral_sub (hK t) (hK p), ← integral_const_mul, ← integral_add (hI p) hint]
  refine integral_mono_ae (hI t) ((hI p).add hint) ?_
  filter_upwards [RevAux.law_ae_mem D] with x hx
  by_cases h1 : t < x <;> by_cases h2 : p < x <;> simp only [h1, h2, if_true, if_false]
  · simp
  · have := hreg hx hp (le_of_not_gt h2); linarith
  · have := hreg hp hx h2.le; linarith
  · simp

end Main
end CHMSPricing.SpmMatroid

namespace CHMSPricing.SpmMatroid
open MeasureTheory Set

section Main2
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma int_inner (D : ι → ValueDist) (i : ι) (F : (ι → ℝ) → ℝ)
    (hF : Integrable F (prior D)) :
    Integrable (fun v => ∫ x, F (Function.update v i x) ∂(D i).law) (prior D) := by
  have hmeas : Measurable (fun p : (ι → ℝ) × ℝ => Function.update p.1 i p.2) := measurable_update'
  rw [← prior_update D i] at hF
  exact ((integrable_map_measure hF.aestronglyMeasurable hmeas.aemeasurable).1 hF).integral_prod_left

theorem pay_le_core (D : ι → ValueDist) (hreg : ∀ i, (D i).Regular)
    (J : SetSystem ι) (M : Mechanism ι) (hM : IsTruthful D J M)
    (p : ι → ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (D i).lo (D i).hi ∧ (D i).cdf (p i) = 1 - servProb D M i)
    (i : ι) : ∫ v, M.pay v i ∂(prior D) ≤ p i * servProb D M i := by
  let F : (ι → ℝ) → ℝ := fun v => if i ∈ M.alloc v then 1 else 0
  have hFi : Integrable F (prior D) := by
    have : F = {v | i ∈ M.alloc v}.indicator 1 := by
      funext v; simp [F, Set.indicator]
    rw [this]; exact (integrable_const 1).indicator (hM.alloc_measurable i)
  have hq : servProb D M i = ∫ v, F v ∂(prior D) := by
    have : F = {v | i ∈ M.alloc v}.indicator 1 := by
      funext v; simp [F, Set.indicator]
    rw [this, integral_indicator_one (hM.alloc_measurable i), measureReal_def, servProb]
  have hqp : ((D i).law (Ioi (p i))).toReal = servProb D M i := by
    rw [← RevAux.one_sub_cdf, (hp i).2]; ring
  set q := servProb D M i with hqdef
  set φ := (D i).virtualValue (p i)
  rw [integral_prior_update D i _ (hM.pay_integrable i)]
  have hA := int_inner D i F hFi
  have hbound : ∀ᵐ v ∂(prior D), ∫ x, M.pay (Function.update v i x) i ∂(D i).law ≤
      p i * q + φ * ((∫ x, F (Function.update v i x) ∂(D i).law) - q) := by
    filter_upwards [ae_ts D] with v hv
    have hlh := (D i).lo_lt_hi.le
    obtain ⟨t, ht, hx⟩ := one_dim' (D i).lo (D i).hi hlh
      (fun x => i ∈ M.alloc (Function.update v i x)) (fun x => M.pay (Function.update v i x) i)
      (by
        intro x hx y hy
        have := hM.dsic _ (update_mem_ts D v hv i x hx) i y hy
        simpa [Mechanism.utility, Function.update_idem] using this)
      (by
        have := hM.ir _ (update_mem_ts D v hv i _ ⟨le_rfl, hlh⟩) i
        simpa [Mechanism.utility] using this)
    have e1 : ∫ x, M.pay (Function.update v i x) i ∂(D i).law ≤ t * ((D i).law (Ioi t)).toReal := by
      have hc : (fun x : ℝ => if t < x then t else 0) = (Ioi t).indicator (fun _ => t) := by
        funext x; simp [Set.indicator]
      have hval : ∫ x, (if t < x then t else 0) ∂(D i).law = t * ((D i).law (Ioi t)).toReal := by
        rw [hc, integral_indicator_const _ measurableSet_Ioi, measureReal_def, smul_eq_mul,
          mul_comm]
      rw [← hval]
      by_cases hint : Integrable (fun x => M.pay (Function.update v i x) i) (D i).law
      · refine integral_mono_ae hint ?_ ?_
        · rw [hc]; exact (integrable_const t).indicator measurableSet_Ioi
        · filter_upwards [RevAux.law_ae_mem (D i), RevAux.ae_ne (D i) t] with x h1 h2
          exact (hx x h1 h2).2
      · rw [integral_undef hint, hval]
        exact mul_nonneg ((D i).lo_nonneg.trans ht.1) ENNReal.toReal_nonneg
    have e2 : ∫ x, F (Function.update v i x) ∂(D i).law = ((D i).law (Ioi t)).toReal := by
      have : ∫ x, F (Function.update v i x) ∂(D i).law =
          ∫ x, (Ioi t).indicator (1 : ℝ → ℝ) x ∂(D i).law := by
        refine integral_congr_ae ?_
        filter_upwards [RevAux.law_ae_mem (D i), RevAux.ae_ne (D i) t] with x h1 h2
        have := (hx x h1 h2).1
        simp only [F, Set.indicator, mem_Ioi, Pi.one_apply]
        by_cases h : t < x
        · rw [if_pos (this.2 h), if_pos h]
        · rw [if_neg (fun h' => h (this.1 h')), if_neg h]
      rw [this, integral_indicator_one measurableSet_Ioi, measureReal_def]
    rw [e2]
    have := concave_rev (D i) (hreg i) t (p i) ht (hp i).1
    rw [hqp] at this
    linarith
  have hB : Integrable (fun v => φ * ((∫ x, F (Function.update v i x) ∂(D i).law) - q))
      (prior D) := (hA.sub (integrable_const q)).const_mul φ
  refine (integral_mono_ae (int_inner D i _ (hM.pay_integrable i))
    ((integrable_const (p i * q)).add hB) hbound).trans ?_
  simp only [Pi.add_apply]
  rw [integral_add (integrable_const _) hB,
    integral_const_mul φ, integral_sub hA (integrable_const q), ← integral_prior_update D i F hFi,
    ← hq]
  simp

theorem rev_le_core (D : ι → ValueDist) (hreg : ∀ i, (D i).Regular)
    (J : SetSystem ι) (M : Mechanism ι) (hM : IsTruthful D J M)
    (p : ι → ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (D i).lo (D i).hi ∧ (D i).cdf (p i) = 1 - servProb D M i) :
    revenue D M ≤ ∑ i, p i * servProb D M i := by
  rw [revenue, integral_finset_sum _ (fun i _ => hM.pay_integrable i)]
  exact Finset.sum_le_sum (fun i _ => pay_le_core D hreg J M hM p hp i)

end Main2
end CHMSPricing.SpmMatroid


namespace CHMSPricing.SpmMatroid
open MeasureTheory Set

namespace TwoPart

open MeasureTheory Set

namespace RevAux

variable (D : ValueDist)

lemma f_intOn : IntegrableOn D.f (Icc D.lo D.hi) :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le D.lo_lt_hi.le).1 D.f_intervalIntegrable

lemma setInt_f : ∫ x in Icc D.lo D.hi, D.f x = 1 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le D.lo_lt_hi.le,
    D.f_integral]

lemma law_univ : D.law univ = 1 := by
  rw [ValueDist.law, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (f_intOn D), setInt_f]
  · simp
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact (D.f_pos x hx).le

instance law_prob : IsProbabilityMeasure D.law := ⟨law_univ D⟩

lemma law_ac : D.law ≪ volume.restrict (Icc D.lo D.hi) := withDensity_absolutelyContinuous _ _

lemma law_ae_mem : ∀ᵐ x ∂D.law, x ∈ Icc D.lo D.hi :=
  law_ac D (ae_restrict_mem measurableSet_Icc)

lemma law_singleton (t : ℝ) : D.law {t} = 0 :=
  law_ac D (Measure.restrict_le_self.absolutelyContinuous (by simp))

lemma law_Ici (x : ℝ) : (D.law (Ici x)).toReal = 1 - D.cdf x := by
  rw [ValueDist.cdf, ← compl_Iio, prob_compl_eq_one_sub measurableSet_Iio,
    ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top,
    measure_congr (Iio_ae_eq_Iic' (law_singleton D x))]
  simp

end RevAux

section Multi
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

instance prior_prob (D : ι → ValueDist) : IsProbabilityMeasure (prior D) := by
  unfold prior; infer_instance

lemma prior_update (D : ι → ValueDist) (i : ι) :
    ((prior D).prod (D i).law).map (fun p => Function.update p.1 i p.2) = prior D := by
  symm
  refine Measure.pi_eq (fun s hs => ?_)
  rw [Measure.map_apply measurable_update' (MeasurableSet.univ_pi hs)]
  have hpre : (fun p : (ι → ℝ) × ℝ => Function.update p.1 i p.2) ⁻¹' (univ.pi s) =
      (univ.pi (Function.update s i univ)) ×ˢ s i := by
    ext ⟨v, x⟩
    simp only [mem_preimage, mem_pi, mem_univ, true_implies, mem_prod]
    constructor
    · intro h
      refine ⟨fun j => ?_, by simpa using h i⟩
      by_cases hj : j = i
      · subst hj; simp
      · simpa [hj] using h j
    · rintro ⟨h1, h2⟩ j
      by_cases hj : j = i
      · subst hj; simpa using h2
      · simpa [hj] using h1 j
  rw [hpre, Measure.prod_prod, prior, Measure.pi_pi]
  rw [← Finset.mul_prod_erase Finset.univ (fun j => (D j).law (s j)) (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  simp only [Function.update_self, measure_univ, one_mul]
  rw [mul_comm]
  congr 1
  refine Finset.prod_congr rfl (fun j hj => ?_)
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

lemma integral_prior_update (D : ι → ValueDist) (i : ι) (F : (ι → ℝ) → ℝ)
    (hF : Integrable F (prior D)) :
    ∫ v, F v ∂(prior D) = ∫ v, ∫ x, F (Function.update v i x) ∂(D i).law ∂(prior D) := by
  have hmeas : Measurable (fun p : (ι → ℝ) × ℝ => Function.update p.1 i p.2) := measurable_update'
  conv_lhs => rw [← prior_update D i]
  rw [← prior_update D i] at hF
  rw [integral_map hmeas.aemeasurable hF.aestronglyMeasurable]
  exact integral_prod (fun p : (ι → ℝ) × ℝ => F (Function.update p.1 i p.2))
    ((integrable_map_measure hF.aestronglyMeasurable hmeas.aemeasurable).1 hF)

end Multi

namespace MatAux
variable {n : ℕ}
lemma A_succ (J : SetSystem (Fin n)) (σ : Equiv.Perm (Fin n)) (p v : Fin n → ℝ) (k : ℕ)
    (hk : k < n) :
    spmServedBefore J σ p v (k+1) = spmStep J p v (spmServedBefore J σ p v k) (σ ⟨k, hk⟩) := by
  have htake : (List.finRange n).take (k+1) = (List.finRange n).take k ++ [⟨k, hk⟩] := by
    rw [List.take_add_one]
    congr 1
    simp [hk]
  unfold spmServedBefore
  rw [htake, List.foldl_append]
  rfl

lemma A_zero (J : SetSystem (Fin n)) (σ : Equiv.Perm (Fin n)) (p v : Fin n → ℝ) :
    spmServedBefore J σ p v 0 = ∅ := by simp [spmServedBefore]

lemma A_dep (J : SetSystem (Fin n)) (σ : Equiv.Perm (Fin n)) (p v w : Fin n → ℝ) (k : ℕ)
    (hk : k ≤ n) (h : ∀ j : Fin n, j.val < k → (p (σ j) ≤ v (σ j) ↔ p (σ j) ≤ w (σ j))) :
    spmServedBefore J σ p v k = spmServedBefore J σ p w k := by
  induction k with
  | zero => rw [A_zero, A_zero]
  | succ k ih =>
    rw [A_succ J σ p v k hk, A_succ J σ p w k hk, ih (by omega) (fun j hj => h j (by omega))]
    have hiff := h ⟨k, hk⟩ (by simp)
    unfold spmStep
    split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; tauto)

lemma A_feas (J : SetSystem (Fin n)) (σ : Equiv.Perm (Fin n)) (p v : Fin n → ℝ) (k : ℕ)
    (hk : k ≤ n) : J.Feasible (spmServedBefore J σ p v k) := by
  induction k with
  | zero => rw [A_zero]; exact J.feasible_empty
  | succ k ih =>
    rw [A_succ J σ p v k hk]
    unfold spmStep
    split_ifs with h
    · exact h.1
    · exact ih (by omega)

lemma A_mem (J : SetSystem (Fin n)) (σ : Equiv.Perm (Fin n)) (p v : Fin n → ℝ) (j : Fin n)
    (m : ℕ) (hm : m ≤ n) :
    σ j ∈ spmServedBefore J σ p v m ↔ j.val < m ∧ σ j ∈ spmServedBefore J σ p v (j.val+1) := by
  induction m with
  | zero => simp [A_zero]
  | succ m ih =>
    have hmn : m < n := hm
    rw [A_succ J σ p v m hmn]
    unfold spmStep
    rcases lt_trichotomy j.val m with hjm | hjm | hjm
    · have hne : σ j ≠ σ ⟨m, hmn⟩ := fun e => by
        have := congrArg Fin.val (σ.injective e); simp at this; omega
      have := ih hmn.le
      split_ifs <;> simp only [Finset.mem_insert, hne, false_or, this] <;>
        constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by omega, h2⟩
    · have hj : j = ⟨m, hmn⟩ := Fin.ext hjm
      subst hj
      rw [A_succ J σ p v m hmn]
      unfold spmStep
      simp
    · have hne : σ j ≠ σ ⟨m, hmn⟩ := fun e => by
        have := congrArg Fin.val (σ.injective e); simp at this; omega
      have := ih hmn.le
      split_ifs <;> simp only [Finset.mem_insert, hne, false_or, this] <;>
        constructor <;> rintro ⟨h1, h2⟩ <;> omega

lemma A_mono (J : SetSystem (Fin n)) (σ : Equiv.Perm (Fin n)) (p v : Fin n → ℝ) (k m : ℕ)
    (hkm : k ≤ m) (hm : m ≤ n) :
    spmServedBefore J σ p v k ⊆ spmServedBefore J σ p v m := by
  induction m with
  | zero =>
    have : k = 0 := by omega
    subst this; exact subset_rfl
  | succ m ih =>
    rcases Nat.eq_or_lt_of_le hkm with h | h
    · rw [h]
    · refine (ih (by omega) (by omega)).trans ?_
      rw [A_succ J σ p v m (by omega)]
      unfold spmStep
      split_ifs
      · exact Finset.subset_insert _ _
      · exact subset_rfl

lemma abel_nonneg (a d : ℕ → ℝ) (ha : ∀ k, a (k+1) ≤ a k) (ha0 : ∀ k, 0 ≤ a k)
    (N : ℕ) (hD : ∀ m ≤ N, 0 ≤ ∑ k ∈ Finset.range m, d k) :
    0 ≤ ∑ k ∈ Finset.range N, a k * d k := by
  have key : ∀ M ≤ N, a M * ∑ k ∈ Finset.range M, d k ≤ ∑ k ∈ Finset.range M, a k * d k := by
    intro M
    induction M with
    | zero => intro _; simp
    | succ M ih =>
      intro hM
      have h1 := ih (by omega)
      have h2 := hD (M+1) hM
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      rw [Finset.sum_range_succ] at h2
      have : a (M+1) * (∑ k ∈ Finset.range M, d k + d M) ≤
          a M * (∑ k ∈ Finset.range M, d k + d M) := mul_le_mul_of_nonneg_right (ha M) h2
      nlinarith
  exact le_trans (mul_nonneg (ha0 N) (hD N le_rfl)) (key N le_rfl)

/-- extension of a `Fin n`-indexed function to `ℕ` by zero -/
noncomputable def ext (g : Fin n → ℝ) (k : ℕ) : ℝ := if h : k < n then g ⟨k, h⟩ else 0

lemma sum_prefix (g : Fin n → ℝ) (m : ℕ) (hm : m ≤ n) :
    ∑ k : Fin n, (if k.val < m then g k else 0) = ∑ k ∈ Finset.range m, ext g k := by
  have h1 := Fin.sum_univ_eq_sum_range (fun k => if k < m then ext g k else 0) n
  have h2 : ∑ k : Fin n, (if k.val < m then g k else 0) =
      ∑ k : Fin n, (if k.val < m then ext g k.val else 0) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp [ext]
  rw [h2, h1, Finset.sum_ite, Finset.sum_const_zero, add_zero]
  congr 1
  ext k; simp [Finset.mem_filter]; omega

lemma sum_all (g : Fin n → ℝ) : ∑ k : Fin n, g k = ∑ k ∈ Finset.range n, ext g k := by
  rw [← sum_prefix g n le_rfl]
  simp

/-- prefix inequality -/
lemma prefix_ineq (J : SetSystem (Fin n)) (hJ : J.IsMatroid)
    (q : Fin n → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hqr : ∀ T : Finset (Fin n), ∑ i ∈ T, q i ≤ (J.rank T : ℝ))
    (σ : Equiv.Perm (Fin n)) (p v : Fin n → ℝ) (m : ℕ) (hm : m ≤ n) :
    ∑ i ∈ (spmBlocked J σ p v).filter (fun i => (σ.symm i).val < m), q i ≤
      ((spmServedBefore J σ p v m).card : ℝ) := by
  classical
  set Am := spmServedBefore J σ p v m with hAm
  set Bm := (spmBlocked J σ p v).filter (fun i => (σ.symm i).val < m) with hBm
  have hrank : J.rank (Am ∪ Bm) ≤ Am.card := by
    unfold SetSystem.rank
    refine Finset.sup_le (fun F hF => ?_)
    rw [Finset.mem_filter, Finset.mem_powerset] at hF
    by_contra hlt
    push_neg at hlt
    obtain ⟨e, he, hfe⟩ := hJ F Am hF.2 (A_feas J σ p v m hm) hlt
    rw [Finset.mem_sdiff] at he
    have heB : e ∈ Bm := by
      rcases Finset.mem_union.1 (hF.1 he.1) with h | h
      · exact absurd h he.2
      · exact h
    rw [hBm, Finset.mem_filter] at heB
    have hbl : ¬ J.Feasible (insert e (spmServedBefore J σ p v (σ.symm e : ℕ))) := by
      have := heB.1
      simp only [spmBlocked, spmOffered] at this
      exact (Finset.mem_filter.1 this).2
    exact hbl (J.feasible_mono (Finset.insert_subset_insert _
      (A_mono J σ p v _ m heB.2.le hm)) hfe)
  calc ∑ i ∈ Bm, q i ≤ ∑ i ∈ Am ∪ Bm, q i :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right (fun i _ _ => hq0 i)
    _ ≤ (J.rank (Am ∪ Bm) : ℝ) := hqr _
    _ ≤ Am.card := by exact_mod_cast hrank

theorem blocked_core (J : SetSystem (Fin n)) (hJ : J.IsMatroid)
    (q : Fin n → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hqr : ∀ T : Finset (Fin n), ∑ i ∈ T, q i ≤ (J.rank T : ℝ))
    (σ : Equiv.Perm (Fin n)) (p : Fin n → ℝ) (hp0 : ∀ i, 0 ≤ p i)
    (hσ : ∀ a b, a ≤ b → p (σ b) ≤ p (σ a)) (v : Fin n → ℝ) :
    ∑ i ∈ spmBlocked J σ p v, p i * q i ≤
      ∑ i ∈ spmServed J σ p v, p i := by
  classical
  set B := spmBlocked J σ p v
  set A := spmServed J σ p v
  let x : Fin n → ℝ := fun k => if σ k ∈ B then q (σ k) else 0
  let y : Fin n → ℝ := fun k => if σ k ∈ A then 1 else 0
  let pk : Fin n → ℝ := fun k => p (σ k)
  have hL : ∑ i ∈ B, p i * q i = ∑ k : Fin n, pk k * x k := by
    rw [← Finset.univ_inter B, ← Finset.sum_ite_mem, ← Equiv.sum_comp σ]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [pk, x, mul_ite, mul_zero]
  have hR : ∑ i ∈ A, p i = ∑ k : Fin n, pk k * y k := by
    rw [← Finset.univ_inter A, ← Finset.sum_ite_mem, ← Equiv.sum_comp σ]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [pk, y, mul_ite, mul_zero, mul_one]
  have hext : ∀ g h : Fin n → ℝ, ∑ k : Fin n, g k * h k =
      ∑ k ∈ Finset.range n, ext g k * ext h k := by
    intro g h
    rw [sum_all (fun k => g k * h k)]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    unfold ext; split_ifs <;> simp
  have hX : ∀ m ≤ n, ∑ k ∈ Finset.range m, ext x k =
      ∑ i ∈ B.filter (fun i => (σ.symm i).val < m), q i := by
    intro m hm
    rw [← sum_prefix x m hm, ← Finset.univ_inter (B.filter _), ← Finset.sum_ite_mem]
    conv_rhs => rw [← Equiv.sum_comp σ]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [x, Finset.mem_filter, Equiv.symm_apply_apply]
    split_ifs <;> tauto
  have hY : ∀ m ≤ n, ∑ k ∈ Finset.range m, ext y k =
      ((spmServedBefore J σ p v m).card : ℝ) := by
    intro m hm
    rw [← sum_prefix y m hm, Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one,
      ← Finset.univ_inter (spmServedBefore J σ p v m), ← Finset.sum_ite_mem]
    conv_rhs => rw [← Equiv.sum_comp σ]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [y, A, spmServed]
    have h1 := A_mem J σ p v k m hm
    have h2 := A_mem J σ p v k n le_rfl
    simp only [k.isLt, true_and] at h2
    by_cases c1 : (k : ℕ) < m <;> by_cases c2 : σ k ∈ spmServedBefore J σ p v n <;>
      simp only [c1, c2, if_true, if_false] <;> simp_all
  have key := abel_nonneg (ext pk) (fun k => ext y k - ext x k) (by
      intro k
      unfold ext
      split_ifs with h1 h2
      · exact hσ _ _ (Fin.mk_le_mk.2 (by omega))
      · omega
      · exact hp0 _
      · exact le_rfl)
    (by intro k; unfold ext; split_ifs <;> simp [pk, hp0]) n (by
      intro m hm
      rw [Finset.sum_sub_distrib, hX m hm, hY m hm, sub_nonneg]
      exact prefix_ineq J hJ q hq0 hqr σ p v m hm)
  rw [hL, hR, hext, hext]
  simp only [mul_sub, Finset.sum_sub_distrib, sub_nonneg] at key
  exact key


lemma meas_A (J : SetSystem (Fin n)) (σ : Equiv.Perm (Fin n)) (p : Fin n → ℝ)
    (P : Finset (Fin n) → Prop) (k : ℕ) (hk : k ≤ n) :
    MeasurableSet {v : Fin n → ℝ | P (spmServedBefore J σ p v k)} := by
  classical
  let acc : (Fin n → ℝ) → (Fin n → Bool) := fun v i => decide (p i ≤ v i)
  have hacc : Measurable acc := by
    refine measurable_pi_lambda _ (fun i => ?_)
    refine measurable_to_countable' (fun b => ?_)
    cases b
    · have : (fun v : Fin n → ℝ => decide (p i ≤ v i)) ⁻¹' {false} = {v | v i < p i} := by
        ext v; simp
      rw [this]; exact measurableSet_lt (measurable_pi_apply i) measurable_const
    · have : (fun v : Fin n → ℝ => decide (p i ≤ v i)) ⁻¹' {true} = {v | p i ≤ v i} := by
        ext v; simp
      rw [this]; exact measurableSet_le measurable_const (measurable_pi_apply i)
  have heq : {v : Fin n → ℝ | P (spmServedBefore J σ p v k)} =
      acc ⁻¹' {b | ∃ w, acc w = b ∧ P (spmServedBefore J σ p w k)} := by
    ext v
    simp only [mem_setOf_eq, mem_preimage]
    constructor
    · intro h; exact ⟨v, rfl, h⟩
    · rintro ⟨w, hw, hP⟩
      rwa [A_dep J σ p v w k hk (fun j _ => by
        have := congrFun hw (σ j); simp [acc] at this; exact this.symm)]
  rw [heq]
  exact hacc (Set.toFinite _).measurableSet

lemma mem_succ_iff (J : SetSystem (Fin n)) (σ : Equiv.Perm (Fin n)) (p v : Fin n → ℝ) (k : Fin n) :
    σ k ∈ spmServedBefore J σ p v (k.val+1) ↔
      p (σ k) ≤ v (σ k) ∧ J.Feasible (insert (σ k) (spmServedBefore J σ p v k.val)) := by
  classical
  have hnot : σ k ∉ spmServedBefore J σ p v k.val := by
    rw [A_mem _ σ p v k k.val k.isLt.le]; simp
  have hkk : (⟨k.val, k.isLt⟩ : Fin n) = k := rfl
  rw [A_succ _ σ p v k.val k.isLt, hkk]
  unfold spmStep
  split_ifs with h
  · simp only [Finset.mem_insert, true_or, true_iff]
    exact ⟨h.2, h.1⟩
  · simp only [hnot, false_iff]
    rintro ⟨h1, h2⟩
    exact h ⟨h2, h1⟩

def Sset (J : SetSystem (Fin n)) (σ : Equiv.Perm (Fin n)) (p : Fin n → ℝ) (j : Fin n) :
    Set (Fin n → ℝ) :=
  {v | σ j ∈ spmServedBefore J σ p v (j.val+1)}

def Tset (J : SetSystem (Fin n)) (σ : Equiv.Perm (Fin n)) (p : Fin n → ℝ) (k : Fin n) :
    Set (Fin n → ℝ) :=
  {v | J.Feasible (insert (σ k) (spmServedBefore J σ p v k.val))}

lemma Sset_meas (J : SetSystem (Fin n)) (σ : Equiv.Perm (Fin n)) (p : Fin n → ℝ) (j : Fin n) :
    MeasurableSet (Sset J σ p j) :=
  meas_A J σ p (fun A => σ j ∈ A) _ j.isLt

lemma Tset_meas (J : SetSystem (Fin n)) (σ : Equiv.Perm (Fin n)) (p : Fin n → ℝ) (k : Fin n) :
    MeasurableSet (Tset J σ p k) :=
  meas_A J σ p (fun A => J.Feasible (insert (σ k) A)) _ k.isLt.le

lemma indep (D : Fin n → ValueDist) (J : SetSystem (Fin n)) (σ : Equiv.Perm (Fin n))
    (p : Fin n → ℝ) (k : Fin n) :
    (prior D (Sset J σ p k)).toReal =
      ((D (σ k)).law (Ici (p (σ k)))).toReal * (prior D (Tset J σ p k)).toReal := by
  classical
  have hS := Sset_meas J σ p k
  have hT := Tset_meas J σ p k
  have hI : Integrable ((Sset J σ p k).indicator (1 : (Fin n → ℝ) → ℝ)) (prior D) :=
    (integrable_const (1:ℝ)).indicator hS
  rw [← measureReal_def, ← integral_indicator_one hS, integral_prior_update D (σ k) _ hI]
  have hTu : ∀ v x, (Function.update v (σ k) x ∈ Tset J σ p k ↔ v ∈ Tset J σ p k) := by
    intro v x
    simp only [Tset, mem_setOf_eq]
    rw [A_dep _ σ p (Function.update v (σ k) x) v k.val k.isLt.le (fun j hj => by
      have hne : σ j ≠ σ k := fun e => by
        have := σ.injective e; rw [this] at hj; exact lt_irrefl _ hj
      rw [Function.update_of_ne hne])]
  have hinner : ∀ v, ∫ x, (Sset J σ p k).indicator 1 (Function.update v (σ k) x)
      ∂(D (σ k)).law = (Tset J σ p k).indicator 1 v *
        ((D (σ k)).law (Ici (p (σ k)))).toReal := by
    intro v
    have : (fun x => (Sset J σ p k).indicator (1 : (Fin n → ℝ) → ℝ)
        (Function.update v (σ k) x)) =
        fun x => (Tset J σ p k).indicator 1 v * (Ici (p (σ k))).indicator 1 x := by
      funext x
      simp only [Set.indicator, Sset, mem_setOf_eq, mem_succ_iff, Function.update_self, mem_Ici,
        Pi.one_apply]
      have := hTu v x
      simp only [Tset, mem_setOf_eq] at this
      by_cases h1 : p (σ k) ≤ x <;> by_cases h2 : v ∈ Tset J σ p k <;>
        simp only [Tset, mem_setOf_eq] at h2 <;> simp [h1, h2, this, Tset]
    rw [this, integral_const_mul, integral_indicator_one measurableSet_Ici, measureReal_def]
  simp_rw [hinner]
  rw [integral_mul_const, integral_indicator_one hT, measureReal_def, mul_comm]

lemma served_sum (J : SetSystem (Fin n)) (σ : Equiv.Perm (Fin n)) (p v : Fin n → ℝ) :
    ∑ i ∈ spmServed J σ p v, p i =
      ∑ k : Fin n, (Sset J σ p k).indicator (fun _ => p (σ k)) v := by
  classical
  have hA : spmServed J σ p v =
      Finset.univ.filter (· ∈ spmServed J σ p v) := by ext; simp
  rw [hA, Finset.sum_filter, ← Equiv.sum_comp σ]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [Set.indicator, Sset, mem_setOf_eq, spmServed]
  simp only [A_mem _ σ p v k n le_rfl, k.isLt, true_and]

lemma served_integrable (D : Fin n → ValueDist) (J : SetSystem (Fin n))
    (σ : Equiv.Perm (Fin n)) (p : Fin n → ℝ) :
    Integrable (fun v => ∑ i ∈ spmServed J σ p v, p i) (prior D) := by
  simp_rw [served_sum]
  exact integrable_finset_sum _ (fun k _ => (integrable_const _).indicator (Sset_meas J σ p k))

lemma rev_eq (D : Fin n → ValueDist) (J : SetSystem (Fin n)) (σ : Equiv.Perm (Fin n))
    (p : Fin n → ℝ) :
    spmRevenue D J σ p = ∑ k : Fin n, p (σ k) * (prior D (Sset J σ p k)).toReal := by
  unfold spmRevenue
  simp_rw [served_sum]
  rw [integral_finset_sum _ (fun k _ => (integrable_const _).indicator (Sset_meas J σ p k))]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [integral_indicator_const _ (Sset_meas J σ p k), measureReal_def, smul_eq_mul, mul_comm]

theorem offer_core (D : Fin n → ValueDist) (J : SetSystem (Fin n))
    (σ : Equiv.Perm (Fin n)) (p : Fin n → ℝ) :
    spmRevenue D J σ p =
      ∑ i, (prior D {v | spmOffered J σ p v i}).toReal * (1 - (D i).cdf (p i)) * p i := by
  rw [rev_eq]
  conv_rhs => rw [← Equiv.sum_comp σ]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [indep, RevAux.law_Ici]
  have : {v | spmOffered J σ p v (σ k)} = Tset J σ p k := by
    ext v; simp [spmOffered, Tset]
  rw [this]; ring

theorem two_core (D : Fin n → ValueDist)
    (J : SetSystem (Fin n)) (hJ : J.IsMatroid)
    (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Set.Icc (D i).lo (D i).hi)
    (hqr : ∀ T : Finset (Fin n), ∑ i ∈ T, (1 - (D i).cdf (p i)) ≤ (J.rank T : ℝ))
    (σ : Equiv.Perm (Fin n)) (hσ : ∀ a b, a ≤ b → p (σ b) ≤ p (σ a)) :
    ∑ i, p i * (1 - (D i).cdf (p i)) ≤ 2 * spmRevenue D J σ p := by
  classical
  set q : Fin n → ℝ := fun i => 1 - (D i).cdf (p i) with hqdef
  have hq0 : ∀ i, 0 ≤ q i := fun i => by
    simp only [hqdef]; rw [← RevAux.law_Ici]; exact ENNReal.toReal_nonneg
  have hp0 : ∀ i, 0 ≤ p i := fun i => (D i).lo_nonneg.trans (hp i).1
  let O : Fin n → Set (Fin n → ℝ) := fun i => {v | spmOffered J σ p v i}
  have hO : ∀ i, MeasurableSet (O i) := fun i =>
    meas_A J σ p (fun A => J.Feasible (insert i A)) (σ.symm i) (σ.symm i).isLt.le
  let c : Fin n → ℝ := fun i => (prior D (O i)).toReal
  have hblk : ∀ v, ∑ i ∈ spmBlocked J σ p v, p i * q i =
      ∑ i, (O i)ᶜ.indicator (fun _ => p i * q i) v := by
    intro v
    unfold spmBlocked
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp [Set.indicator, O]
  have hIb : ∀ i, Integrable ((O i)ᶜ.indicator (fun _ => p i * q i)) (prior D) := fun i =>
    (integrable_const _).indicator (hO i).compl
  have hint : ∫ v, ∑ i ∈ spmBlocked J σ p v, p i * q i ∂(prior D) =
      ∑ i, (1 - c i) * (p i * q i) := by
    simp_rw [hblk]
    rw [integral_finset_sum _ (fun i _ => hIb i)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [integral_indicator_const _ (hO i).compl, measureReal_def, smul_eq_mul,
      prob_compl_eq_one_sub (hO i), ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top]
    simp [c]
  have hle : ∫ v, ∑ i ∈ spmBlocked J σ p v, p i * q i ∂(prior D) ≤ spmRevenue D J σ p := by
    unfold spmRevenue
    refine integral_mono ?_ (served_integrable D J σ p)
      (fun v => blocked_core J hJ q hq0 hqr σ p hp0 hσ v)
    simp_rw [hblk]
    exact integrable_finset_sum _ (fun i _ => hIb i)
  have hoff := offer_core D J σ p
  have hsplit : ∑ i, p i * q i = ∑ i, c i * q i * p i + ∑ i, (1 - c i) * (p i * q i) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  have : ∑ i, c i * q i * p i = spmRevenue D J σ p := hoff.symm
  change ∑ i, p i * q i ≤ _
  linarith

end MatAux
end TwoPart

theorem goal_core {n : ℕ} (D : Fin n → ValueDist) (hreg : ∀ i, (D i).Regular)
    (J : SetSystem (Fin n)) (hJ : J.IsMatroid)
    (M : Mechanism (Fin n)) (hM : IsTruthful D J M)
    (p : Fin n → ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (D i).lo (D i).hi ∧ (D i).cdf (p i) = 1 - servProb D M i)
    (σ : Equiv.Perm (Fin n)) (hσ : ∀ a b, a ≤ b → p (σ b) ≤ p (σ a)) :
    revenue D M ≤ 2 * spmRevenue D J σ p := by
  classical
  have hsp : ∀ i, servProb D M i = 1 - (D i).cdf (p i) := fun i => by rw [(hp i).2]; ring
  have h1 := rev_le_core D hreg J M hM p hp
  have hqr : ∀ T : Finset (Fin n), ∑ i ∈ T, (1 - (D i).cdf (p i)) ≤ (J.rank T : ℝ) := by
    intro T
    simp_rw [← hsp]
    have e : ∀ i, servProb D M i =
        ∫ v, {v | i ∈ M.alloc v}.indicator (fun _ => (1:ℝ)) v ∂(prior D) := by
      intro i
      rw [integral_indicator_const _ (hM.alloc_measurable i), measureReal_def, smul_eq_mul,
        mul_one, servProb]
    simp_rw [e]
    rw [← integral_finset_sum _ (fun i _ =>
      (integrable_const (1:ℝ)).indicator (hM.alloc_measurable i))]
    have : ∫ v, ((J.rank T : ℕ) : ℝ) ∂(prior D) = J.rank T := by simp
    rw [← this]
    refine integral_mono_ae (integrable_finset_sum _ (fun i _ =>
      (integrable_const (1:ℝ)).indicator (hM.alloc_measurable i))) (integrable_const _) ?_
    filter_upwards [ae_ts D] with v hv
    have hc : ∑ i ∈ T, {v | i ∈ M.alloc v}.indicator (fun _ => (1:ℝ)) v =
        ((M.alloc v ∩ T).card : ℝ) := by
      have : M.alloc v ∩ T = T.filter (· ∈ M.alloc v) := by ext; simp [and_comm]
      rw [this, Finset.card_filter, Nat.cast_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp [Set.indicator]
    rw [hc]
    have hF : J.Feasible (M.alloc v ∩ T) :=
      J.feasible_mono Finset.inter_subset_left (hM.feasible v hv)
    have : (M.alloc v ∩ T).card ≤ J.rank T := by
      unfold SetSystem.rank
      exact Finset.le_sup (f := Finset.card) (Finset.mem_filter.2
        ⟨Finset.mem_powerset.2 Finset.inter_subset_right, hF⟩)
    exact_mod_cast this
  have h2 := TwoPart.MatAux.two_core D J hJ p (fun i => (hp i).1) hqr σ hσ
  have h3 : ∑ i, p i * servProb D M i = ∑ i, p i * (1 - (D i).cdf (p i)) := by
    simp_rw [hsp]
  linarith

end CHMSPricing.SpmMatroid

open CHMSPricing.SpmMatroid


theorem solution {n : ℕ} (D : Fin n → ValueDist) (hreg : ∀ i, (D i).Regular)
    (J : SetSystem (Fin n)) (hJ : J.IsMatroid)
    (M : Mechanism (Fin n)) (hM : IsTruthful D J M)
    (p : Fin n → ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (D i).lo (D i).hi ∧ (D i).cdf (p i) = 1 - servProb D M i)
    (σ : Equiv.Perm (Fin n)) (hσ : ∀ a b, a ≤ b → p (σ b) ≤ p (σ a)) :
    revenue D M ≤ 2 * spmRevenue D J σ p := by
  exact goal_core D hreg J hJ M hM p hp σ hσ
