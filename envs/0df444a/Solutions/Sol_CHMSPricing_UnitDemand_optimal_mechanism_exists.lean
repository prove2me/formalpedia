-- Prove2me | solution 1 for CHMSPricing.UnitDemand.optimal_mechanism_exists
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T07:45:55.328062+00:00
-- url     : https://prove2.me/submissions/f6d6cf88-6bbb-45a4-ac16-662804f111cb

import Mathlib
import Definitions.Def_CHMSPricing_UnitDemand_Mechanism



namespace CHMSPricing.UnitDemand

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
end CHMSPricing.UnitDemand

namespace CHMSPricing.UnitDemand
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
end CHMSPricing.UnitDemand

namespace CHMSPricing.UnitDemand
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
end CHMSPricing.UnitDemand

namespace CHMSPricing.UnitDemand
open MeasureTheory Set

section Myerson
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- virtual surplus -/
noncomputable def vs (D : ι → ValueDist) (S : Finset ι) (v : ι → ℝ) : ℝ :=
  ∑ i ∈ S, (D i).virtualValue (v i)

open Classical in
noncomputable def feasSets (J : SetSystem ι) : Finset (Finset ι) :=
  Finset.univ.filter J.Feasible

lemma mem_feasSets (J : SetSystem ι) (S : Finset ι) : S ∈ feasSets J ↔ J.Feasible S := by
  classical
  simp [feasSets]

lemma feasSets_nonempty (J : SetSystem ι) : (feasSets J).Nonempty :=
  ⟨∅, (mem_feasSets J ∅).2 J.feasible_empty⟩

noncomputable def rk (S : Finset ι) : ℕ := (Fintype.equivFin (Finset ι) S : ℕ)

lemma rk_inj : Function.Injective (rk (ι := ι)) := fun S T h =>
  (Fintype.equivFin (Finset ι)).injective (Fin.ext h)

noncomputable def keyf (D : ι → ValueDist) (v : ι → ℝ) (S : Finset ι) : ℝ ×ₗ ℕ :=
  toLex (vs D S v, rk S)

lemma keyf_le_iff (D : ι → ValueDist) (v : ι → ℝ) (S T : Finset ι) :
    keyf D v T ≤ keyf D v S ↔ vs D T v < vs D S v ∨ (vs D T v = vs D S v ∧ rk T ≤ rk S) :=
  Prod.Lex.toLex_le_toLex

noncomputable def myAlloc (D : ι → ValueDist) (J : SetSystem ι) (v : ι → ℝ) : Finset ι :=
  Classical.choose (Finset.exists_max_image (feasSets J) (keyf D v) (feasSets_nonempty J))

lemma myAlloc_spec (D : ι → ValueDist) (J : SetSystem ι) (v : ι → ℝ) :
    myAlloc D J v ∈ feasSets J ∧ ∀ T ∈ feasSets J, keyf D v T ≤ keyf D v (myAlloc D J v) :=
  Classical.choose_spec (Finset.exists_max_image (feasSets J) (keyf D v) (feasSets_nonempty J))

lemma myAlloc_eq_iff (D : ι → ValueDist) (J : SetSystem ι) (v : ι → ℝ) (S : Finset ι) :
    myAlloc D J v = S ↔ S ∈ feasSets J ∧ ∀ T ∈ feasSets J, keyf D v T ≤ keyf D v S := by
  constructor
  · rintro rfl
    exact myAlloc_spec D J v
  · rintro ⟨hS, hmax⟩
    obtain ⟨hA, hAmax⟩ := myAlloc_spec D J v
    have h1 := hmax _ hA
    have h2 := hAmax _ hS
    have heq : keyf D v (myAlloc D J v) = keyf D v S := le_antisymm h1 h2
    have := congrArg (fun k : ℝ ×ₗ ℕ => (ofLex k).2) heq
    simp only [keyf, ofLex_toLex] at this
    exact rk_inj this

lemma vs_update (D : ι → ValueDist) (T : Finset ι) (v : ι → ℝ) (i : ι) (x y : ℝ) :
    vs D T (Function.update v i y) = vs D T (Function.update v i x) +
      (if i ∈ T then (D i).virtualValue y - (D i).virtualValue x else 0) := by
  unfold vs
  by_cases hi : i ∈ T
  · rw [if_pos hi, ← Finset.add_sum_erase _ _ hi, ← Finset.add_sum_erase _ _ hi]
    simp only [Function.update_self]
    have : ∀ j ∈ T.erase i, (D j).virtualValue (Function.update v i y j) =
        (D j).virtualValue (Function.update v i x j) := by
      intro j hj
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj),
        Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    rw [Finset.sum_congr rfl this]
    ring
  · rw [if_neg hi, add_zero]
    apply Finset.sum_congr rfl
    intro j hj
    have : j ≠ i := fun h => hi (h ▸ hj)
    rw [Function.update_of_ne this, Function.update_of_ne this]

lemma myAlloc_mono (D : ι → ValueDist) (hreg : ∀ i, (D i).Regular) (J : SetSystem ι)
    (v : ι → ℝ) (i : ι) (x y : ℝ) (hx : x ∈ Icc (D i).lo (D i).hi) (hy : y ∈ Icc (D i).lo (D i).hi)
    (hxy : x ≤ y) (hi : i ∈ myAlloc D J (Function.update v i x)) :
    i ∈ myAlloc D J (Function.update v i y) := by
  by_contra hn
  obtain ⟨hSF, hSmax⟩ := myAlloc_spec D J (Function.update v i x)
  obtain ⟨hS'F, hS'max⟩ := myAlloc_spec D J (Function.update v i y)
  have hφ : (D i).virtualValue x ≤ (D i).virtualValue y := hreg i hx hy hxy
  have e1 := vs_update D (myAlloc D J (Function.update v i x)) v i x y
  rw [if_pos hi] at e1
  have e2 := vs_update D (myAlloc D J (Function.update v i y)) v i x y
  rw [if_neg hn, add_zero] at e2
  have h1 := (keyf_le_iff D _ _ _).1 (hSmax _ hS'F)
  have h2 := (keyf_le_iff D _ _ _).1 (hS'max _ hSF)
  have hrk : rk (myAlloc D J (Function.update v i x)) = rk (myAlloc D J (Function.update v i y)) := by
    rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
    · exfalso; linarith
    · exfalso; linarith
    · exfalso; linarith
    · omega
  rw [rk_inj hrk] at hi
  exact hn hi

lemma vs_measurable (D : ι → ValueDist) (T : Finset ι) :
    Measurable (fun v : ι → ℝ => vs D T v) := by
  unfold vs
  exact Finset.measurable_sum _
    (fun i _ => (RevAux.vv_measurable (D i)).comp (measurable_pi_apply i))

lemma myAlloc_fiber_meas (D : ι → ValueDist) (J : SetSystem ι) (S : Finset ι) :
    MeasurableSet {v | myAlloc D J v = S} := by
  have e0 : {v | myAlloc D J v = S} =
      {v | S ∈ feasSets J ∧ ∀ T ∈ feasSets J, keyf D v T ≤ keyf D v S} := by
    ext v
    exact myAlloc_eq_iff D J v S
  rw [e0]
  by_cases hS : S ∈ feasSets J
  · simp only [hS, true_and]
    have e1 : {v : ι → ℝ | ∀ T ∈ feasSets J, keyf D v T ≤ keyf D v S} =
        ⋂ T ∈ feasSets J, {v | keyf D v T ≤ keyf D v S} := by
      ext v
      simp
    rw [e1]
    refine Finset.measurableSet_biInter _ (fun T _ => ?_)
    have e : {v : ι → ℝ | keyf D v T ≤ keyf D v S} =
        {v | vs D T v < vs D S v} ∪ ({v | vs D T v = vs D S v} ∩ {v | rk T ≤ rk S}) := by
      ext v
      simp only [mem_setOf_eq, mem_union, mem_inter_iff]
      exact keyf_le_iff D v S T
    rw [e]
    refine (measurableSet_lt (vs_measurable D T) (vs_measurable D S)).union
      ((measurableSet_eq_fun (vs_measurable D T) (vs_measurable D S)).inter ?_)
    by_cases h : rk T ≤ rk S
    · simp [h]
    · simp [h]
  · simp [hS]

lemma myAlloc_mem_meas (D : ι → ValueDist) (J : SetSystem ι) (i : ι) :
    MeasurableSet {v | i ∈ myAlloc D J v} := by
  have : {v | i ∈ myAlloc D J v} =
      ⋃ S ∈ Finset.univ.filter (fun S : Finset ι => i ∈ S), {v | myAlloc D J v = S} := by
    ext v
    simp only [mem_setOf_eq, mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and,
      exists_prop]
    constructor
    · intro h
      exact ⟨myAlloc D J v, h, rfl⟩
    · rintro ⟨S, hS, rfl⟩
      exact hS
  rw [this]
  exact Finset.measurableSet_biUnion _ (fun S _ => myAlloc_fiber_meas D J S)

/-- service indicator of `i` as a function of its own value -/
noncomputable def X (D : ι → ValueDist) (J : SetSystem ι) (v : ι → ℝ) (i : ι) (z : ℝ) : ℝ :=
  if i ∈ myAlloc D J (Function.update v i z) then 1 else 0

lemma X_nonneg (D : ι → ValueDist) (J : SetSystem ι) (v : ι → ℝ) (i : ι) (z : ℝ) :
    0 ≤ X D J v i z := by
  unfold X; split_ifs <;> norm_num

lemma X_le_one (D : ι → ValueDist) (J : SetSystem ι) (v : ι → ℝ) (i : ι) (z : ℝ) :
    X D J v i z ≤ 1 := by
  unfold X; split_ifs <;> norm_num

lemma X_meas (D : ι → ValueDist) (J : SetSystem ι) (v : ι → ℝ) (i : ι) :
    Measurable (X D J v i) := by
  unfold X
  refine Measurable.ite ?_ measurable_const measurable_const
  exact (measurable_update v (a := i)) (myAlloc_mem_meas D J i)

lemma X_intInt (D : ι → ValueDist) (J : SetSystem ι) (v : ι → ℝ) (i : ι) (a b : ℝ) :
    IntervalIntegrable (X D J v i) volume a b := by
  rw [intervalIntegrable_iff]
  haveI : IsFiniteMeasure (volume.restrict (uIoc a b)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
  refine Integrable.of_bound (X_meas D J v i).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (X_nonneg D J v i z)]
  exact X_le_one D J v i z

lemma X_mono (D : ι → ValueDist) (hreg : ∀ i, (D i).Regular) (J : SetSystem ι)
    (v : ι → ℝ) (i : ι) (x y : ℝ) (hx : x ∈ Icc (D i).lo (D i).hi) (hy : y ∈ Icc (D i).lo (D i).hi)
    (hxy : x ≤ y) : X D J v i x ≤ X D J v i y := by
  unfold X
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd (myAlloc_mono D hreg J v i x y hx hy hxy h1) h2
  · norm_num
  · exact le_rfl

/-- the Myerson payment -/
noncomputable def myPay (D : ι → ValueDist) (J : SetSystem ι) (v : ι → ℝ) (i : ι) : ℝ :=
  (if i ∈ myAlloc D J v then v i else 0) -
    ∫ z, (if (D i).lo ≤ z ∧ z ≤ v i ∧ i ∈ myAlloc D J (Function.update v i z) then (1 : ℝ) else 0)

noncomputable def myMech (D : ι → ValueDist) (J : SetSystem ι) : Mechanism ι :=
  ⟨myAlloc D J, myPay D J⟩

lemma myPay_eq (D : ι → ValueDist) (J : SetSystem ι) (v : ι → ℝ) (i : ι) (hv : (D i).lo ≤ v i) :
    myPay D J v i = (if i ∈ myAlloc D J v then v i else 0) -
      ∫ z in (D i).lo..(v i), X D J v i z := by
  unfold myPay
  congr 1
  have : (fun z => if (D i).lo ≤ z ∧ z ≤ v i ∧ i ∈ myAlloc D J (Function.update v i z)
      then (1 : ℝ) else 0) = (Icc (D i).lo (v i)).indicator (X D J v i) := by
    funext z
    by_cases h1 : (D i).lo ≤ z ∧ z ≤ v i
    · by_cases h2 : i ∈ myAlloc D J (Function.update v i z)
      · rw [if_pos ⟨h1.1, h1.2, h2⟩, Set.indicator_of_mem (mem_Icc.2 h1)]
        simp [X, h2]
      · rw [if_neg (fun h => h2 h.2.2), Set.indicator_of_mem (mem_Icc.2 h1)]
        simp [X, h2]
    · rw [if_neg (fun h => h1 ⟨h.1, h.2.1⟩), Set.indicator_of_notMem (fun h => h1 (mem_Icc.1 h))]
  rw [this, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le hv]

lemma myPay_meas (D : ι → ValueDist) (J : SetSystem ι) (i : ι) :
    Measurable (fun v => myPay D J v i) := by
  unfold myPay
  refine Measurable.sub ?_ ?_
  · exact Measurable.ite (myAlloc_mem_meas D J i) (measurable_pi_apply i) measurable_const
  · let G : (ι → ℝ) × ℝ → ℝ := fun q =>
      if (D i).lo ≤ q.2 ∧ q.2 ≤ q.1 i ∧ i ∈ myAlloc D J (Function.update q.1 i q.2) then 1 else 0
    have hG : Measurable G := by
      refine Measurable.ite ?_ measurable_const measurable_const
      have m1 : MeasurableSet {q : (ι → ℝ) × ℝ | (D i).lo ≤ q.2} :=
        measurableSet_le measurable_const measurable_snd
      have m2 : MeasurableSet {q : (ι → ℝ) × ℝ | q.2 ≤ q.1 i} :=
        measurableSet_le measurable_snd ((measurable_pi_apply i).comp measurable_fst)
      have m3 : MeasurableSet {q : (ι → ℝ) × ℝ | i ∈ myAlloc D J (Function.update q.1 i q.2)} :=
        measurable_update' (myAlloc_mem_meas D J i)
      exact m1.inter (m2.inter m3)
    exact (hG.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable

lemma myPay_bound (D : ι → ValueDist) (J : SetSystem ι) (v : ι → ℝ) (i : ι)
    (hv : v ∈ typeSpace D) : |myPay D J v i| ≤ (D i).hi + ((D i).hi - (D i).lo) := by
  have hvi := hv i (mem_univ _)
  rw [myPay_eq D J v i hvi.1]
  have h0 : 0 ≤ ∫ z in (D i).lo..(v i), X D J v i z :=
    intervalIntegral.integral_nonneg hvi.1 (fun u _ => X_nonneg D J v i u)
  have h1 : ∫ z in (D i).lo..(v i), X D J v i z ≤ (v i - (D i).lo) := by
    have := intervalIntegral.integral_mono_on hvi.1 (X_intInt D J v i _ _)
      intervalIntegrable_const (fun u _ => X_le_one D J v i u)
    rwa [intervalIntegral.integral_const, smul_eq_mul, mul_one] at this
  have hvlo := (D i).lo_nonneg
  rw [abs_le]
  split_ifs <;> constructor <;> linarith [hvi.1, hvi.2]

lemma myPay_integrable (D : ι → ValueDist) (J : SetSystem ι) (i : ι) :
    Integrable (fun v => myPay D J v i) (prior D) := by
  refine Integrable.of_bound (myPay_meas D J i).aestronglyMeasurable
    ((D i).hi + ((D i).hi - (D i).lo)) ?_
  filter_upwards [ae_ts D] with v hv
  rw [Real.norm_eq_abs]
  exact myPay_bound D J v i hv

lemma X_update (D : ι → ValueDist) (J : SetSystem ι) (v : ι → ℝ) (i : ι) (x' : ℝ) :
    X D J (Function.update v i x') i = X D J v i := by
  funext z
  simp only [X, Function.update_idem]

lemma myMech_truthful (D : ι → ValueDist) (hreg : ∀ i, (D i).Regular) (J : SetSystem ι) :
    IsTruthful D J (myMech D J) where
  feasible := fun v _ => (mem_feasSets J _).1 (myAlloc_spec D J v).1
  dsic := by
    intro v hv i x' hx'
    have hvi := hv i (mem_univ _)
    show (if i ∈ myAlloc D J (Function.update v i x') then v i else 0) -
      myPay D J (Function.update v i x') i ≤
      (if i ∈ myAlloc D J v then v i else 0) - myPay D J v i
    rw [myPay_eq D J _ i (by simp [hx'.1]), myPay_eq D J v i hvi.1]
    simp only [Function.update_self, X_update]
    have hdiff : (∫ z in (D i).lo..(v i), X D J v i z) - ∫ z in (D i).lo..x', X D J v i z =
        ∫ z in x'..(v i), X D J v i z :=
      intervalIntegral.integral_interval_sub_left (X_intInt D J v i _ _) (X_intInt D J v i _ _)
    have hkey : (v i - x') * X D J v i x' ≤ ∫ z in x'..(v i), X D J v i z := by
      rcases le_or_gt x' (v i) with h | h
      · have := intervalIntegral.integral_mono_on h intervalIntegrable_const (X_intInt D J v i _ _)
          (fun u hu => X_mono D hreg J v i x' u hx' ⟨hx'.1.trans hu.1, hu.2.trans hvi.2⟩ hu.1)
        rwa [intervalIntegral.integral_const, smul_eq_mul] at this
      · have := intervalIntegral.integral_mono_on h.le (X_intInt D J v i _ _) intervalIntegrable_const
          (fun u hu => X_mono D hreg J v i u x' ⟨hvi.1.trans hu.1, hu.2.trans hx'.2⟩ hx' hu.2)
        rw [intervalIntegral.integral_const, smul_eq_mul] at this
        rw [intervalIntegral.integral_symm]
        linarith
    have hXx : X D J v i x' = if i ∈ myAlloc D J (Function.update v i x') then 1 else 0 := rfl
    rw [hXx] at hkey
    split_ifs at hkey ⊢ <;> linarith
  ir := by
    intro v hv i
    show 0 ≤ (if i ∈ myAlloc D J v then v i else 0) - myPay D J v i
    rw [myPay_eq D J v i (hv i (mem_univ _)).1]
    have h0 : 0 ≤ ∫ z in (D i).lo..(v i), X D J v i z :=
      intervalIntegral.integral_nonneg (hv i (mem_univ _)).1 (fun u _ => X_nonneg D J v i u)
    split_ifs <;> linarith
  alloc_measurable := myAlloc_mem_meas D J
  pay_measurable := myPay_meas D J
  pay_integrable := myPay_integrable D J

lemma myMech_norm (D : ι → ValueDist) (J : SetSystem ι) (v : ι → ℝ) (_hv : v ∈ typeSpace D)
    (i : ι) : (myMech D J).utility i (D i).lo (Function.update v i (D i).lo) = 0 := by
  show (if i ∈ myAlloc D J (Function.update v i (D i).lo) then (D i).lo else 0) -
    myPay D J (Function.update v i (D i).lo) i = 0
  rw [myPay_eq D J _ i (by simp)]
  simp only [Function.update_self, intervalIntegral.integral_same]
  split_ifs with h <;> simp [h]

lemma vs_integrable (D : ι → ValueDist) (M : Mechanism ι)
    (hm : ∀ i, MeasurableSet {v | i ∈ M.alloc v}) :
    Integrable (fun v => vs D (M.alloc v) v) (prior D) := by
  let Fvs : ι → (ι → ℝ) → ℝ := fun i v => if i ∈ M.alloc v then (D i).virtualValue (v i) else 0
  have hvs : ∀ v, vs D (M.alloc v) v = ∑ i, Fvs i v := by
    intro v
    simp only [vs, Fvs]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have iFvs : ∀ i, Integrable (Fvs i) (prior D) := by
    intro i
    have hφ : Integrable (fun v : ι → ℝ => (D i).virtualValue (v i)) (prior D) := by
      have hmp : MeasurePreserving (Function.eval i) (prior D) (D i).law :=
        measurePreserving_eval (fun j => (D j).law) i
      have : Integrable (D i).virtualValue (Measure.map (Function.eval i) (prior D)) := by
        rw [hmp.map_eq]; exact RevAux.vv_integrable (D i)
      exact this.comp_measurable (measurable_pi_apply i)
    have := hφ.indicator (hm i)
    refine this.congr (Filter.Eventually.of_forall (fun v => ?_))
    simp [Fvs, Set.indicator]
  simp_rw [hvs]
  exact integrable_finset_sum _ (fun i _ => iFvs i)

theorem rev_eq_vs (D : ι → ValueDist) (J : SetSystem ι) (M : Mechanism ι)
    (hM : IsTruthful D J M)
    (hnorm : ∀ v ∈ typeSpace D, ∀ i,
      M.utility i (D i).lo (Function.update v i (D i).lo) = 0) :
    revenue D M = ∫ v, vs D (M.alloc v) v ∂(prior D) := by
  let Fvs : ι → (ι → ℝ) → ℝ := fun i v => if i ∈ M.alloc v then (D i).virtualValue (v i) else 0
  have hvs : ∀ v, vs D (M.alloc v) v = ∑ i, Fvs i v := by
    intro v
    simp only [vs, Fvs]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have iFvs : ∀ i, Integrable (Fvs i) (prior D) := by
    intro i
    have hφ : Integrable (fun v : ι → ℝ => (D i).virtualValue (v i)) (prior D) := by
      have hmp : MeasurePreserving (Function.eval i) (prior D) (D i).law :=
        measurePreserving_eval (fun j => (D j).law) i
      have : Integrable (D i).virtualValue (Measure.map (Function.eval i) (prior D)) := by
        rw [hmp.map_eq]; exact RevAux.vv_integrable (D i)
      exact this.comp_measurable (measurable_pi_apply i)
    have := hφ.indicator (hM.alloc_measurable i)
    refine this.congr (Filter.Eventually.of_forall (fun v => ?_))
    simp [Fvs, Set.indicator]
  have key : ∀ i, ∫ v, M.pay v i ∂(prior D) = ∫ v, Fvs i v ∂(prior D) := by
    intro i
    rw [integral_prior_update D i _ (hM.pay_integrable i), integral_prior_update D i _ (iFvs i)]
    refine integral_congr_ae ?_
    filter_upwards [ae_ts D] with v hv
    have hlh := (D i).lo_lt_hi.le
    obtain ⟨t, ht, hx⟩ := RevAux.one_dim (D i).lo (D i).hi hlh
      (fun x => i ∈ M.alloc (Function.update v i x)) (fun x => M.pay (Function.update v i x) i)
      (by
        intro x hx y hy
        have := hM.dsic _ (update_mem_ts D v hv i x hx) i y hy
        simpa [Mechanism.utility, Function.update_idem] using this)
      (by
        have := hnorm v hv i
        simpa [Mechanism.utility] using this)
    have e1 : ∫ x, M.pay (Function.update v i x) i ∂(D i).law =
        ∫ x, (if t < x then t else 0) ∂(D i).law := by
      refine integral_congr_ae ?_
      filter_upwards [RevAux.law_ae_mem (D i), RevAux.ae_ne (D i) t] with x h1 h2
      exact (hx x h1 h2).2
    have e2 : ∫ x, Fvs i (Function.update v i x) ∂(D i).law =
        ∫ x, (if t < x then (D i).virtualValue x else 0) ∂(D i).law := by
      refine integral_congr_ae ?_
      filter_upwards [RevAux.law_ae_mem (D i), RevAux.ae_ne (D i) t] with x h1 h2
      have := (hx x h1 h2).1
      simp only [Fvs, Function.update_self]
      by_cases h : t < x
      · rw [if_pos (this.2 h), if_pos h]
      · rw [if_neg (fun h' => h (this.1 h')), if_neg h]
    rw [e1, e2, RevAux.key (D i) t ht]
    have : (fun x : ℝ => if t < x then t else 0) = (Ioi t).indicator (fun _ => t) := by
      funext x; simp [Set.indicator]
    rw [this, integral_indicator_const _ measurableSet_Ioi, measureReal_def, smul_eq_mul,
      mul_comm]
  simp_rw [hvs]
  rw [revenue, integral_finset_sum _ (fun i _ => hM.pay_integrable i),
    integral_finset_sum _ (fun i _ => iFvs i)]
  exact Finset.sum_congr rfl (fun i _ => key i)

theorem rev_le_vs (D : ι → ValueDist) (J : SetSystem ι) (M : Mechanism ι)
    (hM : IsTruthful D J M) :
    revenue D M ≤ ∫ v, vs D (M.alloc v) v ∂(prior D) := by
  let Fvs : ι → (ι → ℝ) → ℝ := fun i v => if i ∈ M.alloc v then (D i).virtualValue (v i) else 0
  have hvs : ∀ v, vs D (M.alloc v) v = ∑ i, Fvs i v := by
    intro v
    simp only [vs, Fvs]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have iFvs : ∀ i, Integrable (Fvs i) (prior D) := by
    intro i
    have hφ : Integrable (fun v : ι → ℝ => (D i).virtualValue (v i)) (prior D) := by
      have hmp : MeasurePreserving (Function.eval i) (prior D) (D i).law :=
        measurePreserving_eval (fun j => (D j).law) i
      have : Integrable (D i).virtualValue (Measure.map (Function.eval i) (prior D)) := by
        rw [hmp.map_eq]; exact RevAux.vv_integrable (D i)
      exact this.comp_measurable (measurable_pi_apply i)
    have := hφ.indicator (hM.alloc_measurable i)
    refine this.congr (Filter.Eventually.of_forall (fun v => ?_))
    simp [Fvs, Set.indicator]
  have key : ∀ i, ∫ v, M.pay v i ∂(prior D) ≤ ∫ v, Fvs i v ∂(prior D) := by
    intro i
    rw [integral_prior_update D i _ (hM.pay_integrable i), integral_prior_update D i _ (iFvs i)]
    refine integral_mono_ae (int_inner D i _ (hM.pay_integrable i)) (int_inner D i _ (iFvs i)) ?_
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
    have e1 : ∫ x, M.pay (Function.update v i x) i ∂(D i).law ≤
        t * ((D i).law (Ioi t)).toReal := by
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
    have e2 : ∫ x, Fvs i (Function.update v i x) ∂(D i).law =
        ∫ x, (if t < x then (D i).virtualValue x else 0) ∂(D i).law := by
      refine integral_congr_ae ?_
      filter_upwards [RevAux.law_ae_mem (D i), RevAux.ae_ne (D i) t] with x h1 h2
      have := (hx x h1 h2).1
      simp only [Fvs, Function.update_self]
      by_cases h : t < x
      · rw [if_pos (this.2 h), if_pos h]
      · rw [if_neg (fun h' => h (this.1 h')), if_neg h]
    rw [e2, RevAux.key (D i) t ht]
    exact e1
  simp_rw [hvs]
  rw [revenue, integral_finset_sum _ (fun i _ => hM.pay_integrable i),
    integral_finset_sum _ (fun i _ => iFvs i)]
  exact Finset.sum_le_sum (fun i _ => key i)

theorem ome_core (D : ι → ValueDist) (hreg : ∀ i, (D i).Regular) (J : SetSystem ι) :
    ∃ Mstar : Mechanism ι, IsTruthful D J Mstar ∧
      ∀ A : Mechanism ι, IsTruthful D J A → revenue D A ≤ revenue D Mstar := by
  refine ⟨myMech D J, myMech_truthful D hreg J, fun A hA => ?_⟩
  rw [rev_eq_vs D J (myMech D J) (myMech_truthful D hreg J) (myMech_norm D J)]
  refine (rev_le_vs D J A hA).trans ?_
  refine integral_mono_ae (vs_integrable D A hA.alloc_measurable)
    (vs_integrable D (myMech D J) (myAlloc_mem_meas D J)) ?_
  filter_upwards [ae_ts D] with v hv
  have hF : A.alloc v ∈ feasSets J := (mem_feasSets J _).2 (hA.feasible v hv)
  have := (keyf_le_iff D v _ _).1 ((myAlloc_spec D J v).2 _ hF)
  show vs D (A.alloc v) v ≤ vs D (myAlloc D J v) v
  rcases this with h | ⟨h, _⟩
  · exact h.le
  · exact h.le

end Myerson
end CHMSPricing.UnitDemand

open CHMSPricing.UnitDemand


theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : ι → ValueDist) (hreg : ∀ i, (D i).Regular) (𝒥 : SetSystem ι) :
    ∃ Mstar : Mechanism ι, IsTruthful D 𝒥 Mstar ∧
      ∀ A : Mechanism ι, IsTruthful D 𝒥 A → revenue D A ≤ revenue D Mstar := by
  exact ome_core D hreg 𝒥
