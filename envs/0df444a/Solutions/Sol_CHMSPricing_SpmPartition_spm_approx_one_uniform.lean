-- Prove2me | solution 1 for CHMSPricing.SpmPartition.spm_approx_one_uniform
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T06:53:31.081989+00:00
-- url     : https://prove2.me/submissions/85919fce-929c-43cc-bef7-0c990a75905e

import Mathlib
import Definitions.Def_CHMSPricing_SpmPartition_ValueDist
import Definitions.Def_CHMSPricing_SpmPartition_SetSystem
import Definitions.Def_CHMSPricing_SpmPartition_Mechanism
import Definitions.Def_CHMSPricing_SpmPartition_Spm



namespace CHMSPricing.SpmPartition

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
end CHMSPricing.SpmPartition

namespace CHMSPricing.SpmPartition
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
end CHMSPricing.SpmPartition

namespace CHMSPricing.SpmPartition
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
end CHMSPricing.SpmPartition

namespace CHMSPricing.SpmPartition

open MeasureTheory Set

namespace SpmAux

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

lemma law_singleton (t : ℝ) : D.law {t} = 0 :=
  law_ac D (Measure.restrict_le_self.absolutelyContinuous (by simp))

lemma law_Iio (x : ℝ) : (D.law (Iio x)).toReal = D.cdf x := by
  rw [ValueDist.cdf, measure_congr (Iio_ae_eq_Iic' (law_singleton D x))]

lemma law_Ici (x : ℝ) : (D.law (Ici x)).toReal = 1 - D.cdf x := by
  rw [ValueDist.cdf, ← compl_Iio, prob_compl_eq_one_sub measurableSet_Iio,
    ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, measure_congr (Iio_ae_eq_Iic' (law_singleton D x))]
  simp

end SpmAux

variable {n : ℕ}

instance prior_prob' {ι : Type*} [Fintype ι] (D : ι → ValueDist) : IsProbabilityMeasure (prior D) := by
  unfold prior; infer_instance

/-- characterization of the served set for the 1-uniform matroid -/
lemma served_one (σ : Equiv.Perm (Fin n)) (p v : Fin n → ℝ) (m : ℕ) (hm : m ≤ n) :
    spmServedBefore (uniformSystem (Fin n) 1) σ p v m =
      (Finset.univ.filter (fun k : Fin n => k.val < m ∧ (∀ j, j < k → v (σ j) < p (σ j)) ∧
        p (σ k) ≤ v (σ k))).map σ.toEmbedding := by
  induction m with
  | zero => simp [spmServedBefore]
  | succ m ih =>
    have hmn : m < n := hm
    have ih := ih hmn.le
    have htake : (List.finRange n).take (m+1) = (List.finRange n).take m ++ [⟨m, hmn⟩] := by
      rw [List.take_add_one]
      congr 1
      simp [hmn]
    unfold spmServedBefore at ih ⊢
    rw [htake, List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil]
    set S := (Finset.univ.filter (fun k : Fin n => k.val < m ∧ (∀ j, j < k → v (σ j) < p (σ j)) ∧
        p (σ k) ≤ v (σ k))).map σ.toEmbedding with hS
    unfold spmStep
    ext x
    by_cases hE : ∀ j : Fin n, j < ⟨m, hmn⟩ → v (σ j) < p (σ j)
    · have hSe : S = ∅ := by
        rw [hS, Finset.map_eq_empty, Finset.filter_eq_empty_iff]
        rintro k - ⟨hk, -, hk2⟩
        have := hE k (Fin.mk_lt_mk.2 hk |> fun h => by simpa using h)
        linarith
      rw [hSe]
      split_ifs with hacc'
      · have hacc := hacc'.2
        simp only [Finset.mem_insert, Finset.notMem_empty, or_false, Finset.mem_map_equiv, Finset.mem_filter,
          Finset.mem_univ, true_and]
        constructor
        · rintro rfl
          refine ⟨by simp, fun j hj => hE j (by simpa using hj), by simpa using hacc⟩
        · rintro ⟨h1, h2, h3⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 h1 with h | h
          · have := hE (σ.symm x) (by exact h)
            simp at this h3; linarith
          · have : σ.symm x = ⟨m, hmn⟩ := Fin.ext h
            rw [← this]; simp
      · have hacc : ¬ p (σ ⟨m, hmn⟩) ≤ v (σ ⟨m, hmn⟩) := fun h =>
          hacc' ⟨by simp [uniformSystem], h⟩
        simp only [Finset.notMem_empty, false_iff, Finset.mem_map_equiv, Finset.mem_filter,
          Finset.mem_univ, true_and, not_and]
        intro h1 h2 h3
        rcases Nat.lt_succ_iff_lt_or_eq.1 h1 with h | h
        · have := hE (σ.symm x) (by exact h)
          simp at this h3; linarith
        · have : σ.symm x = ⟨m, hmn⟩ := Fin.ext h
          rw [this] at h3; exact hacc h3
    · push_neg at hE
      obtain ⟨j0, hj0, hj0'⟩ := hE
      have hj0m : j0.val < m := hj0
      -- S is nonempty, so inserting a new element exceeds capacity
      have hnot : ¬ ((uniformSystem (Fin n) 1).Feasible (insert (σ ⟨m, hmn⟩) S) ∧
          p (σ ⟨m, hmn⟩) ≤ v (σ ⟨m, hmn⟩)) := by
        rintro ⟨hc, -⟩
        change (insert (σ ⟨m, hmn⟩) S).card ≤ 1 at hc
        -- find the first accepted index
        classical
        let T := Finset.univ.filter (fun k : Fin n => p (σ k) ≤ v (σ k))
        have hT : T.Nonempty := ⟨j0, by simp [T, hj0']⟩
        let k0 := T.min' hT
        have hk0T : k0 ∈ T := T.min'_mem hT
        have hk0le : k0 ≤ j0 := T.min'_le j0 (by simp [T, hj0'])
        have hk0S : σ k0 ∈ S := by
          rw [hS, Finset.mem_map_equiv]
          simp only [Equiv.symm_apply_apply, Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨lt_of_le_of_lt (Fin.le_def.1 hk0le) hj0m, fun j hj => ?_, by simpa [T] using hk0T⟩
          by_contra hc'
          push_neg at hc'
          have := T.min'_le j (by simp [T, hc'])
          exact absurd hj (not_lt.2 this)
        have hne : σ ⟨m, hmn⟩ ≠ σ k0 := by
          intro h
          have := σ.injective h
          have : k0.val = m := by rw [← this]
          omega
        have : ({σ ⟨m, hmn⟩, σ k0} : Finset (Fin n)) ⊆ insert (σ ⟨m, hmn⟩) S := by
          intro y hy
          simp only [Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with rfl | rfl
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem hk0S
        have := Finset.card_le_card this
        rw [Finset.card_pair hne] at this
        omega
      rw [if_neg hnot]
      simp only [hS, Finset.mem_map_equiv, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨Nat.lt_succ_of_lt h1, h2, h3⟩
      · rintro ⟨h1, h2, h3⟩
        refine ⟨?_, h2, h3⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 h1 with h | h
        · exact h
        · exfalso
          have := h2 j0 (by rw [Fin.lt_def, h]; exact hj0m)
          linarith

lemma mem_served_one (σ : Equiv.Perm (Fin n)) (p v : Fin n → ℝ) (k : Fin n) :
    σ k ∈ spmServed (uniformSystem (Fin n) 1) σ p v ↔
      (∀ j, j < k → v (σ j) < p (σ j)) ∧ p (σ k) ≤ v (σ k) := by
  rw [spmServed, served_one σ p v n le_rfl, Finset.mem_map_equiv]
  simp

lemma served_set_eq (σ : Equiv.Perm (Fin n)) (p : Fin n → ℝ) (k : Fin n) :
    {v : Fin n → ℝ | σ k ∈ spmServed (uniformSystem (Fin n) 1) σ p v} =
      univ.pi (fun i => if σ.symm i < k then Iio (p i) else if σ.symm i = k then Ici (p i)
        else univ) := by
  ext v
  simp only [mem_setOf_eq, mem_served_one, mem_pi, mem_univ, true_implies]
  constructor
  · rintro ⟨h1, h2⟩ i
    split_ifs with ha hb
    · have := h1 _ ha; simpa using this
    · rw [← hb] at h2; simpa using h2
    · trivial
  · intro h
    refine ⟨fun j hj => ?_, ?_⟩
    · have := h (σ j); simp only [Equiv.symm_apply_apply, if_pos hj] at this; exact this
    · have := h (σ k); simp only [Equiv.symm_apply_apply, lt_irrefl, if_false, if_true] at this
      exact this

theorem spm1_core (D : Fin n → ValueDist)
    (σ : Equiv.Perm (Fin n)) (p : Fin n → ℝ) :
    spmRevenue D (uniformSystem (Fin n) 1) σ p =
      ∑ k : Fin n, oneUnitOfferProb (fun j => 1 - (D (σ j)).cdf (p (σ j))) k *
        p (σ k) * (1 - (D (σ k)).cdf (p (σ k))) := by
  have hprob : ∀ k : Fin n, (prior D {v | σ k ∈ spmServed (uniformSystem (Fin n) 1) σ p v}).toReal
      = oneUnitOfferProb (fun j => 1 - (D (σ j)).cdf (p (σ j))) k *
        (1 - (D (σ k)).cdf (p (σ k))) := by
    intro k
    rw [served_set_eq, prior, Measure.pi_pi, ENNReal.toReal_prod,
      ← Equiv.prod_comp σ]
    simp only [Equiv.symm_apply_apply]
    have : ∀ j : Fin n, ((D (σ j)).law (if j < k then Iio (p (σ j)) else if j = k then
        Ici (p (σ j)) else univ)).toReal = if j < k then (D (σ j)).cdf (p (σ j)) else
        if j = k then 1 - (D (σ j)).cdf (p (σ j)) else 1 := by
      intro j
      split_ifs
      · exact SpmAux.law_Iio _ _
      · exact SpmAux.law_Ici _ _
      · simp
    simp_rw [this]
    rw [Finset.prod_ite, oneUnitOfferProb]
    congr 1
    · refine Finset.prod_congr rfl (fun j _ => by ring)
    · rw [Finset.prod_ite_eq']
      simp
  have hsum : ∀ v : Fin n → ℝ, ∑ i ∈ spmServed (uniformSystem (Fin n) 1) σ p v, p i =
      ∑ k : Fin n, {v | σ k ∈ spmServed (uniformSystem (Fin n) 1) σ p v}.indicator
        (fun _ => p (σ k)) v := by
    intro v
    have hA : spmServed (uniformSystem (Fin n) 1) σ p v =
        Finset.univ.filter (· ∈ spmServed (uniformSystem (Fin n) 1) σ p v) := by ext; simp
    rw [hA, Finset.sum_filter, ← Equiv.sum_comp σ]
    simp [Set.indicator]
  have hmeas : ∀ k : Fin n,
      MeasurableSet {v : Fin n → ℝ | σ k ∈ spmServed (uniformSystem (Fin n) 1) σ p v} := by
    intro k
    rw [served_set_eq]
    refine MeasurableSet.univ_pi (fun i => ?_)
    split_ifs
    · exact measurableSet_Iio
    · exact measurableSet_Ici
    · exact MeasurableSet.univ
  unfold spmRevenue
  simp_rw [hsum]
  rw [integral_finset_sum _ (fun k _ => (integrable_const _).indicator (hmeas k))]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [integral_indicator_const _ (hmeas k), measureReal_def, smul_eq_mul, hprob]
  ring

end CHMSPricing.SpmPartition

namespace CHMSPricing.SpmPartition
open MeasureTheory Set

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

lemma one_sub_exp_ge (Q : ℝ) (h0 : 0 ≤ Q) (h1 : Q ≤ 1) :
    (1 - Real.exp (-1)) * Q ≤ 1 - Real.exp (-Q) := by
  have hc := convexOn_exp.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ (-1:ℝ)) (by linarith : 0 ≤ 1 - Q) h0
    (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at hc
  have : Q * -1 = -Q := by ring
  rw [this] at hc
  nlinarith

lemma prod_le_exp (q : ℕ → ℝ) (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∀ k, q k ≤ 1) (m : ℕ) :
    ∏ k ∈ Finset.range m, (1 - q k) ≤ Real.exp (-∑ k ∈ Finset.range m, q k) := by
  rw [← Finset.sum_neg_distrib, Real.exp_sum]
  refine Finset.prod_le_prod (fun k _ => by linarith [hq1 k]) (fun k _ => ?_)
  have := Real.add_one_le_exp (-q k); linarith

lemma telesc (q : ℕ → ℝ) (m : ℕ) :
    ∑ k ∈ Finset.range m, (∏ j ∈ Finset.range k, (1 - q j)) * q k =
      1 - ∏ k ∈ Finset.range m, (1 - q k) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih, Finset.prod_range_succ]; ring

/-- the pure inequality, ℕ-indexed -/
lemma ineq_nat (a q : ℕ → ℝ) (ha : ∀ k, a (k+1) ≤ a k) (ha0 : ∀ k, 0 ≤ a k)
    (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∀ k, q k ≤ 1) (N : ℕ)
    (hsum : ∑ k ∈ Finset.range N, q k ≤ 1) :
    (1 - Real.exp (-1)) * ∑ k ∈ Finset.range N, a k * q k ≤
      ∑ k ∈ Finset.range N, (∏ j ∈ Finset.range k, (1 - q j)) * a k * q k := by
  have := abel_nonneg a (fun k => (∏ j ∈ Finset.range k, (1 - q j)) * q k -
    (1 - Real.exp (-1)) * q k) ha ha0 N (by
      intro m hm
      rw [Finset.sum_sub_distrib, telesc, ← Finset.mul_sum]
      have hQ0 : 0 ≤ ∑ k ∈ Finset.range m, q k := Finset.sum_nonneg (fun k _ => hq0 k)
      have hQ1 : ∑ k ∈ Finset.range m, q k ≤ 1 := le_trans
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hm)
          (fun k _ _ => hq0 k)) hsum
      have := one_sub_exp_ge _ hQ0 hQ1
      have := prod_le_exp q hq0 hq1 m
      linarith)
  rw [Finset.mul_sum]
  have e : ∀ k, a k * ((∏ j ∈ Finset.range k, (1 - q j)) * q k - (1 - Real.exp (-1)) * q k) =
      (∏ j ∈ Finset.range k, (1 - q j)) * a k * q k - (1 - Real.exp (-1)) * (a k * q k) := by
    intro k; ring
  simp_rw [e] at this
  rw [Finset.sum_sub_distrib] at this
  linarith


lemma sum_servProb_le {ι : Type*} [Fintype ι] [DecidableEq ι] (D : ι → ValueDist)
    (M : Mechanism ι) (hmeas : ∀ i, MeasurableSet {v | i ∈ M.alloc v}) (k : ℕ)
    (hk : ∀ v ∈ typeSpace D, (M.alloc v).card ≤ k) :
    ∑ i, servProb D M i ≤ k := by
  have e : ∀ i, servProb D M i = ∫ v, {v | i ∈ M.alloc v}.indicator (fun _ => (1:ℝ)) v ∂(prior D) := by
    intro i
    rw [integral_indicator_const _ (hmeas i), measureReal_def, smul_eq_mul, mul_one, servProb]
  simp_rw [e]
  rw [← integral_finset_sum _ (fun i _ => (integrable_const _).indicator (hmeas i))]
  have : ∫ v, (k:ℝ) ∂(prior D) = k := by simp
  rw [← this]
  refine integral_mono_ae (integrable_finset_sum _ (fun i _ => (integrable_const _).indicator (hmeas i)))
    (integrable_const _) ?_
  filter_upwards [ae_ts D] with v hv
  have : ∑ i, {v | i ∈ M.alloc v}.indicator (fun _ => (1:ℝ)) v = ((M.alloc v).card : ℝ) := by
    simp only [Set.indicator, mem_setOf_eq]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    congr 2; ext; simp
  rw [this]; exact_mod_cast hk v hv

variable {n : ℕ}

lemma offer_eq_range (g : Fin n → ℝ) (g' : ℕ → ℝ) (hg : ∀ j : Fin n, g j = g' j) (k : Fin n) :
    oneUnitOfferProb g k = ∏ j ∈ Finset.range k, (1 - g' j) := by
  rw [oneUnitOfferProb, Finset.prod_filter]
  have h1 : ∏ j : Fin n, (if j < k then 1 - g j else 1) =
      ∏ j : Fin n, (fun m : ℕ => if m < (k:ℕ) then 1 - g' m else 1) j :=
    Finset.prod_congr rfl (fun j _ => by simp only [Fin.lt_def, hg])
  rw [h1, Fin.prod_univ_eq_prod_range (fun m : ℕ => if m < (k:ℕ) then 1 - g' m else 1) n,
    ← Finset.prod_filter]
  congr 1; ext j; simp; omega

lemma final_ineq (S T : ℝ) (h : (1 - Real.exp (-1)) * S ≤ T) :
    S ≤ Real.exp 1 / (Real.exp 1 - 1) * T := by
  have he : 1 < Real.exp 1 := by
    have := Real.add_one_le_exp (1:ℝ)
    linarith
  have hinv : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; simp
  rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
  have h2 := mul_le_mul_of_nonneg_left h (Real.exp_pos 1).le
  have h3 : Real.exp 1 * ((1 - Real.exp (-1)) * S) = (Real.exp 1 - 1) * S := by
    linear_combination (-S) * hinv
  linarith

theorem approx_core (D : Fin n → ValueDist) (hreg : ∀ i, (D i).Regular) (kk : ℕ)
    (J : SetSystem (Fin n))
    (M : Mechanism (Fin n)) (hM : IsTruthful D J M)
    (hcard : ∀ v ∈ typeSpace D, (M.alloc v).card ≤ 1)
    (p : Fin n → ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (D i).lo (D i).hi ∧ (D i).cdf (p i) = 1 - servProb D M i)
    (σ : Equiv.Perm (Fin n)) (hσ : ∀ a b, a ≤ b → p (σ b) ≤ p (σ a)) :
    revenue D M ≤ Real.exp 1 / (Real.exp 1 - 1) * spmRevenue D (uniformSystem (Fin n) 1) σ p := by
  have hrev := rev_le_core D hreg J M hM p hp
  set q := servProb D M with hqdef
  let a' : ℕ → ℝ := fun k => if h : k < n then p (σ ⟨k, h⟩) else 0
  let qq : ℕ → ℝ := fun k => if h : k < n then q (σ ⟨k, h⟩) else 0
  have hp0 : ∀ i, 0 ≤ p i := fun i => (D i).lo_nonneg.trans (hp i).1.1
  have hq0 : ∀ i, 0 ≤ q i := fun i => ENNReal.toReal_nonneg
  have hq1 : ∀ i, q i ≤ 1 := fun i =>
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
  have hS : ∑ i, p i * q i = ∑ k ∈ Finset.range n, a' k * qq k := by
    rw [← Equiv.sum_comp σ, ← Fin.sum_univ_eq_sum_range (fun k => a' k * qq k)]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp [a', qq, k.isLt]
  have hT : spmRevenue D (uniformSystem (Fin n) 1) σ p =
      ∑ k ∈ Finset.range n, (∏ j ∈ Finset.range k, (1 - qq j)) * a' k * qq k := by
    rw [spm1_core, ← Fin.sum_univ_eq_sum_range
      (fun k => (∏ j ∈ Finset.range k, (1 - qq j)) * a' k * qq k)]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have h1 : ∀ i, 1 - (D i).cdf (p i) = q i := fun i => by rw [(hp i).2]; ring
    simp only [h1]
    rw [offer_eq_range (fun j => q (σ j)) qq (fun j => by simp [qq, j.isLt]) k]
    simp [a', qq, k.isLt]
  have hsum : ∑ k ∈ Finset.range n, qq k ≤ 1 := by
    rw [← Fin.sum_univ_eq_sum_range qq]
    have : ∑ k : Fin n, qq k = ∑ i, q i := by
      rw [show ∑ i, q i = ∑ k, q (σ k) from (Equiv.sum_comp σ q).symm]
      refine Finset.sum_congr rfl (fun k _ => ?_); simp [qq, k.isLt]
    rw [this]
    have := sum_servProb_le D M hM.alloc_measurable 1 hcard
    simpa using this
  have key := ineq_nat a' qq
    (by
      intro k
      simp only [a']
      by_cases h1 : k + 1 < n
      · rw [dif_pos h1, dif_pos (by omega : k < n)]
        exact hσ _ _ (Fin.mk_le_mk.2 (by omega))
      · rw [dif_neg h1]
        split_ifs
        · exact hp0 _
        · exact le_rfl)
    (by intro k; simp only [a']; split_ifs; exacts [hp0 _, le_rfl])
    (by intro k; simp only [qq]; split_ifs; exacts [hq0 _, le_rfl])
    (by intro k; simp only [qq]; split_ifs; exacts [hq1 _, zero_le_one])
    n hsum
  rw [hT]
  refine hrev.trans (final_ineq _ _ ?_)
  rw [hS]; exact key

end CHMSPricing.SpmPartition

open CHMSPricing.SpmPartition


theorem solution {n : ℕ}
    (D : Fin n → ValueDist) (hreg : ∀ i, (D i).Regular)
    (M : Mechanism (Fin n)) (hM : IsTruthful D (uniformSystem (Fin n) 1) M)
    (p : Fin n → ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (D i).lo (D i).hi ∧ (D i).cdf (p i) = 1 - servProb D M i)
    (σ : Equiv.Perm (Fin n)) (hσ : ∀ a b, a ≤ b → p (σ b) ≤ p (σ a)) :
    revenue D M ≤ Real.exp 1 / (Real.exp 1 - 1) * spmRevenue D (uniformSystem (Fin n) 1) σ p := by
  exact approx_core D hreg 0 _ M hM (fun v hv => hM.feasible v hv) p hp σ hσ
