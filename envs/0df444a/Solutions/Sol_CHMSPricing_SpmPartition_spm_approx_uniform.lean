-- Prove2me | solution 1 for CHMSPricing.SpmPartition.spm_approx_uniform
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T07:07:00.096659+00:00
-- url     : https://prove2.me/submissions/afc54af9-2227-4b9b-aeeb-5f65114ecda3

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

namespace CHMSPricing.SpmPartition
open MeasureTheory Set

namespace PartAux
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

end PartAux
end CHMSPricing.SpmPartition

namespace CHMSPricing.SpmPartition
open MeasureTheory Set

namespace PartAux
variable {n : ℕ}

lemma meas_A (J : SetSystem (Fin n)) (σ : Equiv.Perm (Fin n)) (p : Fin n → ℝ)
    (P : Finset (Fin n) → Prop) (k : ℕ) (hk : k ≤ n) :
    MeasurableSet {v : Fin n → ℝ | P (spmServedBefore J σ p v k)} := by
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

variable {β : Type*} [Fintype β] [DecidableEq β] (part : Fin n → β) (cap : β → ℕ)

lemma mem_succ_iff (σ : Equiv.Perm (Fin n)) (p v : Fin n → ℝ) (k : Fin n) :
    σ k ∈ spmServedBefore (partitionSystem part cap) σ p v (k.val+1) ↔
      p (σ k) ≤ v (σ k) ∧
      ((spmServedBefore (partitionSystem part cap) σ p v k.val).filter
        (fun i => part i = part (σ k))).card < cap (part (σ k)) := by
  set A := spmServedBefore (partitionSystem part cap) σ p v k.val with hA
  have hnot : σ k ∉ A := by
    rw [hA, A_mem _ σ p v k k.val k.isLt.le]; simp
  have hfeas := A_feas (partitionSystem part cap) σ p v k.val k.isLt.le
  rw [← hA] at hfeas
  have hkk : (⟨k.val, k.isLt⟩ : Fin n) = k := rfl
  rw [A_succ _ σ p v k.val k.isLt, hkk, ← hA]
  unfold spmStep
  have hF : (partitionSystem part cap).Feasible (insert (σ k) A) ↔
      (A.filter (fun i => part i = part (σ k))).card < cap (part (σ k)) := by
    change (∀ b, ((insert (σ k) A).filter (fun i => part i = b)).card ≤ cap b) ↔ _
    constructor
    · intro h
      have := h (part (σ k))
      rw [Finset.filter_insert, if_pos rfl, Finset.card_insert_of_notMem
        (fun hh => hnot (Finset.mem_filter.1 hh).1)] at this
      omega
    · intro h b
      rw [Finset.filter_insert]
      split_ifs with hb
      · rw [Finset.card_insert_of_notMem (fun hh => hnot (Finset.mem_filter.1 hh).1)]
        rw [← hb]; omega
      · exact hfeas b
  split_ifs with h
  · simp only [Finset.mem_insert, true_or, true_iff]
    exact ⟨h.2, hF.1 h.1⟩
  · simp only [hnot, false_iff]
    rintro ⟨h1, h2⟩
    exact h ⟨hF.2 h2, h1⟩

lemma count_eq (σ : Equiv.Perm (Fin n)) (p v : Fin n → ℝ) (b : β) (m : ℕ) (hm : m ≤ n) :
    ((spmServedBefore (partitionSystem part cap) σ p v m).filter (fun i => part i = b)).card =
      (Finset.univ.filter (fun j : Fin n => j.val < m ∧ part (σ j) = b ∧
        σ j ∈ spmServedBefore (partitionSystem part cap) σ p v (j.val+1))).card := by
  symm
  rw [← Finset.card_map σ.toEmbedding]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_map_equiv, Finset.mem_univ, true_and]
  have := A_mem (partitionSystem part cap) σ p v (σ.symm x) m hm
  simp only [Equiv.apply_symm_apply] at this
  rw [this]
  simp only [Equiv.apply_symm_apply]
  tauto

end PartAux
end CHMSPricing.SpmPartition

namespace CHMSPricing.SpmPartition
open MeasureTheory Set

namespace PartAux
variable {n : ℕ}
variable {β : Type*} [Fintype β] [DecidableEq β] (part : Fin n → β) (cap : β → ℕ)

/-- served-at-position set -/
def Sset (σ : Equiv.Perm (Fin n)) (p : Fin n → ℝ) (j : Fin n) : Set (Fin n → ℝ) :=
  {v | σ j ∈ spmServedBefore (partitionSystem part cap) σ p v (j.val+1)}

def Tset (σ : Equiv.Perm (Fin n)) (p : Fin n → ℝ) (k : Fin n) : Set (Fin n → ℝ) :=
  {v | ((spmServedBefore (partitionSystem part cap) σ p v k.val).filter
        (fun i => part i = part (σ k))).card < cap (part (σ k))}

lemma Sset_meas (σ : Equiv.Perm (Fin n)) (p : Fin n → ℝ) (j : Fin n) :
    MeasurableSet (Sset part cap σ p j) :=
  meas_A _ σ p (fun A => σ j ∈ A) _ j.isLt

lemma Tset_meas (σ : Equiv.Perm (Fin n)) (p : Fin n → ℝ) (k : Fin n) :
    MeasurableSet (Tset part cap σ p k) :=
  meas_A _ σ p (fun A => (A.filter (fun i => part i = part (σ k))).card < cap (part (σ k)))
    _ k.isLt.le

lemma indep (D : Fin n → ValueDist) (σ : Equiv.Perm (Fin n)) (p : Fin n → ℝ) (k : Fin n) :
    (prior D (Sset part cap σ p k)).toReal =
      ((D (σ k)).law (Ici (p (σ k)))).toReal * (prior D (Tset part cap σ p k)).toReal := by
  have hS := Sset_meas part cap σ p k
  have hT := Tset_meas part cap σ p k
  have hI : Integrable ((Sset part cap σ p k).indicator (1 : (Fin n → ℝ) → ℝ)) (prior D) :=
    (integrable_const (1:ℝ)).indicator hS
  rw [← measureReal_def, ← integral_indicator_one hS, integral_prior_update D (σ k) _ hI]
  have hTu : ∀ v x, (Function.update v (σ k) x ∈ Tset part cap σ p k ↔ v ∈ Tset part cap σ p k) := by
    intro v x
    simp only [Tset, mem_setOf_eq]
    rw [A_dep _ σ p (Function.update v (σ k) x) v k.val k.isLt.le (fun j hj => by
      have hne : σ j ≠ σ k := fun e => by
        have := σ.injective e; rw [this] at hj; exact lt_irrefl _ hj
      rw [Function.update_of_ne hne])]
  have hinner : ∀ v, ∫ x, (Sset part cap σ p k).indicator 1 (Function.update v (σ k) x)
      ∂(D (σ k)).law = (Tset part cap σ p k).indicator 1 v *
        ((D (σ k)).law (Ici (p (σ k)))).toReal := by
    intro v
    have : (fun x => (Sset part cap σ p k).indicator (1 : (Fin n → ℝ) → ℝ)
        (Function.update v (σ k) x)) =
        fun x => (Tset part cap σ p k).indicator 1 v * (Ici (p (σ k))).indicator 1 x := by
      funext x
      simp only [Set.indicator, Sset, mem_setOf_eq, mem_succ_iff, Function.update_self, mem_Ici,
        Pi.one_apply]
      have := hTu v x
      simp only [Tset, mem_setOf_eq] at this
      by_cases h1 : p (σ k) ≤ x <;> by_cases h2 : v ∈ Tset part cap σ p k <;>
        simp only [Tset, mem_setOf_eq] at h2 <;> simp [h1, h2, this, Tset]
    rw [this, integral_const_mul, integral_indicator_one measurableSet_Ici, measureReal_def]
  simp_rw [hinner]
  rw [integral_mul_const, integral_indicator_one hT, measureReal_def, mul_comm]

end PartAux
end CHMSPricing.SpmPartition

namespace CHMSPricing.SpmPartition
open MeasureTheory Set

namespace PartAux
variable {n : ℕ}
variable {β : Type*} [Fintype β] [DecidableEq β] (part : Fin n → β) (cap : β → ℕ)

lemma count_bounds (D : Fin n → ValueDist) (σ : Equiv.Perm (Fin n)) (p : Fin n → ℝ) (k : Fin n) :
    ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k.val ∧ part (σ j) = part (σ k)),
        (prior D (Sset part cap σ p j)).toReal ≤ cap (part (σ k)) ∧
    (cap (part (σ k)) : ℝ) * (1 - (prior D (Tset part cap σ p k)).toReal) ≤
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k.val ∧ part (σ j) = part (σ k)),
        (prior D (Sset part cap σ p j)).toReal := by
  set filt := Finset.univ.filter (fun j : Fin n => j.val < k.val ∧ part (σ j) = part (σ k))
  let f : (Fin n → ℝ) → ℝ := fun v => ∑ j ∈ filt, (Sset part cap σ p j).indicator (fun _ => (1:ℝ)) v
  have hfI : Integrable f (prior D) :=
    integrable_finset_sum _ (fun j _ => (integrable_const (1:ℝ)).indicator (Sset_meas part cap σ p j))
  have hfint : ∫ v, f v ∂(prior D) = ∑ j ∈ filt, (prior D (Sset part cap σ p j)).toReal := by
    rw [integral_finset_sum _ (fun j _ => (integrable_const (1:ℝ)).indicator (Sset_meas part cap σ p j))]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [integral_indicator_const _ (Sset_meas part cap σ p j), measureReal_def, smul_eq_mul, mul_one]
  have hfC : ∀ v, f v = (((spmServedBefore (partitionSystem part cap) σ p v k.val).filter
        (fun i => part i = (part (σ k)))).card : ℝ) := by
    intro v
    rw [count_eq part cap σ p v (part (σ k)) k.val k.isLt.le]
    simp only [f, Set.indicator, Sset, mem_setOf_eq]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.filter_filter]
    congr 2
    ext j; simp [and_assoc]
  constructor
  · rw [← hfint]
    have : ∫ v, (cap (part (σ k)) : ℝ) ∂(prior D) = cap (part (σ k)) := by simp
    rw [← this]
    refine integral_mono hfI (integrable_const _) (fun v => ?_)
    rw [hfC]
    have := A_feas (partitionSystem part cap) σ p v k.val k.isLt.le
    exact Nat.cast_le.mpr (this (part (σ k)))
  · rw [← hfint]
    have hTc : (cap (part (σ k)) : ℝ) * (1 - (prior D (Tset part cap σ p k)).toReal) =
        ∫ v, (Tset part cap σ p k)ᶜ.indicator (fun _ => (cap (part (σ k)) : ℝ)) v ∂(prior D) := by
      rw [integral_indicator_const _ (Tset_meas part cap σ p k).compl, measureReal_def,
        prob_compl_eq_one_sub (Tset_meas part cap σ p k), ENNReal.toReal_sub_of_le prob_le_one
        ENNReal.one_ne_top, smul_eq_mul]
      simp [mul_comm]
    rw [hTc]
    refine integral_mono ((integrable_const _).indicator (Tset_meas part cap σ p k).compl) hfI
      (fun v => ?_)
    rw [hfC]
    simp only [Set.indicator, mem_compl_iff, Tset, mem_setOf_eq]
    split_ifs with h <;> first | exact Nat.cast_nonneg _ | exact Nat.cast_le.mpr (by omega)

lemma rev_eq (D : Fin n → ValueDist) (σ : Equiv.Perm (Fin n)) (p : Fin n → ℝ) :
    spmRevenue D (partitionSystem part cap) σ p =
      ∑ k : Fin n, p (σ k) * (prior D (Sset part cap σ p k)).toReal := by
  have hsum : ∀ v : Fin n → ℝ, ∑ i ∈ spmServed (partitionSystem part cap) σ p v, p i =
      ∑ k : Fin n, (Sset part cap σ p k).indicator (fun _ => p (σ k)) v := by
    intro v
    have hA : spmServed (partitionSystem part cap) σ p v =
        Finset.univ.filter (· ∈ spmServed (partitionSystem part cap) σ p v) := by ext; simp
    rw [hA, Finset.sum_filter, ← Equiv.sum_comp σ]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [Set.indicator, Sset, mem_setOf_eq, spmServed]
    simp only [A_mem _ σ p v k n le_rfl, k.isLt, true_and]
  unfold spmRevenue
  simp_rw [hsum]
  rw [integral_finset_sum _ (fun k _ => (integrable_const _).indicator (Sset_meas part cap σ p k))]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [integral_indicator_const _ (Sset_meas part cap σ p k), measureReal_def, smul_eq_mul, mul_comm]

end PartAux
end CHMSPricing.SpmPartition

namespace CHMSPricing.SpmPartition
open MeasureTheory Set

namespace PartAux

lemma unit_decay (x y : ℕ → ℝ) (K : ℝ) (hK : 0 < K) (hx0 : ∀ k, 0 ≤ x k)
    (hy : ∀ k, x k * (1 - (∑ j ∈ Finset.range k, y j) / K) ≤ y k)
    (hG : ∀ k, ∑ j ∈ Finset.range k, y j ≤ K) (m : ℕ) :
    K - ∑ j ∈ Finset.range m, y j ≤ K * Real.exp (-(∑ j ∈ Finset.range m, x j) / K) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    set G := ∑ j ∈ Finset.range m, y j
    set X := ∑ j ∈ Finset.range m, x j
    have hU : 0 ≤ K - G := by linarith [hG m]
    have h1 : K - (G + y m) ≤ (K - G) * (1 - x m / K) := by
      have := hy m
      have e : x m * (1 - G / K) = (K - G) * (x m / K) := by field_simp
      nlinarith
    have h2 : (1 - x m / K) ≤ Real.exp (-(x m / K)) := by
      have := Real.add_one_le_exp (-(x m / K)); linarith
    have h3 : (K - G) * (1 - x m / K) ≤ (K - G) * Real.exp (-(x m / K)) :=
      mul_le_mul_of_nonneg_left h2 hU
    have h4 : (K - G) * Real.exp (-(x m / K)) ≤ K * Real.exp (-X / K) * Real.exp (-(x m / K)) :=
      mul_le_mul_of_nonneg_right ih (Real.exp_pos _).le
    have h5 : K * Real.exp (-X / K) * Real.exp (-(x m / K)) = K * Real.exp (-(X + x m) / K) := by
      rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    linarith

lemma part_ineq (a x y : ℕ → ℝ) (ha : ∀ k, a (k+1) ≤ a k) (ha0 : ∀ k, 0 ≤ a k)
    (K : ℝ) (hK : 0 ≤ K) (hx0 : ∀ k, 0 ≤ x k) (hy0 : ∀ k, 0 ≤ y k)
    (hy : ∀ k, x k * (1 - (∑ j ∈ Finset.range k, y j) / K) ≤ y k)
    (hG : ∀ k, ∑ j ∈ Finset.range k, y j ≤ K) (N : ℕ)
    (hsum : ∑ k ∈ Finset.range N, x k ≤ K) :
    (1 - Real.exp (-1)) * ∑ k ∈ Finset.range N, a k * x k ≤
      ∑ k ∈ Finset.range N, a k * y k := by
  have hpre : ∀ m ≤ N, (1 - Real.exp (-1)) * ∑ k ∈ Finset.range m, x k ≤
      ∑ k ∈ Finset.range m, y k := by
    intro m hm
    have hX0 : 0 ≤ ∑ k ∈ Finset.range m, x k := Finset.sum_nonneg (fun k _ => hx0 k)
    have hXK : ∑ k ∈ Finset.range m, x k ≤ K := le_trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hm)
        (fun k _ _ => hx0 k)) hsum
    have hY0 : 0 ≤ ∑ k ∈ Finset.range m, y k := Finset.sum_nonneg (fun k _ => hy0 k)
    rcases hK.lt_or_eq with hK | hK
    · have hd := unit_decay x y K hK hx0 hy hG m
      have hQ := one_sub_exp_ge ((∑ k ∈ Finset.range m, x k) / K) (div_nonneg hX0 hK.le)
        ((div_le_one hK).2 hXK)
      have e1 : K * ((1 - Real.exp (-1)) * ((∑ k ∈ Finset.range m, x k) / K)) =
          (1 - Real.exp (-1)) * ∑ k ∈ Finset.range m, x k := by field_simp
      have e2 : -(∑ k ∈ Finset.range m, x k) / K = -((∑ k ∈ Finset.range m, x k) / K) := by ring
      rw [e2] at hd
      have := mul_le_mul_of_nonneg_left hQ hK.le
      nlinarith
    · have : ∑ k ∈ Finset.range m, x k = 0 := le_antisymm (hK ▸ hXK) hX0
      rw [this, mul_zero]; exact hY0
  have := abel_nonneg a (fun k => y k - (1 - Real.exp (-1)) * x k) ha ha0 N (by
    intro m hm
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    linarith [hpre m hm])
  have e : ∀ k, a k * (y k - (1 - Real.exp (-1)) * x k) =
      a k * y k - (1 - Real.exp (-1)) * (a k * x k) := fun k => by ring
  simp_rw [e] at this
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at this
  linarith

lemma conv {n : ℕ} (g : Fin n → ℝ) (P : Fin n → Prop) [DecidablePred P] (k : ℕ) (hk : k ≤ n) :
    ∑ j ∈ Finset.range k, (if h : j < n then (if P ⟨j, h⟩ then g ⟨j, h⟩ else 0) else 0) =
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k ∧ P j), g j := by
  rw [Finset.sum_filter]
  let H : ℕ → ℝ := fun j => if h : j < n then (if j < k ∧ P ⟨j, h⟩ then g ⟨j, h⟩ else 0) else 0
  have e1 : ∑ j : Fin n, (if j.val < k ∧ P j then g j else 0) = ∑ j : Fin n, H j :=
    Finset.sum_congr rfl (fun j _ => by simp [H, j.isLt])
  rw [e1, Fin.sum_univ_eq_sum_range H n, ← Finset.sum_range_add_sum_Ico H hk]
  have e2 : ∑ j ∈ Finset.Ico k n, H j = 0 :=
    Finset.sum_eq_zero (fun j hj => by
      simp only [Finset.mem_Ico] at hj
      simp only [H]; split_ifs with h1 h2
      · omega
      · rfl
      · rfl)
  rw [e2, add_zero]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  simp only [Finset.mem_range] at hj
  simp only [H]
  split_ifs <;> first | rfl | (exfalso; tauto) | omega

end PartAux
end CHMSPricing.SpmPartition

namespace CHMSPricing.SpmPartition
open MeasureTheory Set

namespace PartAux
variable {n : ℕ}
variable {β : Type*} [Fintype β] [DecidableEq β] (part : Fin n → β) (cap : β → ℕ)

lemma count_total (D : Fin n → ValueDist) (σ : Equiv.Perm (Fin n)) (p : Fin n → ℝ) (b : β) :
    ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < n ∧ part (σ j) = b),
        (prior D (Sset part cap σ p j)).toReal ≤ cap b := by
  set filt := Finset.univ.filter (fun j : Fin n => j.val < n ∧ part (σ j) = b)
  let f : (Fin n → ℝ) → ℝ := fun v => ∑ j ∈ filt, (Sset part cap σ p j).indicator (fun _ => (1:ℝ)) v
  have hfI : Integrable f (prior D) :=
    integrable_finset_sum _ (fun j _ => (integrable_const (1:ℝ)).indicator (Sset_meas part cap σ p j))
  have hfint : ∫ v, f v ∂(prior D) = ∑ j ∈ filt, (prior D (Sset part cap σ p j)).toReal := by
    rw [integral_finset_sum _ (fun j _ => (integrable_const (1:ℝ)).indicator (Sset_meas part cap σ p j))]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [integral_indicator_const _ (Sset_meas part cap σ p j), measureReal_def, smul_eq_mul, mul_one]
  have hfC : ∀ v, f v = (((spmServedBefore (partitionSystem part cap) σ p v n).filter
        (fun i => part i = b)).card : ℝ) := by
    intro v
    rw [count_eq part cap σ p v b n le_rfl]
    simp only [f, Set.indicator, Sset, mem_setOf_eq]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.filter_filter]
    congr 2
    ext j; simp [filt, and_assoc]
  rw [← hfint]
  have : ∫ v, (cap b : ℝ) ∂(prior D) = cap b := by simp
  rw [← this]
  refine integral_mono hfI (integrable_const _) (fun v => ?_)
  rw [hfC]
  have := A_feas (partitionSystem part cap) σ p v n le_rfl
  exact Nat.cast_le.mpr (this b)

lemma sum_servProb_part {ι : Type*} [Fintype ι] [DecidableEq ι] (D : ι → ValueDist)
    (M : Mechanism ι) (hmeas : ∀ i, MeasurableSet {v | i ∈ M.alloc v}) (s : Finset ι) (k : ℕ)
    (hk : ∀ v ∈ typeSpace D, (s.filter (· ∈ M.alloc v)).card ≤ k) :
    ∑ i ∈ s, servProb D M i ≤ k := by
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
  have : ∑ i ∈ s, {v | i ∈ M.alloc v}.indicator (fun _ => (1:ℝ)) v =
      ((s.filter (· ∈ M.alloc v)).card : ℝ) := by
    simp only [Set.indicator, mem_setOf_eq]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [this]; exact_mod_cast hk v hv

theorem part_core (D : Fin n → ValueDist) (hreg : ∀ i, (D i).Regular)
    (M : Mechanism (Fin n)) (hM : IsTruthful D (partitionSystem part cap) M)
    (p : Fin n → ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (D i).lo (D i).hi ∧ (D i).cdf (p i) = 1 - servProb D M i)
    (σ : Equiv.Perm (Fin n)) (hσ : ∀ a b, a ≤ b → p (σ b) ≤ p (σ a)) :
    revenue D M ≤
      Real.exp 1 / (Real.exp 1 - 1) * spmRevenue D (partitionSystem part cap) σ p := by
  have hrev := rev_le_core D hreg _ M hM p hp
  set q := servProb D M with hqdef
  set s : Fin n → ℝ := fun k => (prior D (Sset part cap σ p k)).toReal with hsdef
  set π : Fin n → ℝ := fun k => (prior D (Tset part cap σ p k)).toReal with hπdef
  have hp0 : ∀ i, 0 ≤ p i := fun i => (D i).lo_nonneg.trans (hp i).1.1
  have hq0 : ∀ i, 0 ≤ q i := fun i => ENNReal.toReal_nonneg
  have hq1 : ∀ i, q i ≤ 1 := fun i =>
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
  have hs0 : ∀ k, 0 ≤ s k := fun k => ENNReal.toReal_nonneg
  have hπ1 : ∀ k, π k ≤ 1 := fun k =>
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
  have hsq : ∀ k, s k = q (σ k) * π k := by
    intro k
    simp only [hsdef, hπdef]
    rw [indep part cap D σ p k, SpmAux.law_Ici, (hp (σ k)).2]; ring
  have hcapq : ∀ b, ∑ i ∈ Finset.univ.filter (fun i => part i = b), q i ≤ cap b := by
    intro b
    refine sum_servProb_part D M hM.alloc_measurable _ _ (fun v hv => ?_)
    have := hM.feasible v hv b
    convert this using 2
    ext i; simp [and_comm]
  rw [rev_eq]
  refine hrev.trans (final_ineq _ _ ?_)
  rw [show ∑ i, p i * q i = ∑ k, p (σ k) * q (σ k) from (Equiv.sum_comp σ (fun i => p i * q i)).symm]
  rw [← Finset.sum_fiberwise Finset.univ (fun k => part (σ k)) (fun k => p (σ k) * q (σ k)),
    ← Finset.sum_fiberwise Finset.univ (fun k => part (σ k)) (fun k => p (σ k) * s k),
    Finset.mul_sum]
  refine Finset.sum_le_sum (fun b _ => ?_)
  -- ℕ-indexed data for part b
  let a' : ℕ → ℝ := fun k => if h : k < n then p (σ ⟨k, h⟩) else 0
  let x : ℕ → ℝ := fun k => if h : k < n then (if part (σ ⟨k, h⟩) = b then q (σ ⟨k, h⟩) else 0) else 0
  let y : ℕ → ℝ := fun k => if h : k < n then (if part (σ ⟨k, h⟩) = b then s ⟨k, h⟩ else 0) else 0
  have hfilt : ∀ (g : Fin n → ℝ), ∑ k ∈ Finset.univ.filter (fun k : Fin n => part (σ k) = b), g k =
      ∑ k ∈ Finset.univ.filter (fun j : Fin n => j.val < n ∧ part (σ j) = b), g k := by
    intro g; congr 1; ext j; simp [j.isLt]
  have hG : ∀ k, ∑ j ∈ Finset.range k, y j =
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < min k n ∧ part (σ j) = b), s j := by
    intro k
    rw [← conv s (fun j => part (σ j) = b) (min k n) (min_le_right _ _)]
    rcases le_total k n with hkn | hkn
    · rw [min_eq_left hkn]
    · rw [min_eq_right hkn, ← Finset.sum_range_add_sum_Ico _ hkn]
      have : ∑ j ∈ Finset.Ico n k, y j = 0 :=
        Finset.sum_eq_zero (fun j hj => by
          simp only [Finset.mem_Ico] at hj; simp only [y]; rw [dif_neg (by omega)])
      rw [this, add_zero]
  have hGle : ∀ k, ∑ j ∈ Finset.range k, y j ≤ cap b := by
    intro k
    rw [hG k]
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun j _ _ => hs0 j))
      (count_total part cap D σ p b)
    intro j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rintro ⟨h1, h2⟩; exact ⟨j.isLt, h2⟩
  have hsumx : ∑ k ∈ Finset.range n, x k ≤ cap b := by
    have : ∑ k ∈ Finset.range n, x k = ∑ i ∈ Finset.univ.filter (fun i => part i = b), q i := by
      rw [show (∑ k ∈ Finset.range n, x k) = ∑ k ∈ Finset.range n,
        (if h : k < n then (if part (σ ⟨k, h⟩) = b then q (σ ⟨k, h⟩) else 0) else 0) from rfl,
        conv (fun k => q (σ k)) (fun j => part (σ j) = b) n le_rfl, ← hfilt,
        Finset.sum_filter, Finset.sum_filter]
      exact Equiv.sum_comp σ (fun i => if part i = b then q i else 0)
    rw [this]; exact hcapq b
  have hcap0 : cap b = 0 → ∀ k : Fin n, part (σ k) = b → q (σ k) = 0 := by
    intro hc k hk
    have h1 := hcapq b
    rw [hc, Nat.cast_zero] at h1
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hq0 i)).1
      (le_antisymm h1 (Finset.sum_nonneg (fun i _ => hq0 i))) (σ k) (by simp [hk])
    exact h2
  have key := part_ineq a' x y
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
    (cap b) (Nat.cast_nonneg _)
    (by intro k; simp only [x]; split_ifs <;> first | exact hq0 _ | exact le_rfl)
    (by intro k; simp only [y]; split_ifs <;> first | exact hs0 _ | exact le_rfl)
    (by
      intro k
      simp only [x, y]
      split_ifs with hk hb
      · have hkk := (count_bounds part cap D σ p ⟨k, hk⟩).2
        rw [hb] at hkk
        rw [hG k, min_eq_left hk.le, hsq]
        rcases (Nat.cast_nonneg (α := ℝ) (cap b)).lt_or_eq with hc | hc
        · have : 1 - (∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k ∧ part (σ j) = b),
              s j) / (cap b) ≤ π ⟨k, hk⟩ := by
            rw [sub_le_iff_le_add, ← sub_le_iff_le_add', le_div_iff₀ hc]
            simp only [hsdef] at hkk ⊢
            linarith
          exact mul_le_mul_of_nonneg_left this (hq0 _)
        · have := hcap0 (by exact_mod_cast hc.symm) ⟨k, hk⟩ hb
          rw [this]; simp
      · simp
      · simp)
    hGle n hsumx
  have eL : ∑ k ∈ Finset.univ.filter (fun k : Fin n => part (σ k) = b), p (σ k) * q (σ k) =
      ∑ k ∈ Finset.range n, a' k * x k := by
    rw [hfilt, ← conv (fun k => p (σ k) * q (σ k)) (fun j => part (σ j) = b) n le_rfl]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [a', x]; split_ifs <;> simp
  have eR : ∑ k ∈ Finset.univ.filter (fun k : Fin n => part (σ k) = b), p (σ k) * s k =
      ∑ k ∈ Finset.range n, a' k * y k := by
    rw [hfilt, ← conv (fun k => p (σ k) * s k) (fun j => part (σ j) = b) n le_rfl]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [a', y]; split_ifs <;> simp
  rw [eL, eR]; exact key

end PartAux
end CHMSPricing.SpmPartition

namespace CHMSPricing.SpmPartition
namespace PartAux

lemma unif_eq {n : ℕ} (k : ℕ) :
    uniformSystem (Fin n) k = partitionSystem (fun _ : Fin n => ()) (fun _ => k) := by
  unfold uniformSystem partitionSystem
  congr 1
  funext S
  apply propext
  constructor
  · intro h b; simpa using h
  · intro h; simpa using h ()

theorem unif_core {n : ℕ}
    (D : Fin n → ValueDist) (hreg : ∀ i, (D i).Regular)
    (k : ℕ)
    (M : Mechanism (Fin n)) (hM : IsTruthful D (uniformSystem (Fin n) k) M)
    (p : Fin n → ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (D i).lo (D i).hi ∧ (D i).cdf (p i) = 1 - servProb D M i)
    (σ : Equiv.Perm (Fin n)) (hσ : ∀ a b, a ≤ b → p (σ b) ≤ p (σ a)) :
    revenue D M ≤ Real.exp 1 / (Real.exp 1 - 1) * spmRevenue D (uniformSystem (Fin n) k) σ p := by
  rw [unif_eq] at hM ⊢
  exact part_core _ _ D hreg M hM p hp σ hσ

end PartAux
end CHMSPricing.SpmPartition

open CHMSPricing.SpmPartition


theorem solution {n : ℕ}
    (D : Fin n → ValueDist) (hreg : ∀ i, (D i).Regular)
    (k : ℕ)
    (M : Mechanism (Fin n)) (hM : IsTruthful D (uniformSystem (Fin n) k) M)
    (p : Fin n → ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (D i).lo (D i).hi ∧ (D i).cdf (p i) = 1 - servProb D M i)
    (σ : Equiv.Perm (Fin n)) (hσ : ∀ a b, a ≤ b → p (σ b) ≤ p (σ a)) :
    revenue D M ≤ Real.exp 1 / (Real.exp 1 - 1) * spmRevenue D (uniformSystem (Fin n) k) σ p := by
  exact CHMSPricing.SpmPartition.PartAux.unif_core D hreg k M hM p hp σ hσ
