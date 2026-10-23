-- Prove2me | solution 1 for CHMSPricing.UnitDemand.two_partition_opm_approx
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T07:30:53.680309+00:00
-- url     : https://prove2.me/submissions/dc2a8276-cc7d-47b3-b4a4-c55e2f413481

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

open MeasureTheory

theorem law_prob (D : ValueDist) : IsProbabilityMeasure D.law := by
  constructor
  unfold ValueDist.law
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hint : IntegrableOn D.f (Set.Icc D.lo D.hi) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le D.lo_lt_hi.le).1 D.f_intervalIntegrable
  rw [← ofReal_integral_eq_lintegral_ofReal hint]
  · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le D.lo_lt_hi.le,
      D.f_integral]
    simp
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx using (D.f_pos x hx).le

theorem law_singleton (D : ValueDist) (x : ℝ) : D.law {x} = 0 := by
  unfold ValueDist.law
  apply withDensity_absolutelyContinuous
  rw [Measure.restrict_apply (measurableSet_singleton x)]
  exact measure_mono_null Set.inter_subset_left (Real.volume_singleton)

theorem law_split (D : ValueDist) (x : ℝ) :
    (D.law (Set.Iio x)).toReal + (D.law (Set.Ici x)).toReal = 1 ∧
    D.cdf x = (D.law (Set.Iio x)).toReal := by
  haveI := law_prob D
  constructor
  · have h1 : D.law (Set.Iio x) + D.law (Set.Ici x) = 1 := by
      rw [← Set.compl_Iio, measure_add_measure_compl measurableSet_Iio, measure_univ]
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), h1]; simp
  · unfold ValueDist.cdf
    rw [← Set.Iio_insert, Set.insert_eq, measure_union (by simp) measurableSet_Iio,
      law_singleton, zero_add]

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (D : ι → ValueDist) (p : ι → ℝ)

noncomputable def qq (j : ι) : ℝ := ((D j).law (Set.Ici (p j))).toReal

noncomputable def mu (S : Finset ι) : ℝ := ∏ j, (if j ∈ S then qq D p j else 1 - qq D p j)

theorem qq_eq (j : ι) : qq D p j = 1 - (D j).cdf (p j) := by
  obtain ⟨h1, h2⟩ := law_split (D j) (p j)
  unfold qq; linarith

theorem qq_nonneg (j : ι) : 0 ≤ qq D p j := ENNReal.toReal_nonneg

theorem qq_le (j : ι) : qq D p j ≤ 1 := by
  obtain ⟨h1, _⟩ := law_split (D j) (p j)
  unfold qq; linarith [ENNReal.toReal_nonneg (a := (D j).law (Set.Iio (p j)))]

theorem mu_nonneg (S : Finset ι) : 0 ≤ mu D p S := by
  unfold mu
  apply Finset.prod_nonneg
  intro j _
  split_ifs
  · exact qq_nonneg D p j
  · linarith [qq_le D p j]

theorem fiber_eq (S : Finset ι) : {v : ι → ℝ | desiring p v = S} =
    Set.pi Set.univ (fun j => if j ∈ S then Set.Ici (p j) else Set.Iio (p j)) := by
  ext v
  simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies, Finset.ext_iff, desiring,
    Finset.mem_filter, Finset.mem_univ, true_and]
  apply forall_congr'
  intro j
  split_ifs with hj <;> simp [hj]

theorem fiber_meas (S : Finset ι) : MeasurableSet {v : ι → ℝ | desiring p v = S} := by
  rw [fiber_eq]
  apply MeasurableSet.univ_pi
  intro j
  split_ifs
  · exact measurableSet_Ici
  · exact measurableSet_Iio

theorem prior_fiber (S : Finset ι) : (prior D {v | desiring p v = S}).toReal = mu D p S := by
  haveI := fun j => law_prob (D j)
  rw [fiber_eq]
  unfold prior
  rw [Measure.pi_pi, ENNReal.toReal_prod]
  unfold mu
  apply Finset.prod_congr rfl
  intro j _
  split_ifs
  · rfl
  · obtain ⟨h1, _⟩ := law_split (D j) (p j)
    unfold qq; linarith

theorem prior_pred (P : Finset ι → Prop) [DecidablePred P] :
    (prior D {v | P (desiring p v)}).toReal = ∑ S, mu D p S * (if P S then 1 else 0) := by
  haveI := fun j => law_prob (D j)
  haveI : IsProbabilityMeasure (prior D) := by unfold prior; infer_instance
  have hset : {v : ι → ℝ | P (desiring p v)} =
      ⋃ S ∈ Finset.univ.filter P, {v | desiring p v = S} := by
    ext v; simp
  rw [hset, measure_biUnion_finset]
  · rw [ENNReal.toReal_sum (fun S _ => measure_ne_top _ _)]
    simp only [prior_fiber, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_filter]
  · intro a _ b _ hab
    rw [Function.onFun, Set.disjoint_left]
    intro v ha hb
    exact hab (ha.symm.trans hb)
  · intro S _; exact fiber_meas p S

theorem mu_sum : ∑ S, mu D p S = 1 := by
  haveI := fun j => law_prob (D j)
  have := prior_pred D p (fun _ => True)
  simp only [Set.setOf_true, if_true, mul_one] at this
  rw [← this]
  unfold prior; simp

theorem mu_marg (j : ι) : ∑ S, mu D p S * (if j ∈ S then 1 else 0) = qq D p j := by
  haveI := fun j => law_prob (D j)
  rw [← prior_pred D p (fun S => j ∈ S)]
  have hset : {v : ι → ℝ | j ∈ desiring p v} =
      Set.pi Set.univ (Function.update (fun _ => Set.univ) j (Set.Ici (p j))) := by
    ext v
    simp only [Set.mem_setOf_eq, desiring, Finset.mem_filter, Finset.mem_univ, true_and,
      Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro h k
      by_cases hk : k = j
      · subst hk; simpa using h
      · simp [Function.update_of_ne hk]
    · intro h; simpa using h j
  rw [hset]
  unfold prior
  rw [Measure.pi_pi, Finset.prod_eq_single j]
  · simp [qq]
  · intro k _ hk; simp [Function.update_of_ne hk]
  · simp

theorem mu_mul (a b : Finset ι) : mu D p a * mu D p b = mu D p (a ∩ b) * mu D p (a ∪ b) := by
  unfold mu
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  by_cases ha : j ∈ a <;> by_cases hb : j ∈ b <;> simp [ha, hb, mul_comm]

/-- Markov: the probability (under `mu`) that at least `k` members of `T` lie in `S`. -/
theorem markov (T : Finset ι) (k : ℕ) (hk : 1 ≤ k) (hT : ∑ j ∈ T, qq D p j ≤ (k : ℝ) / 3) :
    (2 / 3 : ℝ) ≤ ∑ S, mu D p S * (if (S.filter (· ∈ T)).card ≤ k - 1 then 1 else 0) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hpt : ∀ S : Finset ι, (if (S.filter (· ∈ T)).card ≤ k - 1 then (1 : ℝ) else 0) ≥
      1 - ((S.filter (· ∈ T)).card : ℝ) / k := by
    intro S
    split_ifs with h
    · have : (0 : ℝ) ≤ ((S.filter (· ∈ T)).card : ℝ) / k := by positivity
      linarith
    · have h' : k ≤ (S.filter (· ∈ T)).card := by omega
      have : (k : ℝ) ≤ (S.filter (· ∈ T)).card := by exact_mod_cast h'
      rw [ge_iff_le, sub_nonpos, le_div_iff₀ hkpos]; linarith
  have hcard : ∀ S : Finset ι, ((S.filter (· ∈ T)).card : ℝ) =
      ∑ j ∈ T, (if j ∈ S then 1 else 0) := by
    intro S
    rw [Finset.sum_boole]
    congr 2
    ext j; simp [and_comm]
  have hexp : ∑ S, mu D p S * ((S.filter (· ∈ T)).card : ℝ) = ∑ j ∈ T, qq D p j := by
    simp only [hcard, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    exact mu_marg D p j
  calc (2 / 3 : ℝ) ≤ 1 - (∑ j ∈ T, qq D p j) / k := by
        have : (∑ j ∈ T, qq D p j) / k ≤ 1 / 3 := by
          rw [div_le_iff₀ hkpos]; linarith
        linarith
    _ = ∑ S, mu D p S * (1 - ((S.filter (· ∈ T)).card : ℝ) / k) := by
        simp only [mul_sub, Finset.sum_sub_distrib, mu_sum, mul_div_assoc', ← Finset.sum_div, hexp,
          mul_one]
    _ ≤ _ := by
        apply Finset.sum_le_sum
        intro S _
        exact mul_le_mul_of_nonneg_left (hpt S) (mu_nonneg D p S)

theorem harris (f g : Finset ι → ℝ) (hf0 : 0 ≤ f) (hg0 : 0 ≤ g) (hf : Antitone f) (hg : Antitone g) :
    (∑ S, mu D p S * f S) * (∑ S, mu D p S * g S) ≤ ∑ S, mu D p S * (f S * g S) := by
  have := fkg (α := (Finset ι)ᵒᵈ) (μ := fun a => mu D p (OrderDual.ofDual a))
    (f := fun a => f (OrderDual.ofDual a)) (g := fun a => g (OrderDual.ofDual a))
    (fun a => mu_nonneg D p _) (fun a => hf0 _) (fun a => hg0 _)
    (fun a b h => hf h) (fun a b h => hg h)
    (fun a b => by
      rw [mu_mul D p (OrderDual.ofDual a) (OrderDual.ofDual b)]
      show _ ≤ mu D p (OrderDual.ofDual a ∪ OrderDual.ofDual b) * mu D p (OrderDual.ofDual a ∩ OrderDual.ofDual b)
      rw [mul_comm])
  have hs : ∑ a : (Finset ι)ᵒᵈ, mu D p (OrderDual.ofDual a) = 1 := mu_sum D p
  rw [hs, one_mul] at this
  exact this

end

theorem hT_lem {ι β : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq β] (D : ι → ValueDist)
    (p : ι → ℝ) (i : ι) (part : ι → β) (cap : β → ℕ)
    (h : ∀ b, ∑ i' ∈ Finset.univ.filter (fun i' => part i' = b), (1 - (D i').cdf (p i'))
        ≤ (cap b : ℝ) / 3) :
    ∑ j ∈ Finset.univ.filter (fun i' => i' ≠ i ∧ part i' = part i), qq D p j ≤ (cap (part i) : ℝ) / 3 := by
  refine le_trans ?_ (h (part i))
  simp only [← qq_eq]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx; simp only [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, hx.2.2⟩
  · intro j _ _; exact qq_nonneg D p j

theorem cp_core {ι β₁ β₂ : Type*} [Fintype ι] [DecidableEq ι]
    [DecidableEq β₁] [DecidableEq β₂]
    (D : ι → ValueDist) (part₁ : ι → β₁) (cap₁ : β₁ → ℕ) (part₂ : ι → β₂) (cap₂ : β₂ → ℕ)
    (p : ι → ℝ)
    (hq₁ : ∀ b, ∑ i' ∈ Finset.univ.filter (fun i' => part₁ i' = b), (1 - (D i').cdf (p i'))
      ≤ (cap₁ b : ℝ) / 3)
    (hq₂ : ∀ b, ∑ i' ∈ Finset.univ.filter (fun i' => part₂ i' = b), (1 - (D i').cdf (p i'))
      ≤ (cap₂ b : ℝ) / 3)
    (i : ι) (hk₁ : 1 ≤ cap₁ (part₁ i)) (hk₂ : 1 ≤ cap₂ (part₂ i)) :
    (4 / 9 : ℝ) ≤ (prior D {v |
      ((desiring p v).filter (fun i' => i' ≠ i ∧ part₁ i' = part₁ i)).card ≤ cap₁ (part₁ i) - 1 ∧
      ((desiring p v).filter (fun i' => i' ≠ i ∧ part₂ i' = part₂ i)).card ≤ cap₂ (part₂ i) - 1}).toReal := by
  classical
  set T₁ := Finset.univ.filter (fun i' => i' ≠ i ∧ part₁ i' = part₁ i)
  set T₂ := Finset.univ.filter (fun i' => i' ≠ i ∧ part₂ i' = part₂ i)
  have e1 : ∀ S : Finset ι, S.filter (fun i' => i' ≠ i ∧ part₁ i' = part₁ i) = S.filter (· ∈ T₁) := by
    intro S; ext x; simp [T₁]
  have e2 : ∀ S : Finset ι, S.filter (fun i' => i' ≠ i ∧ part₂ i' = part₂ i) = S.filter (· ∈ T₂) := by
    intro S; ext x; simp [T₂]
  have m1 := markov D p T₁ _ hk₁ (hT_lem D p i part₁ cap₁ hq₁)
  have m2 := markov D p T₂ _ hk₂ (hT_lem D p i part₂ cap₂ hq₂)
  have hP := prior_pred D p (fun S => (S.filter (· ∈ T₁)).card ≤ cap₁ (part₁ i) - 1 ∧
    (S.filter (· ∈ T₂)).card ≤ cap₂ (part₂ i) - 1)
  have hsetEq : {v : ι → ℝ |
      ((desiring p v).filter (fun i' => i' ≠ i ∧ part₁ i' = part₁ i)).card ≤ cap₁ (part₁ i) - 1 ∧
      ((desiring p v).filter (fun i' => i' ≠ i ∧ part₂ i' = part₂ i)).card ≤ cap₂ (part₂ i) - 1} =
      {v | ((desiring p v).filter (· ∈ T₁)).card ≤ cap₁ (part₁ i) - 1 ∧
        ((desiring p v).filter (· ∈ T₂)).card ≤ cap₂ (part₂ i) - 1} := by
    simp only [e1, e2]
  rw [hsetEq, hP]
  have H := harris D p (fun S => if (S.filter (· ∈ T₁)).card ≤ cap₁ (part₁ i) - 1 then 1 else 0)
    (fun S => if (S.filter (· ∈ T₂)).card ≤ cap₂ (part₂ i) - 1 then 1 else 0)
    (fun S => by simp only [Pi.zero_apply]; split_ifs <;> norm_num)
    (fun S => by simp only [Pi.zero_apply]; split_ifs <;> norm_num)
    (fun a b hab => by
      have : (a.filter (· ∈ T₁)).card ≤ (b.filter (· ∈ T₁)).card :=
        Finset.card_le_card (Finset.filter_subset_filter _ hab)
      simp only; split_ifs <;> first | (exfalso; rename_i h1 h2; exact h2 (this.trans h1)) | norm_num)
    (fun a b hab => by
      have : (a.filter (· ∈ T₂)).card ≤ (b.filter (· ∈ T₂)).card :=
        Finset.card_le_card (Finset.filter_subset_filter _ hab)
      simp only; split_ifs <;> first | (exfalso; rename_i h1 h2; exact h2 (this.trans h1)) | norm_num)
  have hprod : (4 / 9 : ℝ) ≤ (∑ S, mu D p S * (if (S.filter (· ∈ T₁)).card ≤ cap₁ (part₁ i) - 1 then 1 else 0)) *
      (∑ S, mu D p S * (if (S.filter (· ∈ T₂)).card ≤ cap₂ (part₂ i) - 1 then 1 else 0)) := by
    have := mul_le_mul m1 m2 (by norm_num) (by linarith)
    linarith
  refine hprod.trans (H.trans (le_of_eq ?_))
  apply Finset.sum_congr rfl
  intro S _
  by_cases hA : (S.filter (· ∈ T₁)).card ≤ cap₁ (part₁ i) - 1 <;>
    by_cases hB : (S.filter (· ∈ T₂)).card ≤ cap₂ (part₂ i) - 1 <;> simp [hA, hB]

end CHMSPricing.UnitDemand

namespace CHMSPricing.UnitDemand
open MeasureTheory Set

namespace TPAux

variable (D : ValueDist)

lemma f_intOn' : IntegrableOn D.f (Icc D.lo D.hi) :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le D.lo_lt_hi.le).1 D.f_intervalIntegrable

lemma law_apply (s : Set ℝ) (hs : MeasurableSet s) :
    D.law s = ENNReal.ofReal (∫ x in Icc D.lo D.hi ∩ s, D.f x) := by
  rw [ValueDist.law, withDensity_apply _ hs, Measure.restrict_restrict hs, Set.inter_comm s]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · exact (f_intOn' D).mono_set inter_subset_left
  · filter_upwards [ae_restrict_mem (measurableSet_Icc.inter hs)] with x hx
    exact (D.f_pos x hx.1).le

lemma cdf_eq (x : ℝ) (hx : x ∈ Icc D.lo D.hi) : D.cdf x = ∫ t in D.lo..x, D.f t := by
  unfold ValueDist.cdf
  rw [law_apply D _ measurableSet_Iic]
  have h : Icc D.lo D.hi ∩ Iic x = Icc D.lo x := by
    ext t
    simp only [mem_inter_iff, mem_Icc, mem_Iic]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨h1, h3.trans hx.2⟩, h3⟩
  rw [h, ENNReal.toReal_ofReal, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le hx.1]
  exact setIntegral_nonneg measurableSet_Icc
    (fun t ht => (D.f_pos t ⟨ht.1, ht.2.trans hx.2⟩).le)

lemma cdf_contOn : ContinuousOn D.cdf (Icc D.lo D.hi) := by
  have h1 : IntegrableOn D.f (uIcc D.lo D.hi) := by
    rw [uIcc_of_le D.lo_lt_hi.le]; exact f_intOn' D
  have := intervalIntegral.continuousOn_primitive_interval (μ := volume) h1
  rw [uIcc_of_le D.lo_lt_hi.le] at this
  exact this.congr (fun x hx => cdf_eq D x hx)

lemma cdf_lo : D.cdf D.lo = 0 := by
  rw [cdf_eq D D.lo ⟨le_rfl, D.lo_lt_hi.le⟩, intervalIntegral.integral_same]

lemma cdf_hi : D.cdf D.hi = 1 := by
  rw [cdf_eq D D.hi ⟨D.lo_lt_hi.le, le_rfl⟩, D.f_integral]

lemma exists_cdf_eq (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ∃ t ∈ Icc D.lo D.hi, D.cdf t = 1 - q := by
  have h := intermediate_value_Icc D.lo_lt_hi.le (cdf_contOn D)
  have hmem : 1 - q ∈ Icc (D.cdf D.lo) (D.cdf D.hi) := by
    rw [cdf_lo, cdf_hi]; constructor <;> linarith
  obtain ⟨t, ht, hte⟩ := h hmem
  exact ⟨t, ht, hte⟩

lemma cdf_mono' : Monotone D.cdf := fun x y h => by
  unfold ValueDist.cdf
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Iic_subset_Iic.2 h))

lemma cdf_nonneg (x : ℝ) : 0 ≤ D.cdf x := ENNReal.toReal_nonneg

lemma cdf_le_one (x : ℝ) : D.cdf x ≤ 1 := by
  unfold ValueDist.cdf
  have := ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := D.law) (s := Iic x))
  simpa using this

end TPAux

section TP
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma ind_integrable (D : ι → ValueDist) (P : (ι → ℝ) → Prop) [DecidablePred P]
    (hs : MeasurableSet {v | P v}) :
    Integrable (fun v => if P v then (1 : ℝ) else 0) (prior D) := by
  have := (integrable_const (1 : ℝ) (μ := prior D)).indicator hs
  refine this.congr (Filter.Eventually.of_forall fun v => ?_)
  by_cases h : P v <;> simp [Set.indicator_apply, h]

lemma servProb_eq (D : ι → ValueDist) (M : Mechanism ι)
    (hM : ∀ i, MeasurableSet {v | i ∈ M.alloc v}) (i : ι) :
    servProb D M i = ∫ v, (if i ∈ M.alloc v then (1 : ℝ) else 0) ∂(prior D) := by
  unfold servProb
  rw [← measureReal_def, ← integral_indicator_one (hM i)]
  congr 1
  funext v
  by_cases h : i ∈ M.alloc v <;> simp [Set.indicator_apply, h]

lemma servProb_nonneg (D : ι → ValueDist) (M : Mechanism ι) (i : ι) : 0 ≤ servProb D M i :=
  ENNReal.toReal_nonneg

lemma servProb_le_one (D : ι → ValueDist) (M : Mechanism ι) (i : ι) : servProb D M i ≤ 1 := by
  unfold servProb
  have := ENNReal.toReal_mono ENNReal.one_ne_top
    (prob_le_one (μ := prior D) (s := {v | i ∈ M.alloc v}))
  simpa using this

lemma sum_servProb_le (D : ι → ValueDist) {β : Type*} [DecidableEq β] (part : ι → β)
    (cap : β → ℕ) (J : SetSystem ι)
    (hJ : ∀ S, J.Feasible S → (partitionSystem part cap).Feasible S)
    (M : Mechanism ι) (hM : IsTruthful D J M) (b : β) :
    ∑ i ∈ Finset.univ.filter (fun i => part i = b), servProb D M i ≤ cap b := by
  simp_rw [servProb_eq D M hM.alloc_measurable]
  have hint : ∀ i, Integrable (fun v => if i ∈ M.alloc v then (1 : ℝ) else 0) (prior D) :=
    fun i => ind_integrable D _ (hM.alloc_measurable i)
  rw [← integral_finset_sum _ (fun i _ => hint i)]
  have hle : ∀ᵐ v ∂(prior D), ∑ i ∈ Finset.univ.filter (fun i => part i = b),
      (if i ∈ M.alloc v then (1 : ℝ) else 0) ≤ (cap b : ℝ) := by
    filter_upwards [ae_ts D] with v hv
    have hf := hJ _ (hM.feasible v hv) b
    calc ∑ i ∈ Finset.univ.filter (fun i => part i = b), (if i ∈ M.alloc v then (1 : ℝ) else 0)
        = (((M.alloc v).filter (fun i => part i = b)).card : ℝ) := by
          rw [Finset.sum_boole]
          congr 2
          ext i; simp [and_comm]
      _ ≤ cap b := by exact_mod_cast hf
  calc _ ≤ ∫ v, (cap b : ℝ) ∂(prior D) :=
        integral_mono_ae (integrable_finset_sum _ (fun i _ => hint i)) (integrable_const _) hle
    _ = cap b := by simp

lemma indep (D : ι → ValueDist) (p : ι → ℝ) (i : ι) (E : Finset ι → Prop) [DecidablePred E]
    (hE : ∀ S, E (S.erase i) ↔ E S) :
    ∑ S, mu D p S * (if i ∈ S ∧ E S then 1 else 0) =
      qq D p i * ∑ S, mu D p S * (if E S then 1 else 0) := by
  classical
  set w : Finset ι → ℝ :=
    fun S => ∏ j ∈ Finset.univ.erase i, (if j ∈ S then qq D p j else 1 - qq D p j) with hw
  have hmu : ∀ S, mu D p S = (if i ∈ S then qq D p i else 1 - qq D p i) * w S := by
    intro S
    unfold mu
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  have hwe : ∀ S, w (S.erase i) = w S := by
    intro S
    apply Finset.prod_congr rfl
    intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    simp [Finset.mem_erase, hji]
  have key : ∑ S ∈ Finset.univ.filter (fun S => i ∈ S), w S * (if E S then 1 else 0)
      = ∑ S ∈ Finset.univ.filter (fun S => i ∉ S), w S * (if E S then 1 else 0) := by
    apply Finset.sum_nbij' (fun S => S.erase i) (fun S => insert i S)
    · intro S _
      simp
    · intro S _
      simp
    · intro S hS
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
      exact Finset.insert_erase hS
    · intro S hS
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
      exact Finset.erase_insert hS
    · intro S _
      rw [hwe]
      congr 1
      simp only [hE]
  have lhs : ∑ S, mu D p S * (if i ∈ S ∧ E S then 1 else 0) =
      qq D p i * ∑ S ∈ Finset.univ.filter (fun S => i ∈ S), w S * (if E S then 1 else 0) := by
    rw [Finset.mul_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro S _
    rw [hmu S]
    by_cases hi : i ∈ S
    · simp [hi, mul_assoc]
    · simp [hi]
  have rhs : ∑ S, mu D p S * (if E S then 1 else 0) =
      qq D p i * (∑ S ∈ Finset.univ.filter (fun S => i ∈ S), w S * (if E S then 1 else 0)) +
      (1 - qq D p i) * (∑ S ∈ Finset.univ.filter (fun S => i ∉ S), w S * (if E S then 1 else 0)) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun S => i ∈ S), Finset.mul_sum,
      Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro S hS
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
      rw [hmu S, if_pos hS, mul_assoc]
    · apply Finset.sum_congr rfl
      intro S hS
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
      rw [hmu S, if_neg hS, mul_assoc]
  rw [lhs, rhs, ← key]
  ring

lemma integral_comp_desiring (D : ι → ValueDist) (p : ι → ℝ) (h : Finset ι → ℝ) :
    ∫ v, h (desiring p v) ∂(prior D) = ∑ S, mu D p S * h S := by
  have e : ∀ v, h (desiring p v) =
      ∑ S, Set.indicator {v | desiring p v = S} (fun _ => h S) v := by
    intro v
    rw [Finset.sum_eq_single (desiring p v)]
    · simp
    · intro S _ hS
      exact Set.indicator_of_notMem (fun h' => hS (by simpa using h'.symm)) _
    · simp
  simp_rw [e]
  rw [integral_finset_sum _ (fun S _ => (integrable_const _).indicator (fiber_meas p S))]
  apply Finset.sum_congr rfl
  intro S _
  rw [integral_indicator_const _ (fiber_meas p S), measureReal_def, prior_fiber, smul_eq_mul]

lemma obl_ge (D : ι → ValueDist) (J : SetSystem ι) (p : ι → ℝ) (L : Finset ι → ℝ)
    (hL : ∀ v, ∀ S ∈ maxFeasDesiringSets J p v, L (desiring p v) ≤ ∑ i ∈ S, p i) :
    ∑ S, mu D p S * L S ≤ oblRevenue D J p := by
  classical
  let f := fun v => (maxFeasDesiringSets J p v).inf' (maxFeasDesiringSets_nonempty J p v)
      (fun S => ∑ i ∈ S, p i)
  have hcong : ∀ v w, desiring p v = desiring p w → f v = f w := by
    intro v w h
    have hs : maxFeasDesiringSets J p v = maxFeasDesiringSets J p w := by
      unfold maxFeasDesiringSets IsMaxFeasDesiring
      ext S
      simp only [Finset.mem_filter, Finset.mem_powerset, h]
    exact Finset.inf'_congr _ hs (fun _ _ => rfl)
  let g : Finset ι → ℝ := fun T => if h : ∃ w, desiring p w = T then f h.choose else L T
  have e : ∀ v, f v = g (desiring p v) := by
    intro v
    have h : ∃ w, desiring p w = desiring p v := ⟨v, rfl⟩
    simp only [g, dif_pos h]
    exact hcong _ _ h.choose_spec.symm
  have hg : ∀ T, L T ≤ g T := by
    intro T
    simp only [g]
    split_ifs with h
    · have hc := h.choose_spec
      have := hL h.choose
      rw [hc] at this
      exact Finset.le_inf' _ _ this
    · exact le_rfl
  unfold oblRevenue
  have e' : (fun v => (maxFeasDesiringSets J p v).inf' (maxFeasDesiringSets_nonempty J p v)
      (fun S => ∑ i ∈ S, p i)) = fun v => g (desiring p v) := funext e
  rw [e', integral_comp_desiring]
  apply Finset.sum_le_sum
  intro S _
  exact mul_le_mul_of_nonneg_left (hg S) (mu_nonneg D p S)

variable {β₁ β₂ : Type*} [DecidableEq β₁] [DecidableEq β₂]

/-- the event under which `i` is always considered (plus the cap conditions) -/
def Ev (part₁ : ι → β₁) (cap₁ : β₁ → ℕ) (part₂ : ι → β₂) (cap₂ : β₂ → ℕ) (i : ι)
    (S : Finset ι) : Prop :=
  ((S.filter (fun i' => i' ≠ i ∧ part₁ i' = part₁ i)).card ≤ cap₁ (part₁ i) - 1 ∧
    (S.filter (fun i' => i' ≠ i ∧ part₂ i' = part₂ i)).card ≤ cap₂ (part₂ i) - 1) ∧
  (1 ≤ cap₁ (part₁ i) ∧ 1 ≤ cap₂ (part₂ i))

lemma Ev_erase (part₁ : ι → β₁) (cap₁ : β₁ → ℕ) (part₂ : ι → β₂) (cap₂ : β₂ → ℕ) (i : ι)
    (S : Finset ι) :
    Ev part₁ cap₁ part₂ cap₂ i (S.erase i) ↔ Ev part₁ cap₁ part₂ cap₂ i S := by
  unfold Ev
  have h1 : (S.erase i).filter (fun i' => i' ≠ i ∧ part₁ i' = part₁ i) =
      S.filter (fun i' => i' ≠ i ∧ part₁ i' = part₁ i) := by
    ext x; simp only [Finset.mem_filter, Finset.mem_erase]; tauto
  have h2 : (S.erase i).filter (fun i' => i' ≠ i ∧ part₂ i' = part₂ i) =
      S.filter (fun i' => i' ≠ i ∧ part₂ i' = part₂ i) := by
    ext x; simp only [Finset.mem_filter, Finset.mem_erase]; tauto
  rw [h1, h2]

lemma mem_of_Ev (part₁ : ι → β₁) (cap₁ : β₁ → ℕ) (part₂ : ι → β₂) (cap₂ : β₂ → ℕ)
    (p : ι → ℝ) (i : ι) (v : ι → ℝ)
    (hi : i ∈ desiring p v) (hE : Ev part₁ cap₁ part₂ cap₂ i (desiring p v)) (S : Finset ι)
    (hS : S ∈ maxFeasDesiringSets (twoPartitionSystem part₁ cap₁ part₂ cap₂) p v) : i ∈ S := by
  by_contra hn
  simp only [maxFeasDesiringSets, Finset.mem_filter, Finset.mem_powerset,
    IsMaxFeasDesiring] at hS
  obtain ⟨_, hsub, hfeas, hmax⟩ := hS
  obtain ⟨⟨hE1, hE2⟩, hk₁, hk₂⟩ := hE
  apply hmax i hi hn
  have hf1 : (partitionSystem part₁ cap₁).Feasible S := hfeas.1
  have hf2 : (partitionSystem part₂ cap₂).Feasible S := hfeas.2
  refine ⟨?_, ?_⟩
  · intro b
    by_cases hb : b = part₁ i
    · subst hb
      have : (insert i S).filter (fun x => part₁ x = part₁ i) =
          insert i (S.filter (fun x => part₁ x = part₁ i)) := by
        rw [Finset.filter_insert, if_pos rfl]
      rw [this, Finset.card_insert_of_notMem (by simp [hn])]
      have hsub2 : S.filter (fun x => part₁ x = part₁ i) ⊆
          (desiring p v).filter (fun i' => i' ≠ i ∧ part₁ i' = part₁ i) := by
        intro x hx
        simp only [Finset.mem_filter] at hx ⊢
        exact ⟨hsub hx.1, fun h => hn (h ▸ hx.1), hx.2⟩
      have := Finset.card_le_card hsub2
      omega
    · have : (insert i S).filter (fun x => part₁ x = b) = S.filter (fun x => part₁ x = b) := by
        rw [Finset.filter_insert, if_neg (Ne.symm hb)]
      rw [this]
      exact hf1 b
  · intro b
    by_cases hb : b = part₂ i
    · subst hb
      have : (insert i S).filter (fun x => part₂ x = part₂ i) =
          insert i (S.filter (fun x => part₂ x = part₂ i)) := by
        rw [Finset.filter_insert, if_pos rfl]
      rw [this, Finset.card_insert_of_notMem (by simp [hn])]
      have hsub2 : S.filter (fun x => part₂ x = part₂ i) ⊆
          (desiring p v).filter (fun i' => i' ≠ i ∧ part₂ i' = part₂ i) := by
        intro x hx
        simp only [Finset.mem_filter] at hx ⊢
        exact ⟨hsub hx.1, fun h => hn (h ▸ hx.1), hx.2⟩
      have := Finset.card_le_card hsub2
      omega
    · have : (insert i S).filter (fun x => part₂ x = b) = S.filter (fun x => part₂ x = b) := by
        rw [Finset.filter_insert, if_neg (Ne.symm hb)]
      rw [this]
      exact hf2 b

end TP
end CHMSPricing.UnitDemand

namespace CHMSPricing.UnitDemand
open MeasureTheory Set

section TPMain
variable {ι β₁ β₂ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq β₁] [DecidableEq β₂]

theorem tp_core (D : ι → ValueDist) (hreg : ∀ i, (D i).Regular)
    (part₁ : ι → β₁) (cap₁ : β₁ → ℕ) (part₂ : ι → β₂) (cap₂ : β₂ → ℕ) :
    ∃ p : ι → ℝ, ∀ M : Mechanism ι,
      IsTruthful D (twoPartitionSystem part₁ cap₁ part₂ cap₂) M →
        revenue D M ≤ (27 / 4 : ℝ) * oblRevenue D (twoPartitionSystem part₁ cap₁ part₂ cap₂) p := by
  classical
  set J := twoPartitionSystem part₁ cap₁ part₂ cap₂ with hJ
  let qf : (ι → ℝ) → ι → ℝ := fun t i => 1 - (D i).cdf (t i)
  let K := typeSpace D
  have hKc : IsCompact K := isCompact_univ_pi (fun i => isCompact_Icc)
  have hKcl : IsClosed K := isClosed_set_pi (fun i _ => isClosed_Icc)
  have hcont : ∀ i, ContinuousOn (fun t : ι → ℝ => (D i).cdf (t i)) K := by
    intro i
    refine (TPAux.cdf_contOn (D i)).comp (continuous_apply i).continuousOn ?_
    intro t ht
    exact ht i (mem_univ _)
  let C₁ : β₁ → Set (ι → ℝ) := fun b =>
    K ∩ {t | ∑ i ∈ Finset.univ.filter (fun i => part₁ i = b), qf t i ≤ (cap₁ b : ℝ)}
  have hC₁ : ∀ b, IsClosed (C₁ b) := by
    intro b
    have : ContinuousOn (fun t => ∑ i ∈ Finset.univ.filter (fun i => part₁ i = b), qf t i) K :=
      continuousOn_finset_sum _ (fun i _ => continuousOn_const.sub (hcont i))
    exact this.preimage_isClosed_of_isClosed hKcl isClosed_Iic
  let C₂ : β₂ → Set (ι → ℝ) := fun b =>
    K ∩ {t | ∑ i ∈ Finset.univ.filter (fun i => part₂ i = b), qf t i ≤ (cap₂ b : ℝ)}
  have hC₂ : ∀ b, IsClosed (C₂ b) := by
    intro b
    have : ContinuousOn (fun t => ∑ i ∈ Finset.univ.filter (fun i => part₂ i = b), qf t i) K :=
      continuousOn_finset_sum _ (fun i _ => continuousOn_const.sub (hcont i))
    exact this.preimage_isClosed_of_isClosed hKcl isClosed_Iic
  let Q := K ∩ ((⋂ b, C₁ b) ∩ (⋂ b, C₂ b))
  have hQcl : IsClosed Q := hKcl.inter ((isClosed_iInter hC₁).inter (isClosed_iInter hC₂))
  have hQc : IsCompact Q := hKc.of_isClosed_subset hQcl inter_subset_left
  have hQmem : ∀ t, t ∈ Q ↔ t ∈ K ∧
      (∀ b, ∑ i ∈ Finset.univ.filter (fun i => part₁ i = b), qf t i ≤ (cap₁ b : ℝ)) ∧
      (∀ b, ∑ i ∈ Finset.univ.filter (fun i => part₂ i = b), qf t i ≤ (cap₂ b : ℝ)) := by
    intro t
    simp only [Q, C₁, C₂, mem_inter_iff, mem_iInter, mem_setOf_eq]
    constructor
    · rintro ⟨hK, h1, h2⟩
      exact ⟨hK, fun b => (h1 b).2, fun b => (h2 b).2⟩
    · rintro ⟨hK, h1, h2⟩
      exact ⟨hK, fun b => ⟨hK, h1 b⟩, fun b => ⟨hK, h2 b⟩⟩
  have hQne : Q.Nonempty := by
    refine ⟨fun i => (D i).hi, (hQmem _).2 ⟨fun i _ => ⟨(D i).lo_lt_hi.le, le_rfl⟩, ?_, ?_⟩⟩
    · intro b
      simp only [qf, TPAux.cdf_hi, sub_self, Finset.sum_const_zero]
      exact Nat.cast_nonneg _
    · intro b
      simp only [qf, TPAux.cdf_hi, sub_self, Finset.sum_const_zero]
      exact Nat.cast_nonneg _
  let R : (ι → ℝ) → ℝ := fun t => ∑ i, t i * qf t i
  have hR : ContinuousOn R K :=
    continuousOn_finset_sum _ (fun i _ =>
      (continuous_apply i).continuousOn.mul (continuousOn_const.sub (hcont i)))
  obtain ⟨t, htQ, htmax⟩ := hQc.exists_isMaxOn hQne (hR.mono inter_subset_left)
  obtain ⟨htK, htc₁, htc₂⟩ := (hQmem t).1 htQ
  let q : ι → ℝ := fun i => qf t i
  have hq0 : ∀ i, 0 ≤ q i := fun i => by
    simp only [q, qf]; linarith [TPAux.cdf_le_one (D i) (t i)]
  have hq1 : ∀ i, q i ≤ 1 := fun i => by
    simp only [q, qf]; linarith [TPAux.cdf_nonneg (D i) (t i)]
  choose p hp using fun i => TPAux.exists_cdf_eq (D i) (q i / 3) (by linarith [hq0 i])
    (by linarith [hq1 i])
  have hp0 : ∀ i, 0 ≤ p i := fun i => (D i).lo_nonneg.trans (hp i).1.1
  have hqq : ∀ i, qq D p i = q i / 3 := by
    intro i
    rw [qq_eq, (hp i).2]; ring
  -- the single-agent bound: q i = 0 when a cap is 0
  have hq_cap₁ : ∀ i, cap₁ (part₁ i) = 0 → q i = 0 := by
    intro i h0
    have h := htc₁ (part₁ i)
    rw [h0] at h
    have : q i ≤ ∑ i' ∈ Finset.univ.filter (fun i' => part₁ i' = part₁ i), qf t i' :=
      Finset.single_le_sum (f := fun i' => qf t i') (fun i' _ => hq0 i')
        (Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩)
    simp only [Nat.cast_zero] at h
    linarith [hq0 i]
  have hq_cap₂ : ∀ i, cap₂ (part₂ i) = 0 → q i = 0 := by
    intro i h0
    have h := htc₂ (part₂ i)
    rw [h0] at h
    have : q i ≤ ∑ i' ∈ Finset.univ.filter (fun i' => part₂ i' = part₂ i), qf t i' :=
      Finset.single_le_sum (f := fun i' => qf t i') (fun i' _ => hq0 i')
        (Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩)
    simp only [Nat.cast_zero] at h
    linarith [hq0 i]
  -- oblRevenue lower bound
  have hobl : (4 / 27 : ℝ) * ∑ i, p i * q i ≤ oblRevenue D J p := by
    let L : Finset ι → ℝ := fun S =>
      ∑ i, p i * (if i ∈ S ∧ Ev part₁ cap₁ part₂ cap₂ i S then 1 else 0)
    have hL : ∀ v, ∀ S ∈ maxFeasDesiringSets J p v, L (desiring p v) ≤ ∑ i ∈ S, p i := by
      intro v S hS
      simp only [L, mul_ite, mul_one, mul_zero]
      rw [← Finset.sum_filter]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        exact mem_of_Ev part₁ cap₁ part₂ cap₂ p i v hi.1 hi.2 S hS
      · intro i _ _
        exact hp0 i
    have h1 := obl_ge D J p L hL
    refine le_trans ?_ h1
    have h2 : ∑ S, mu D p S * L S =
        ∑ i, p i * (qq D p i * ∑ S, mu D p S *
          (if Ev part₁ cap₁ part₂ cap₂ i S then 1 else 0)) := by
      simp only [L, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      have hin := indep D p i (Ev part₁ cap₁ part₂ cap₂ i) (Ev_erase part₁ cap₁ part₂ cap₂ i)
      have e1 : ∑ x, mu D p x * (p i * (if i ∈ x ∧ Ev part₁ cap₁ part₂ cap₂ i x then 1 else 0))
          = p i * ∑ x, mu D p x * (if i ∈ x ∧ Ev part₁ cap₁ part₂ cap₂ i x then 1 else 0) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun x _ => by ring)
      rw [e1, hin, Finset.mul_sum, Finset.mul_sum]
    rw [h2, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    by_cases hk : 1 ≤ cap₁ (part₁ i) ∧ 1 ≤ cap₂ (part₂ i)
    · have hE : ∀ S, Ev part₁ cap₁ part₂ cap₂ i S ↔
          ((S.filter (fun i' => i' ≠ i ∧ part₁ i' = part₁ i)).card ≤ cap₁ (part₁ i) - 1 ∧
          (S.filter (fun i' => i' ≠ i ∧ part₂ i' = part₂ i)).card ≤ cap₂ (part₂ i) - 1) := by
        intro S
        unfold Ev
        exact ⟨fun h => h.1, fun h => ⟨h, hk⟩⟩
      have hsum : ∑ S, mu D p S * (if Ev part₁ cap₁ part₂ cap₂ i S then 1 else 0) =
          (prior D {v |
            ((desiring p v).filter (fun i' => i' ≠ i ∧ part₁ i' = part₁ i)).card ≤ cap₁ (part₁ i) - 1 ∧
            ((desiring p v).filter (fun i' => i' ≠ i ∧ part₂ i' = part₂ i)).card ≤ cap₂ (part₂ i) - 1}).toReal := by
        rw [prior_pred D p (fun S =>
            ((S.filter (fun i' => i' ≠ i ∧ part₁ i' = part₁ i)).card ≤ cap₁ (part₁ i) - 1 ∧
            (S.filter (fun i' => i' ≠ i ∧ part₂ i' = part₂ i)).card ≤ cap₂ (part₂ i) - 1))]
        apply Finset.sum_congr rfl
        intro S _
        simp only [hE]
      have hq₁ : ∀ b, ∑ i' ∈ Finset.univ.filter (fun i' => part₁ i' = b), (1 - (D i').cdf (p i'))
          ≤ (cap₁ b : ℝ) / 3 := by
        intro b
        have := htc₁ b
        simp only [(hp _).2, sub_sub_cancel]
        rw [← Finset.sum_div]
        exact div_le_div_of_nonneg_right this (by norm_num)
      have hq₂ : ∀ b, ∑ i' ∈ Finset.univ.filter (fun i' => part₂ i' = b), (1 - (D i').cdf (p i'))
          ≤ (cap₂ b : ℝ) / 3 := by
        intro b
        have := htc₂ b
        simp only [(hp _).2, sub_sub_cancel]
        rw [← Finset.sum_div]
        exact div_le_div_of_nonneg_right this (by norm_num)
      have hcp := cp_core D part₁ cap₁ part₂ cap₂ p hq₁ hq₂ i hk.1 hk.2
      rw [hsum, hqq]
      have hpq : 0 ≤ p i * (q i / 3) := mul_nonneg (hp0 i) (by linarith [hq0 i])
      nlinarith
    · have hqi : q i = 0 := by
        rcases not_and_or.1 hk with h | h
        · exact hq_cap₁ i (by omega)
        · exact hq_cap₂ i (by omega)
      rw [hqi, hqq, hqi]
      simp
  refine ⟨p, fun M hM => ?_⟩
  -- revenue ≤ R t
  choose pM hpM using fun i => TPAux.exists_cdf_eq (D i) (servProb D M i)
    (servProb_nonneg D M i) (servProb_le_one D M i)
  have h1 : revenue D M ≤ ∑ i, pM i * servProb D M i :=
    rev_le_core D hreg J M hM pM (fun i => ⟨(hpM i).1, (hpM i).2⟩)
  have hqM : ∀ i, qf pM i = servProb D M i := by
    intro i
    simp only [qf, (hpM i).2, sub_sub_cancel]
  have h2 : ∑ i, pM i * servProb D M i = R pM := by
    simp only [R, hqM]
  have hpMQ : pM ∈ Q := by
    refine (hQmem pM).2 ⟨fun i _ => (hpM i).1, fun b => ?_, fun b => ?_⟩
    · simp only [hqM]
      exact sum_servProb_le D part₁ cap₁ J (fun S hS => hS.1) M hM b
    · simp only [hqM]
      exact sum_servProb_le D part₂ cap₂ J (fun S hS => hS.2) M hM b
  have h3 : R pM ≤ R t := isMaxOn_iff.1 htmax pM hpMQ
  have h4 : R t ≤ ∑ i, p i * q i := by
    apply Finset.sum_le_sum
    intro i _
    show t i * q i ≤ p i * q i
    rcases (hq0 i).lt_or_eq with hpos | hzero
    · apply mul_le_mul_of_nonneg_right _ (hq0 i)
      by_contra hlt
      push_neg at hlt
      have hm := TPAux.cdf_mono' (D i) hlt.le
      have e1 := (hp i).2
      have e2 : (D i).cdf (t i) = 1 - q i := by simp only [q, qf]; ring
      rw [e1, e2] at hm
      linarith
    · rw [← hzero]; simp
  linarith

end TPMain
end CHMSPricing.UnitDemand

open CHMSPricing.UnitDemand


theorem solution {ι β₁ β₂ : Type*} [Fintype ι] [DecidableEq ι]
    [DecidableEq β₁] [DecidableEq β₂]
    (D : ι → ValueDist) (hreg : ∀ i, (D i).Regular)
    (part₁ : ι → β₁) (cap₁ : β₁ → ℕ) (part₂ : ι → β₂) (cap₂ : β₂ → ℕ) :
    ∃ p : ι → ℝ, ∀ M : Mechanism ι,
      IsTruthful D (twoPartitionSystem part₁ cap₁ part₂ cap₂) M →
        revenue D M ≤ (27 / 4 : ℝ) * oblRevenue D (twoPartitionSystem part₁ cap₁ part₂ cap₂) p := by
  exact tp_core D hreg part₁ cap₁ part₂ cap₂
