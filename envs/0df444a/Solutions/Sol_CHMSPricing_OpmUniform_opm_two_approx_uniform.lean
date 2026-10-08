-- Prove2me | solution 1 for CHMSPricing.OpmUniform.opm_two_approx_uniform
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T06:55:51.340146+00:00
-- url     : https://prove2.me/submissions/4ccf68d0-dd96-449c-b644-49d1b81afa0e

import Mathlib
import Definitions.Def_CHMSPricing_OpmUniform_Mechanism
import Definitions.Def_CHMSPricing_OpmUniform_Opm



namespace CHMSPricing.OpmUniform

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
end CHMSPricing.OpmUniform

namespace CHMSPricing.OpmUniform
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

lemma int_inner (D : ι → ValueDist) (i : ι) (F : (ι → ℝ) → ℝ)
    (hF : Integrable F (prior D)) :
    Integrable (fun v => ∫ x, F (Function.update v i x) ∂(D i).law) (prior D) := by
  have hmeas : Measurable (fun p : (ι → ℝ) × ℝ => Function.update p.1 i p.2) := measurable_update'
  rw [← prior_update D i] at hF
  have := (integrable_map_measure hF.aestronglyMeasurable hmeas.aemeasurable).1 hF
  exact this.integral_prod_left

theorem rev_le (D : ι → ValueDist) (J : SetSystem ι) (M : Mechanism ι)
    (hM : IsTruthful D J M) :
    revenue D M ≤ ∫ v, virtualSurplus D (M.alloc v) v ∂(prior D) := by
  let Fvs : ι → (ι → ℝ) → ℝ := fun i v => if i ∈ M.alloc v then (D i).virtualValue (v i) else 0
  have hvs : ∀ v, virtualSurplus D (M.alloc v) v = ∑ i, Fvs i v := by
    intro v
    simp only [virtualSurplus, Fvs]
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
    have hlo : (D i).lo ∈ Icc (D i).lo (D i).hi := ⟨le_rfl, hlh⟩
    set u0 := M.utility i (D i).lo (Function.update v i (D i).lo) with hu0
    have hu0nn : 0 ≤ u0 := by
      have := hM.ir _ (update_mem_ts D v hv i _ hlo) i
      simpa using this
    obtain ⟨t, ht, hx⟩ := RevAux.one_dim (D i).lo (D i).hi hlh
      (fun x => i ∈ M.alloc (Function.update v i x))
      (fun x => M.pay (Function.update v i x) i + u0)
      (by
        intro x hx y hy
        have := hM.dsic _ (update_mem_ts D v hv i x hx) i y hy
        have h2 : (if i ∈ M.alloc (Function.update v i y) then x else 0) -
            M.pay (Function.update v i y) i ≤ (if i ∈ M.alloc (Function.update v i x) then x else 0) -
            M.pay (Function.update v i x) i := by
          simpa [Mechanism.utility, Function.update_idem] using this
        linarith)
      (by
        rw [hu0]; simp [Mechanism.utility])
    have e1 : ∫ x, M.pay (Function.update v i x) i ∂(D i).law =
        ∫ x, ((if t < x then t else 0) - u0) ∂(D i).law := by
      refine integral_congr_ae ?_
      filter_upwards [RevAux.law_ae_mem (D i), RevAux.ae_ne (D i) t] with x h1 h2
      have := (hx x h1 h2).2
      linarith
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
    have hi : Integrable (fun x : ℝ => if t < x then t else 0) (D i).law := by
      rw [this]; exact (integrable_const _).indicator measurableSet_Ioi
    rw [integral_sub hi (integrable_const _), this, integral_indicator_const _ measurableSet_Ioi,
      measureReal_def, smul_eq_mul, mul_comm]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    linarith
  simp_rw [hvs]
  rw [revenue, integral_finset_sum _ (fun i _ => hM.pay_integrable i),
    integral_finset_sum _ (fun i _ => iFvs i)]
  exact Finset.sum_le_sum (fun i _ => key i)

end Main
end CHMSPricing.OpmUniform

namespace CHMSPricing.OpmUniform

open MeasureTheory Finset

open MeasureTheory Finset

namespace SAux
variable {n : ℕ}

def bef (p : Fin n → ℝ) (j i : Fin n) : Prop := p j < p i ∨ (p j = p i ∧ j < i)

noncomputable instance (p : Fin n → ℝ) (j i : Fin n) : Decidable (bef p j i) := by
  unfold bef; infer_instance

lemma bef_irrefl (p : Fin n → ℝ) (i : Fin n) : ¬ bef p i i := by
  simp [bef]

lemma bef_trans (p : Fin n → ℝ) {a b c : Fin n} (h1 : bef p a b) (h2 : bef p b c) : bef p a c := by
  unfold bef at *
  rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
  · left; linarith
  · left; linarith
  · left; linarith
  · right; exact ⟨h1.trans h2, h1'.trans h2'⟩

lemma bef_total (p : Fin n → ℝ) {a b : Fin n} (h : a ≠ b) : bef p a b ∨ bef p b a := by
  unfold bef
  rcases lt_trichotomy (p a) (p b) with h1 | h1 | h1
  · left; left; exact h1
  · rcases lt_or_gt_of_ne h with h2 | h2
    · left; right; exact ⟨h1, h2⟩
    · right; right; exact ⟨h1.symm, h2⟩
  · right; left; exact h1

noncomputable def pre (p v : Fin n → ℝ) (i : Fin n) : Finset (Fin n) :=
  univ.filter (fun j => p j ≤ v j ∧ bef p j i)

noncomputable def Dset (p v : Fin n → ℝ) : Finset (Fin n) := univ.filter (fun j => p j ≤ v j)

noncomputable def Sstar (p v : Fin n → ℝ) (k : ℕ) : Finset (Fin n) :=
  univ.filter (fun i => p i ≤ v i ∧ (pre p v i).card < k)

lemma mem_Sstar {p v : Fin n → ℝ} {k : ℕ} {i : Fin n} :
    i ∈ Sstar p v k ↔ p i ≤ v i ∧ (pre p v i).card < k := by
  simp [Sstar]

lemma pre_lt (p v : Fin n → ℝ) {a b : Fin n} (ha : p a ≤ v a) (h : bef p a b) :
    (pre p v a).card < (pre p v b).card := by
  refine card_lt_card ⟨fun j hj => ?_, fun hsub => ?_⟩
  · simp only [pre, mem_filter, mem_univ, true_and] at hj ⊢
    exact ⟨hj.1, bef_trans p hj.2 h⟩
  · have : a ∈ pre p v b := by simp [pre, ha, h]
    have := hsub this
    simp [pre, bef_irrefl] at this

lemma pre_sub_D (p v : Fin n → ℝ) (i : Fin n) (hi : p i ≤ v i) :
    (pre p v i).card < (Dset p v).card := by
  refine card_lt_card ⟨fun j hj => ?_, fun hsub => ?_⟩
  · simp only [pre, Dset, mem_filter, mem_univ, true_and] at hj ⊢; exact hj.1
  · have : i ∈ Dset p v := by simp [Dset, hi]
    have := hsub this
    simp [pre, bef_irrefl] at this

lemma Sstar_sub (p v : Fin n → ℝ) (k : ℕ) : Sstar p v k ⊆ Dset p v := by
  intro i hi; rw [mem_Sstar] at hi; simp [Dset, hi.1]

lemma Sstar_card_le (p v : Fin n → ℝ) (k : ℕ) : (Sstar p v k).card ≤ k := by
  have := card_le_card_of_injOn (fun a => (pre p v a).card) (s := Sstar p v k) (t := range k)
    (fun a ha => by rw [Finset.mem_coe, mem_Sstar] at ha; simpa using ha.2) (fun a ha b hb hab => by
      by_contra hne
      rcases bef_total p hne with h | h
      · have := pre_lt p v (mem_Sstar.1 (Finset.mem_coe.1 ha)).1 h; simp only at hab; omega
      · have := pre_lt p v (mem_Sstar.1 (Finset.mem_coe.1 hb)).1 h; simp only at hab; omega)
  simpa using this

lemma Sstar_eq_D (p v : Fin n → ℝ) (k : ℕ) (h : (Dset p v).card ≤ k) : Sstar p v k = Dset p v := by
  refine Subset.antisymm (Sstar_sub p v k) (fun i hi => ?_)
  have hi' : p i ≤ v i := by simpa [Dset] using hi
  rw [mem_Sstar]
  exact ⟨hi', lt_of_lt_of_le (pre_sub_D p v i hi') h⟩

lemma Sstar_card_ge (p v : Fin n → ℝ) (k : ℕ) (h : k ≤ (Dset p v).card) :
    k ≤ (Sstar p v k).card := by
  by_contra hlt
  push_neg at hlt
  have hne : (Dset p v \ Sstar p v k).Nonempty := by
    rw [nonempty_iff_ne_empty]
    intro he
    rw [sdiff_eq_empty_iff_subset] at he
    have := card_le_card he
    omega
  obtain ⟨b, hb, hmin⟩ := exists_min_image _ (fun a => (pre p v a).card) hne
  rw [mem_sdiff] at hb
  have hbD : p b ≤ v b := by simpa [Dset] using hb.1
  have hbk : k ≤ (pre p v b).card := by
    by_contra h'; exact hb.2 (mem_Sstar.2 ⟨hbD, by omega⟩)
  have : ¬ pre p v b ⊆ Sstar p v k := by
    intro hs; have := card_le_card hs; omega
  rw [not_subset] at this
  obtain ⟨j, hj, hjS⟩ := this
  simp only [pre, mem_filter, mem_univ, true_and] at hj
  have hjN : j ∈ Dset p v \ Sstar p v k := mem_sdiff.2 ⟨by simp [Dset, hj.1], hjS⟩
  have h1 := hmin j hjN
  have h2 := pre_lt p v hj.1 hj.2
  omega

lemma Sstar_mem (p v : Fin n → ℝ) (k : ℕ) :
    Sstar p v k ∈ maxFeasDesiringSets (uniformSystem n k) p v := by
  classical
  unfold maxFeasDesiringSets
  rw [mem_filter]
  refine ⟨mem_univ _, Sstar_card_le p v k, fun i hi => (mem_Sstar.1 hi).1, fun S' hS' hfS' => ?_⟩
  by_contra hall
  push_neg at hall
  have hsub : S' ⊆ Dset p v := fun i hi => by simp [Dset, hall i hi]
  have hc := card_lt_card hS'
  have hf : S'.card ≤ k := hfS'
  rcases le_or_gt (Dset p v).card k with h | h
  · rw [Sstar_eq_D p v k h] at hc; have := card_le_card hsub; omega
  · have := Sstar_card_ge p v k h.le; omega

lemma sum_le_of_le {A B : Finset (Fin n)} (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hc : A.card ≤ B.card) (h : ∀ a ∈ A, ∀ b ∈ B, p a ≤ p b) : ∑ a ∈ A, p a ≤ ∑ b ∈ B, p b := by
  rcases A.eq_empty_or_nonempty with hA | hA
  · rw [hA, sum_empty]; exact sum_nonneg (fun i _ => hp i)
  · set m := A.sup' hA p
    have h1 : ∑ a ∈ A, p a ≤ A.card * m := by
      have : ∑ a ∈ A, p a ≤ ∑ _a ∈ A, m := sum_le_sum (fun a ha => le_sup' p ha)
      simpa using this
    have h2 : (B.card : ℝ) * m ≤ ∑ b ∈ B, p b := by
      have : ∑ _b ∈ B, m ≤ ∑ b ∈ B, p b :=
        sum_le_sum (fun b hb => (sup'_le hA p (fun a ha => h a ha b hb) : m ≤ p b))
      simpa using this
    have hm : 0 ≤ m := (hp _).trans (le_sup' p hA.choose_spec)
    have : (A.card : ℝ) * m ≤ B.card * m :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hm
    linarith

lemma Sstar_min (p v : Fin n → ℝ) (k : ℕ) (hp : ∀ i, 0 ≤ p i) (S : Finset (Fin n))
    (hS : S ∈ maxFeasDesiringSets (uniformSystem n k) p v) :
    ∑ i ∈ Sstar p v k, p i ≤ ∑ i ∈ S, p i := by
  classical
  unfold maxFeasDesiringSets at hS
  rw [mem_filter] at hS
  obtain ⟨_, hSf, hSd, hSmax⟩ := hS
  have hSf' : S.card ≤ k := hSf
  have hSsub : S ⊆ Dset p v := fun i hi => by simp [Dset, hSd i hi]
  -- |S| ≥ |S*|
  have hcard : (Sstar p v k).card ≤ S.card := by
    by_contra hlt
    push_neg at hlt
    have h1 := Sstar_card_le p v k
    have h2 := card_le_card (Sstar_sub p v k)
    have : ¬ Dset p v ⊆ S := fun hs => by have := card_le_card hs; omega
    rw [not_subset] at this
    obtain ⟨b, hbD, hbS⟩ := this
    obtain ⟨i, hi, hlt'⟩ := hSmax (insert b S) (ssubset_insert hbS)
      (by show (insert b S).card ≤ k; rw [card_insert_of_notMem hbS]; omega)
    rw [mem_insert] at hi
    rcases hi with rfl | hi
    · simp [Dset] at hbD; linarith
    · linarith [hSd i hi]
  rw [← sum_sdiff (inter_subset_left (s₁ := Sstar p v k) (s₂ := S)),
    ← sum_sdiff (inter_subset_right (s₁ := Sstar p v k) (s₂ := S))]
  have hAB : (Sstar p v k \ (Sstar p v k ∩ S)).card ≤ (S \ (Sstar p v k ∩ S)).card := by
    rw [card_sdiff_of_subset inter_subset_left, card_sdiff_of_subset inter_subset_right]
    omega
  have := sum_le_of_le p hp hAB (fun a ha b hb => ?_)
  · linarith
  · rw [mem_sdiff] at ha hb
    have haS : a ∈ Sstar p v k := ha.1
    have hbn : b ∉ Sstar p v k := fun h => hb.2 (mem_inter.2 ⟨h, hb.1⟩)
    have hbD : p b ≤ v b := hSd b hb.1
    by_contra hlt
    push_neg at hlt
    have hba : bef p b a := Or.inl hlt
    have h1 := pre_lt p v hbD hba
    have h2 := (mem_Sstar.1 haS).2
    exact hbn (mem_Sstar.2 ⟨hbD, by omega⟩)

lemma inf_eq (p v : Fin n → ℝ) (k : ℕ) (hp : ∀ i, 0 ≤ p i) :
    (maxFeasDesiringSets (uniformSystem n k) p v).inf'
      (maxFeasDesiringSets_nonempty (uniformSystem n k) p v) (fun S => ∑ i ∈ S, p i) =
    ∑ i ∈ Sstar p v k, p i :=
  le_antisymm (inf'_le _ (Sstar_mem p v k)) (le_inf' _ _ (fun S hS => Sstar_min p v k hp S hS))

end SAux

namespace GAux
lemma meas_filter {Ω : Type*} [MeasurableSpace Ω] {m : ℕ} (p : Fin m → Ω → Prop)
    [∀ l ω, Decidable (p l ω)] (hp : ∀ l, MeasurableSet {ω | p l ω})
    (Q : Finset (Fin m) → Prop) : MeasurableSet {ω | Q (univ.filter (fun l => p l ω))} := by
  classical
  have : {ω | Q (univ.filter (fun l => p l ω))} =
      ⋃ s ∈ (univ.filter Q : Finset (Finset (Fin m))), ⋂ l, {ω | p l ω ↔ l ∈ s} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_iInter, mem_filter, mem_univ,
      true_and, exists_prop]
    constructor
    · intro h; exact ⟨_, h, fun l => by simp⟩
    · rintro ⟨s, hs, h⟩
      convert hs
      ext l; simp [h l]
  rw [this]
  refine Finset.measurableSet_biUnion _ (fun s _ => MeasurableSet.iInter (fun l => ?_))
  by_cases hl : l ∈ s
  · simpa [hl] using hp l
  · have : {ω | p l ω ↔ l ∈ s} = {ω | p l ω}ᶜ := by ext ω; simp [hl]
    rw [this]; exact (hp l).compl

end GAux

namespace GAux

lemma vv_le (D : ValueDist) (x : ℝ) (hx : x ∈ Set.Icc D.lo D.hi) : D.virtualValue x ≤ x := by
  unfold ValueDist.virtualValue
  have h1 : 0 ≤ 1 - D.cdf x := by rw [RevAux.one_sub_cdf]; exact ENNReal.toReal_nonneg
  have h2 := D.f_pos x hx
  have : 0 ≤ (1 - D.cdf x) / D.f x := div_nonneg h1 h2.le
  linarith

lemma price_exists (D : ValueDist) (hreg : D.Regular) (c : ℝ) :
    ∃ q ∈ Set.Icc D.lo D.hi, ∀ x ∈ Set.Icc D.lo D.hi, x ≠ q →
      (q ≤ x ↔ c ≤ D.virtualValue x) := by
  set U := {x | x ∈ Set.Icc D.lo D.hi ∧ c ≤ D.virtualValue x} with hU
  have hbdd : BddBelow U := ⟨D.lo, fun x hx => hx.1.1⟩
  by_cases hne : U.Nonempty
  · obtain ⟨x0, hx0⟩ := hne
    refine ⟨sInf U, ⟨le_csInf ⟨x0, hx0⟩ (fun x hx => hx.1.1),
      (csInf_le hbdd hx0).trans hx0.1.2⟩, fun x hx hne' => ?_⟩
    rcases lt_or_gt_of_ne hne' with h | h
    · refine ⟨fun h' => absurd h' (not_le.2 h), fun h' => ?_⟩
      exact csInf_le hbdd ⟨hx, h'⟩
    · obtain ⟨u, hu, hux⟩ := exists_lt_of_csInf_lt ⟨x0, hx0⟩ h
      exact ⟨fun _ => hu.2.trans (hreg hu.1 hx hux.le), fun _ => h.le⟩
  · refine ⟨D.hi, ⟨D.lo_lt_hi.le, le_rfl⟩, fun x hx hne' => ?_⟩
    have hlt : x < D.hi := lt_of_le_of_ne hx.2 hne'
    refine ⟨fun h => absurd h (not_le.2 hlt), fun h => ?_⟩
    exact absurd ⟨x, hx, h⟩ hne

/-- the excess function -/
noncomputable def Ex (D : ValueDist) (c : ℝ) : ℝ := ∫ x, max 0 (D.virtualValue x - c) ∂D.law

lemma ex_integrable (D : ValueDist) (c : ℝ) :
    Integrable (fun x => max 0 (D.virtualValue x - c)) D.law := by
  have := ((RevAux.vv_integrable D).sub (integrable_const c)).pos_part
  refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
  simp [max_comm]

lemma ex_nonneg (D : ValueDist) (c : ℝ) : 0 ≤ Ex D c :=
  integral_nonneg (fun _ => le_max_left _ _)

lemma ex_cont (D : ValueDist) : Continuous (fun c => Ex D (max c 0)) := by
  unfold Ex
  refine continuous_of_dominated (bound := fun x => |D.virtualValue x|) ?_ ?_
    (RevAux.vv_integrable D).abs ?_
  · intro c
    exact ((measurable_const.max ((RevAux.vv_measurable D).sub measurable_const))).aestronglyMeasurable
  · intro c
    refine Filter.Eventually.of_forall (fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
    refine max_le (abs_nonneg _) ?_
    have := le_abs_self (D.virtualValue x)
    have := le_max_right c 0
    linarith
  · refine Filter.Eventually.of_forall (fun x => ?_)
    exact continuous_const.max (continuous_const.sub (continuous_id.max continuous_const))

lemma c_exists {n : ℕ} (D : Fin n → ValueDist) (k : ℕ) :
    ∃ c, 0 ≤ c ∧ ∑ i, Ex (D i) c = k * c := by
  set C := ∑ i, (D i).hi with hC
  have hC0 : 0 ≤ C := Finset.sum_nonneg (fun i _ => (D i).lo_nonneg.trans (D i).lo_lt_hi.le)
  let G : ℝ → ℝ := fun c => ∑ i, Ex (D i) (max c 0) - k * c
  have hG : Continuous G :=
    (continuous_finset_sum _ (fun i _ => ex_cont (D i))).sub (continuous_const.mul continuous_id)
  have hG0 : 0 ≤ G 0 := by
    simp only [G, max_self, mul_zero, sub_zero]
    exact Finset.sum_nonneg (fun i _ => ex_nonneg _ _)
  have hGC : G C ≤ 0 := by
    have : ∀ i, Ex (D i) (max C 0) = 0 := by
      intro i
      rw [max_eq_left hC0]
      unfold Ex
      have : (fun x => max 0 ((D i).virtualValue x - C)) =ᵐ[(D i).law] fun _ => 0 := by
        filter_upwards [RevAux.law_ae_mem (D i)] with x hx
        have h1 := vv_le (D i) x hx
        have h2 : (D i).hi ≤ C := Finset.single_le_sum (f := fun j => (D j).hi)
          (fun j _ => (D j).lo_nonneg.trans (D j).lo_lt_hi.le) (Finset.mem_univ i)
        exact max_eq_left (by linarith [hx.2])
      rw [integral_congr_ae this]; simp
    simp only [G, this, Finset.sum_const_zero, zero_sub, neg_nonpos]
    exact mul_nonneg (Nat.cast_nonneg _) hC0
  obtain ⟨c, hc, hGc⟩ := intermediate_value_Icc' hC0 hG.continuousOn ⟨hGC, hG0⟩
  refine ⟨c, hc.1, ?_⟩
  simp only [G, max_eq_left hc.1] at hGc
  linarith

end GAux

open GAux SAux

variable {n : ℕ}

lemma eval_integral (D : Fin n → ValueDist) (i : Fin n) (g : ℝ → ℝ)
    (hg : AEStronglyMeasurable g (D i).law) :
    ∫ v, g (v i) ∂(prior D) = ∫ x, g x ∂(D i).law := by
  have hmp : MeasurePreserving (Function.eval i) (prior D) (D i).law :=
    measurePreserving_eval (fun j => (D j).law) i
  rw [← hmp.map_eq] at hg ⊢
  exact (integral_map (measurable_pi_apply i).aemeasurable hg).symm

lemma eval_integrable (D : Fin n → ValueDist) (i : Fin n) (g : ℝ → ℝ)
    (hg : Integrable g (D i).law) : Integrable (fun v : Fin n → ℝ => g (v i)) (prior D) := by
  have hmp : MeasurePreserving (Function.eval i) (prior D) (D i).law :=
    measurePreserving_eval (fun j => (D j).law) i
  rw [← hmp.map_eq] at hg
  exact hg.comp_measurable (measurable_pi_apply i)

lemma upper (D : Fin n → ValueDist) (k : ℕ) (c : ℝ) (hc : 0 ≤ c)
    (M : Mechanism (Fin n)) (hM : IsTruthful D (uniformSystem n k) M) :
    revenue D M ≤ k * c + ∑ i, Ex (D i) c := by
  refine (rev_le D _ M hM).trans ?_
  have hvs_int : Integrable (fun v => virtualSurplus D (M.alloc v) v) (prior D) := by
    have : (fun v => virtualSurplus D (M.alloc v) v) = fun v => ∑ i,
        (if i ∈ M.alloc v then (D i).virtualValue (v i) else 0) := by
      funext v; simp only [virtualSurplus]; rw [Finset.sum_ite_mem, Finset.univ_inter]
    rw [this]
    refine integrable_finset_sum _ (fun i _ => ?_)
    have := (eval_integrable D i _ (RevAux.vv_integrable (D i))).indicator (hM.alloc_measurable i)
    refine this.congr (Filter.Eventually.of_forall (fun v => ?_))
    simp [Set.indicator]
  have hup_int : Integrable (fun v : Fin n → ℝ => (k : ℝ) * c +
      ∑ i, max 0 ((D i).virtualValue (v i) - c)) (prior D) :=
    (integrable_const _).add (integrable_finset_sum _ (fun i _ =>
      eval_integrable D i _ (ex_integrable (D i) c)))
  have hcalc : ∫ v, ((k : ℝ) * c + ∑ i, max 0 ((D i).virtualValue (v i) - c)) ∂(prior D) =
      k * c + ∑ i, Ex (D i) c := by
    rw [integral_add (integrable_const _) (integrable_finset_sum _ (fun i _ =>
      eval_integrable D i _ (ex_integrable (D i) c))), integral_finset_sum _ (fun i _ =>
      eval_integrable D i _ (ex_integrable (D i) c))]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    exact eval_integral D i _ (ex_integrable (D i) c).aestronglyMeasurable
  rw [← hcalc]
  refine integral_mono_ae hvs_int hup_int ?_
  filter_upwards [ae_ts D] with v hv
  have hcard : (M.alloc v).card ≤ k := hM.feasible v hv
  simp only [virtualSurplus]
  calc ∑ i ∈ M.alloc v, (D i).virtualValue (v i)
      ≤ ∑ i ∈ M.alloc v, (c + max 0 ((D i).virtualValue (v i) - c)) :=
        Finset.sum_le_sum (fun i _ => by linarith [le_max_right 0 ((D i).virtualValue (v i) - c)])
    _ = (M.alloc v).card * c + ∑ i ∈ M.alloc v, max 0 ((D i).virtualValue (v i) - c) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    _ ≤ k * c + ∑ i, max 0 ((D i).virtualValue (v i) - c) := by
        gcongr
        exact Finset.subset_univ _

lemma ind_int (D : Fin n → ValueDist) (s : Set (Fin n → ℝ)) [DecidablePred (· ∈ s)] (hs : MeasurableSet s) (a : ℝ) :
    ∫ v, (if v ∈ s then a else 0) ∂(prior D) = (prior D s).toReal * a := by
  have : (fun v => if v ∈ s then a else 0) = s.indicator (fun _ => a) := by
    funext v; simp [Set.indicator]
  rw [this, integral_indicator_const _ hs, measureReal_def, smul_eq_mul]

lemma ind_integrable (D : Fin n → ValueDist) (s : Set (Fin n → ℝ)) [DecidablePred (· ∈ s)] (hs : MeasurableSet s)
    (g : (Fin n → ℝ) → ℝ) (hg : Integrable g (prior D)) :
    Integrable (fun v => if v ∈ s then g v else 0) (prior D) := by
  have := hg.indicator hs
  refine this.congr (Filter.Eventually.of_forall (fun v => ?_))
  simp [Set.indicator]

lemma lower (D : Fin n → ValueDist) (k : ℕ) (c : ℝ) (hc : 0 ≤ c)
    (hfix : ∑ i, Ex (D i) c = k * c) (q : Fin n → ℝ)
    (hq : ∀ i, q i ∈ Set.Icc (D i).lo (D i).hi)
    (hqp : ∀ i, ∀ x ∈ Set.Icc (D i).lo (D i).hi, x ≠ q i →
      (q i ≤ x ↔ c ≤ (D i).virtualValue x)) :
    (k : ℝ) * c ≤ oblRevenue D (uniformSystem n k) q := by
  have hqnn : ∀ i, 0 ≤ q i := fun i => (D i).lo_nonneg.trans (hq i).1
  have hle : ∀ j, MeasurableSet {v : Fin n → ℝ | q j ≤ v j} :=
    fun j => measurableSet_le measurable_const (measurable_pi_apply j)
  have hSm : ∀ i, MeasurableSet {v : Fin n → ℝ | i ∈ Sstar q v k} := by
    intro i
    have : {v : Fin n → ℝ | i ∈ Sstar q v k} = {v | q i ≤ v i} ∩
        {v | (univ.filter (fun j => q j ≤ v j ∧ bef q j i)).card < k} := by
      ext v; simp [mem_Sstar, pre]
    rw [this]
    refine (hle i).inter (meas_filter (fun j (v : Fin n → ℝ) => q j ≤ v j ∧ bef q j i) (fun j => ?_)
      (fun s => s.card < k))
    by_cases h : bef q j i
    · simpa [h] using hle j
    · simp [h]
  have hDm : MeasurableSet {v : Fin n → ℝ | k ≤ (Dset q v).card} := by
    unfold Dset
    exact meas_filter (fun j (v : Fin n → ℝ) => q j ≤ v j) hle (fun s => k ≤ s.card)
  have hBm : ∀ i, MeasurableSet {v : Fin n → ℝ |
      (univ.filter (fun j => j ≠ i ∧ q j ≤ v j)).card < k} := by
    intro i
    refine meas_filter (fun j (v : Fin n → ℝ) => j ≠ i ∧ q j ≤ v j) (fun j => ?_) (fun s => s.card < k)
    by_cases h : j = i
    · simp [h]
    · simpa [h] using hle j
  -- step 1
  have h1 : oblRevenue D (uniformSystem n k) q =
      ∑ i, ∫ v, (if v ∈ {v : Fin n → ℝ | i ∈ Sstar q v k} then q i else 0) ∂(prior D) := by
    unfold oblRevenue
    rw [← integral_finset_sum _ (fun i _ => ind_integrable D _ (hSm i) _ (integrable_const _))]
    congr 1; funext v
    rw [inf_eq q v k hqnn]
    simp only [Set.mem_setOf_eq]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hφint : ∀ i, Integrable (fun v : Fin n → ℝ => (D i).virtualValue (v i)) (prior D) :=
    fun i => eval_integrable D i _ (RevAux.vv_integrable (D i))
  -- step 3 : Myerson
  have h3 : ∀ i, ∫ v, (if v ∈ {v : Fin n → ℝ | i ∈ Sstar q v k} then q i else 0) ∂(prior D) =
      ∫ v, (if v ∈ {v : Fin n → ℝ | i ∈ Sstar q v k} then (D i).virtualValue (v i) else 0)
        ∂(prior D) := by
    intro i
    rw [integral_prior_update D i _ (ind_integrable D _ (hSm i) _ (integrable_const _)),
      integral_prior_update D i _ (ind_integrable D _ (hSm i) _ (hφint i))]
    refine integral_congr_ae ?_
    filter_upwards [ae_ts D] with v hv
    have hpre : ∀ x, pre q (Function.update v i x) i = pre q v i := by
      intro x; ext j
      simp only [pre, mem_filter, mem_univ, true_and]
      by_cases hj : j = i
      · subst hj; simp [bef_irrefl]
      · rw [Function.update_of_ne hj]
    have hmemu : ∀ x, i ∈ Sstar q (Function.update v i x) k ↔
        q i ≤ x ∧ (pre q v i).card < k := by
      intro x
      simp only [Set.mem_setOf_eq, mem_Sstar, hpre, Function.update_self]
    by_cases hR : (pre q v i).card < k
    · have e1 : ∫ x, (if i ∈ Sstar q (Function.update v i x) k
          then q i else 0) ∂(D i).law = ∫ x, (if q i < x then q i else 0) ∂(D i).law := by
        refine integral_congr_ae ?_
        filter_upwards [RevAux.ae_ne (D i) (q i)] with x hx
        by_cases h : q i < x
        · rw [if_pos ((hmemu x).2 ⟨h.le, hR⟩), if_pos h]
        · rw [if_neg (fun h' => h (lt_of_le_of_ne ((hmemu x).1 h').1 (Ne.symm hx))), if_neg h]
      have e2 : ∫ x, (if i ∈ Sstar q (Function.update v i x) k
          then (D i).virtualValue (Function.update v i x i) else 0) ∂(D i).law =
          ∫ x, (if q i < x then (D i).virtualValue x else 0) ∂(D i).law := by
        refine integral_congr_ae ?_
        filter_upwards [RevAux.ae_ne (D i) (q i)] with x hx
        rw [Function.update_self]
        by_cases h : q i < x
        · rw [if_pos ((hmemu x).2 ⟨h.le, hR⟩), if_pos h]
        · rw [if_neg (fun h' => h (lt_of_le_of_ne ((hmemu x).1 h').1 (Ne.symm hx))), if_neg h]
      rw [e1, e2, RevAux.key (D i) (q i) (hq i)]
      have : (fun x : ℝ => if q i < x then q i else 0) = (Set.Ioi (q i)).indicator (fun _ => q i) := by
        funext x; simp [Set.indicator]
      rw [this, integral_indicator_const _ measurableSet_Ioi, measureReal_def, smul_eq_mul, mul_comm]
    · have : ∀ x, ¬ (i ∈ Sstar q (Function.update v i x) k) :=
        fun x h => hR ((hmemu x).1 h).2
      simp only [Set.mem_setOf_eq, this, if_false]
  -- step 4: pointwise lower bound
  set qT := (prior D {v : Fin n → ℝ | k ≤ (Dset q v).card}ᶜ).toReal with hqT
  set pT := (prior D {v : Fin n → ℝ | k ≤ (Dset q v).card}).toReal with hpT
  have hpq : pT + qT = 1 := by
    rw [hpT, hqT, prob_compl_eq_one_sub hDm, ENNReal.toReal_sub_of_le prob_le_one
      ENNReal.one_ne_top]
    simp
  have hexi : ∀ i, Integrable (fun v : Fin n → ℝ => max 0 ((D i).virtualValue (v i) - c)) (prior D) :=
    fun i => eval_integrable D i _ (ex_integrable (D i) c)
  have hB : ∀ i, ∫ v, (if v ∈ {v : Fin n → ℝ | (univ.filter (fun j => j ≠ i ∧ q j ≤ v j)).card < k}
      then max 0 ((D i).virtualValue (v i) - c) else 0) ∂(prior D) =
      (prior D {v : Fin n → ℝ | (univ.filter (fun j => j ≠ i ∧ q j ≤ v j)).card < k}).toReal *
        Ex (D i) c := by
    intro i
    rw [integral_prior_update D i _ (ind_integrable D _ (hBm i) _ (hexi i)), ← ind_int D _ (hBm i)]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
    have hBu : ∀ x, (univ.filter (fun j => j ≠ i ∧ q j ≤ Function.update v i x j)) =
        univ.filter (fun j => j ≠ i ∧ q j ≤ v j) := by
      intro x; ext j
      simp only [mem_filter, mem_univ, true_and]
      constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨h1, ?_⟩
      · rwa [Function.update_of_ne h1] at h2
      · rwa [Function.update_of_ne h1]
    simp only [Set.mem_setOf_eq, hBu, Function.update_self]
    split_ifs
    · rfl
    · simp
  have hpw : ∀ᵐ v ∂(prior D),
      (if v ∈ {v : Fin n → ℝ | k ≤ (Dset q v).card} then (k : ℝ) * c else 0) +
        ∑ i, (if v ∈ {v : Fin n → ℝ | (univ.filter (fun j => j ≠ i ∧ q j ≤ v j)).card < k}
          then max 0 ((D i).virtualValue (v i) - c) else 0) ≤
      ∑ i, (if v ∈ {v : Fin n → ℝ | i ∈ Sstar q v k} then (D i).virtualValue (v i) else 0) := by
    have hne : ∀ᵐ v ∂(prior D), ∀ j, v j ≠ q j := by
      rw [ae_all_iff]
      intro j
      have hmp : MeasurePreserving (Function.eval j) (prior D) (D j).law :=
        measurePreserving_eval (fun l => (D l).law) j
      exact hmp.quasiMeasurePreserving.ae (RevAux.ae_ne (D j) (q j))
    filter_upwards [ae_ts D, hne] with v hv hne
    have hdes : ∀ j, q j ≤ v j ↔ c ≤ (D j).virtualValue (v j) :=
      fun j => hqp j (v j) (hv j trivial) (hne j)
    rw [Finset.sum_ite_mem, Finset.univ_inter]
    rcases le_or_gt (Dset q v).card k with hDk | hDk
    · rw [Sstar_eq_D q v k hDk]
      have hb : ∀ i, (if (univ.filter (fun j => j ≠ i ∧ q j ≤ v j)).card < k
          then max 0 ((D i).virtualValue (v i) - c) else 0) ≤
          if i ∈ Dset q v then (D i).virtualValue (v i) - c else 0 := by
        intro i
        by_cases hi : i ∈ Dset q v
        · have : c ≤ (D i).virtualValue (v i) := (hdes i).1 (by simpa [Dset] using hi)
          rw [if_pos hi]
          split_ifs
          · exact (max_eq_right (by linarith)).le
          · linarith
        · have : (D i).virtualValue (v i) < c := by
            rw [← not_le, ← hdes i]; simpa [Dset] using hi
          rw [if_neg hi]
          split_ifs
          · exact (max_eq_left (by linarith)).le
          · exact le_rfl
      have hs := Finset.sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin n))) => hb i)
      rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_sub_distrib, Finset.sum_const,
        nsmul_eq_mul] at hs
      have hk : (if k ≤ (Dset q v).card then (k : ℝ) * c else 0) ≤ (Dset q v).card * c := by
        split_ifs with h
        · have : (Dset q v).card = k := le_antisymm hDk h
          rw [this]
        · exact mul_nonneg (Nat.cast_nonneg _) hc
      linarith
    · have hBf : ∀ i, ¬ (univ.filter (fun j => j ≠ i ∧ q j ≤ v j)).card < k := by
        intro i
        have : (Dset q v).erase i ⊆ univ.filter (fun j => j ≠ i ∧ q j ≤ v j) := by
          intro j hj
          simp only [mem_erase, Dset, mem_filter, mem_univ, true_and] at hj ⊢
          exact hj
        have h1 := card_le_card this
        have h2 := Finset.pred_card_le_card_erase (s := Dset q v) (a := i)
        omega
      simp only [hBf, if_false, Finset.sum_const_zero, add_zero]
      rw [if_pos hDk.le]
      have hcard := Sstar_card_ge q v k hDk.le
      calc (k : ℝ) * c ≤ (Sstar q v k).card * c :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hc
        _ = ∑ i ∈ Sstar q v k, c := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ _ := Finset.sum_le_sum (fun i hi => (hdes i).1 ((mem_Sstar.1 hi).1))
  have hLint : Integrable (fun v =>
      (if v ∈ {v : Fin n → ℝ | k ≤ (Dset q v).card} then (k : ℝ) * c else 0) +
        ∑ i, (if v ∈ {v : Fin n → ℝ | (univ.filter (fun j => j ≠ i ∧ q j ≤ v j)).card < k}
          then max 0 ((D i).virtualValue (v i) - c) else 0)) (prior D) :=
    (ind_integrable D _ hDm _ (integrable_const _)).add
      (integrable_finset_sum _ (fun i _ => ind_integrable D _ (hBm i) _ (hexi i)))
  have hRint : Integrable (fun v => ∑ i, (if v ∈ {v : Fin n → ℝ | i ∈ Sstar q v k}
      then (D i).virtualValue (v i) else 0)) (prior D) :=
    integrable_finset_sum _ (fun i _ => ind_integrable D _ (hSm i) _ (hφint i))
  have hmono := integral_mono_ae hLint hRint hpw
  rw [integral_add (ind_integrable D _ hDm _ (integrable_const _))
      (integrable_finset_sum _ (fun i _ => ind_integrable D _ (hBm i) _ (hexi i))),
    integral_finset_sum _ (fun i _ => ind_integrable D _ (hBm i) _ (hexi i)),
    integral_finset_sum _ (fun i _ => ind_integrable D _ (hSm i) _ (hφint i)),
    ind_int D _ hDm] at hmono
  simp_rw [hB] at hmono
  rw [h1]
  simp_rw [h3]
  refine le_trans ?_ hmono
  have hE : ∀ i, qT * Ex (D i) c ≤
      (prior D {v : Fin n → ℝ | (univ.filter (fun j => j ≠ i ∧ q j ≤ v j)).card < k}).toReal *
        Ex (D i) c := by
    intro i
    refine mul_le_mul_of_nonneg_right ?_ (ex_nonneg _ _)
    rw [hqT]
    refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (fun v hv => ?_))
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hv ⊢
    refine lt_of_le_of_lt (card_le_card (fun j hj => ?_)) hv
    simp only [mem_filter, mem_univ, true_and, Dset] at hj ⊢
    exact hj.2
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin n))) => hE i)
  rw [← Finset.mul_sum, hfix] at hsum
  have : pT * (k * c) + qT * (k * c) = k * c := by rw [← add_mul, hpq, one_mul]
  linarith

theorem goal_core (D : Fin n → ValueDist) (hreg : ∀ i, (D i).Regular) (k : ℕ) :
    ∃ p : Fin n → ℝ, ∀ M : Mechanism (Fin n), IsTruthful D (uniformSystem n k) M →
      revenue D M ≤ 2 * oblRevenue D (uniformSystem n k) p := by
  obtain ⟨c, hc, hfix⟩ := c_exists D k
  choose q hq hqp using fun i => price_exists (D i) (hreg i) c
  refine ⟨q, fun M hM => ?_⟩
  have h1 := upper D k c hc M hM
  have h2 := lower D k c hc hfix q hq hqp
  linarith


end CHMSPricing.OpmUniform

open CHMSPricing.OpmUniform
open MeasureTheory

theorem solution {n : ℕ} (D : Fin n → ValueDist) (hreg : ∀ i, (D i).Regular)
    (k : ℕ) :
    ∃ p : Fin n → ℝ, ∀ M : Mechanism (Fin n), IsTruthful D (uniformSystem n k) M →
      revenue D M ≤ 2 * oblRevenue D (uniformSystem n k) p := by
  exact goal_core D hreg k
