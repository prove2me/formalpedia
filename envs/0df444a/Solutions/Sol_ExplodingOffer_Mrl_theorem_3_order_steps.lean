-- Prove2me | solution 1 for ExplodingOffer.Mrl.theorem_3_order_steps
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T23:15:07.093104+00:00
-- url     : https://prove2.me/submissions/e116c04a-7027-420f-8c7c-f21fdb29a537

import Mathlib
import Definitions.Def_StochasticOrders_MeanResidualLife_MrlOrder
import Definitions.Def_ExplodingOffer_Mrl_Model
import Theorems.Thm_ExplodingOffer_Mrl_lemma_4
import Theorems.Thm_ExplodingOffer_Mrl_tval_bijection
import Theorems.Thm_ExplodingOffer_Mrl_sHat_wellDefined

open MeasureTheory
open ExplodingOffer.Mrl

namespace OrdAux

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

lemma condMean_eq_add_mrl (hμ : OfferDist μ a b) (s : ℝ) (hF : 0 < (μ (Set.Ioi s)).toReal) :
    condMean μ s = s + StochasticOrders.MeanResidualLife.mrl μ id s := by
  haveI := hμ.isProb
  haveI := hμ.noAtoms
  unfold StochasticOrders.MeanResidualLife.mrl
  have hset : {ω : ℝ | s < id ω} = Set.Ioi s := rfl
  rw [hset, if_pos hF]
  unfold condMean
  rw [setIntegral_congr_set (Ioi_ae_eq_Ici (μ := μ) (a := s)).symm,
    measure_congr (Ioi_ae_eq_Ici (μ := μ) (a := s)).symm]
  simp only [id]
  rw [integral_sub hμ.integrable.integrableOn (integrable_const s).integrableOn,
    setIntegral_const, smul_eq_mul, Measure.real_def]
  field_simp
  ring

lemma condMean_eq_mean (hμ : OfferDist μ a b) (t : ℝ) (ht : t ≤ a) : condMean μ t = mean μ := by
  haveI := hμ.isProb
  have hae : ∀ᵐ x ∂μ, x ∈ Set.Ici t := by
    rw [ae_iff]
    have : {x : ℝ | ¬ x ∈ Set.Ici t} ⊆ Set.Iio a := by
      intro x hx; simp only [Set.mem_setOf_eq, Set.mem_Ici, not_le] at hx
      exact lt_of_lt_of_le hx ht
    exact measure_mono_null this hμ.below
  have h1 : μ (Set.Ici t) = 1 := by
    rw [← Measure.restrict_apply_univ, Measure.restrict_eq_self_of_ae_mem hae]; simp
  unfold condMean mean
  rw [Measure.restrict_eq_self_of_ae_mem hae, h1]
  simp

lemma F_pos (hμ : OfferDist μ a b) (v : ℝ) (hv : (v : EReal) < b) :
    0 < (μ (Set.Ioi v)).toReal := by
  haveI := hμ.isProb
  refine ENNReal.toReal_pos ?_ (measure_ne_top _ _)
  rcases lt_or_ge v a with hva | hav
  · have h1 : μ (Set.Ici a) = 1 := by
      have := prob_compl_eq_one_sub (μ := μ) (s := Set.Iio a) measurableSet_Iio
      rw [Set.compl_Iio, hμ.below] at this; simpa using this
    have : Set.Ici a ⊆ Set.Ioi v := fun x hx => lt_of_lt_of_le hva hx
    have := measure_mono (μ := μ) this
    rw [h1] at this
    exact (lt_of_lt_of_le one_pos this).ne'
  · obtain ⟨y, hvy, hyb⟩ : ∃ y : ℝ, v < y ∧ (y : EReal) ≤ b := by
      induction b using EReal.rec with
      | bot => exact absurd hv (by simp)
      | top => exact ⟨v + 1, by linarith, le_top⟩
      | coe r =>
        have hr : v < r := EReal.coe_lt_coe_iff.mp hv
        exact ⟨r, hr, le_rfl⟩
    exact (lt_of_lt_of_le (hμ.noGap v y hav hvy hyb) (measure_mono Set.Ioo_subset_Ioi_self)).ne'

end OrdAux

open OrdAux in
theorem solution {μ₁ μ₂ : Measure ℝ} {a₁ a₂ : ℝ} {b₁ b₂ : EReal}
    (h₁ : OfferDist μ₁ a₁ b₁) (h₂ : OfferDist μ₂ a₂ b₂)
    (hmrl : StochasticOrders.MeanResidualLife.MrlOrder μ₁ μ₂ id id)
    {lam T : ℝ} (hlam : 0 < lam) (hT : 0 < T) :
    (∀ V : ℝ, 0 ≤ V → (V : EReal) < b₁ → Tval μ₂ V ≤ Tval μ₁ V) ∧
    Tinv μ₁ b₁ (lam * T) ≤ Tinv μ₂ b₂ (lam * T) ∧
    (∀ u sh₁ sh₂ : ℝ, 0 < u → (u : EReal) < b₁ →
      IsSHat μ₁ a₁ b₁ u sh₁ → IsSHat μ₂ a₂ b₂ u sh₂ → sh₂ ≤ sh₁) := by
  obtain ⟨hmean, hb12, hL12⟩ := lemma_4 h₁ h₂ hmrl
  obtain ⟨hLpos1, hmono1, hinv1, _⟩ := tval_bijection h₁
  obtain ⟨hLpos2, hmono2, hinv2, _⟩ := tval_bijection h₂
  obtain ⟨hcm1, _, _, _⟩ := sHat_wellDefined h₁
  obtain ⟨hcm2, _, _, _⟩ := sHat_wellDefined h₂
  -- (A) 𝒯₂ ≤ 𝒯₁ on [0, b₁)
  have hA : ∀ V : ℝ, 0 ≤ V → (V : EReal) < b₁ → Tval μ₂ V ≤ Tval μ₁ V := by
    intro V hV0 hVb
    have hpos : ∀ v ∈ Set.Icc 0 V, 0 < Lfun μ₁ v := fun v hv =>
      hLpos1 v hv.1 (lt_of_le_of_lt (EReal.coe_le_coe_iff.mpr hv.2) hVb)
    have hc1 : ContinuousOn (fun v => 1 / Lfun μ₁ v) (Set.uIcc 0 V) := by
      rw [Set.uIcc_of_le hV0]
      exact ContinuousOn.div continuousOn_const (L_cont h₁).continuousOn
        (fun v hv => (hpos v hv).ne')
    have hc2 : ContinuousOn (fun v => 1 / Lfun μ₂ v) (Set.uIcc 0 V) := by
      rw [Set.uIcc_of_le hV0]
      exact ContinuousOn.div continuousOn_const (L_cont h₂).continuousOn
        (fun v hv => (lt_of_lt_of_le (hpos v hv) (hL12 v)).ne')
    unfold Tval
    apply intervalIntegral.integral_mono_on hV0 hc2.intervalIntegrable hc1.intervalIntegrable
    intro v hv
    exact one_div_le_one_div_of_le (hpos v hv) (hL12 v)
  refine ⟨hA, ?_, ?_⟩
  · -- (B)
    obtain ⟨hV10, hV1b, hTV1⟩ := hinv1 (lam * T) (by positivity)
    obtain ⟨hV20, hV2b, hTV2⟩ := hinv2 (lam * T) (by positivity)
    by_contra hcon
    push Not at hcon
    have hV1b2 : (Tinv μ₁ b₁ (lam * T) : EReal) < b₂ := lt_of_lt_of_le hV1b hb12
    have h1 := hmono2 ⟨hV20, hV2b⟩ ⟨hV10, hV1b2⟩ hcon
    have h2 := hA _ hV10 hV1b
    linarith
  · -- (C)
    intro u sh₁ sh₂ hu hub1 hsh₁ hsh₂
    have hub2 : (u : EReal) < b₂ := lt_of_lt_of_le hub1 hb12
    rcases hsh₁ with ⟨hbu, _⟩ | ⟨hm1, _, has1, hsb1, hc1⟩ | ⟨hlt1, he1⟩
    · exact absurd (lt_of_lt_of_le hub1 hbu) (lt_irrefl _)
    · rcases hsh₂ with ⟨hbu, _⟩ | ⟨hm2, _, has2, hsb2, hc2⟩ | ⟨_, he2⟩
      · exact absurd (lt_of_lt_of_le hub2 hbu) (lt_irrefl _)
      · by_contra hcon
        push Not at hcon
        have hsh1b2 : (sh₁ : EReal) < b₂ :=
          lt_trans (EReal.coe_lt_coe_iff.mpr hcon) hsb2
        have hF1 := F_pos h₁ sh₁ hsb1
        have hF2 := F_pos h₂ sh₁ hsh1b2
        have hcm12 : condMean μ₁ sh₁ ≤ condMean μ₂ sh₁ := by
          rw [condMean_eq_add_mrl h₁ sh₁ hF1, condMean_eq_add_mrl h₂ sh₁ hF2]
          linarith [hmrl sh₁]
        rcases le_or_gt a₂ sh₁ with ha2 | ha2
        · have := hcm2 ⟨ha2, hsh1b2⟩ ⟨has2, hsb2⟩ hcon
          linarith
        · obtain ⟨t₀, ht₀1, ht₀2⟩ := EReal.lt_iff_exists_real_btwn.mp hsb1
          have ht₀ : sh₁ < t₀ := EReal.coe_lt_coe_iff.mp ht₀1
          set t := min t₀ ((sh₁ + a₂) / 2) with htdef
          have hst : sh₁ < t := lt_min ht₀ (by linarith)
          have hta2 : t < a₂ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
          have htb1 : (t : EReal) < b₁ :=
            lt_of_le_of_lt (EReal.coe_le_coe_iff.mpr (min_le_left _ _)) ht₀2
          have htb2 : (t : EReal) < b₂ := lt_of_lt_of_le htb1 hb12
          have hmono := hcm1 ⟨has1, hsb1⟩ ⟨le_trans has1 hst.le, htb1⟩ hst
          have hct2 : condMean μ₂ t = mean μ₂ := condMean_eq_mean h₂ t hta2.le
          have e1 := condMean_eq_add_mrl h₁ t (F_pos h₁ t htb1)
          have e2 := condMean_eq_add_mrl h₂ t (F_pos h₂ t htb2)
          have hmt := hmrl t
          linarith
      · rw [he2]; exact le_trans h₁.a_nonneg has1
    · rcases hsh₂ with ⟨hbu, _⟩ | ⟨hm2, _, _, _, _⟩ | ⟨_, he2⟩
      · exact absurd (lt_of_lt_of_le hub2 hbu) (lt_irrefl _)
      · linarith
      · rw [he1, he2]
