-- Prove2me | solution 1 for ExplodingOffer.Mrl.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T23:09:50.257207+00:00
-- url     : https://prove2.me/submissions/6f7e4027-b3bd-4c24-be66-af953872cb4c

import Mathlib
import Definitions.Def_StochasticOrders_MeanResidualLife_MrlOrder
import Definitions.Def_ExplodingOffer_Mrl_Model

open MeasureTheory
open ExplodingOffer.Mrl

namespace Lem4Aux

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

lemma L_eq_mean_sub (hμ : OfferDist μ a b) (t : ℝ) (ht : t ≤ a) :
    Lfun μ t = mean μ - t := by
  haveI := hμ.isProb
  have hae : ∀ᵐ x ∂μ, max (x - t) 0 = x - t := by
    have h0 : ∀ᵐ x ∂μ, a ≤ x := by
      rw [ae_iff]
      have : {x : ℝ | ¬ a ≤ x} = Set.Iio a := by ext x; simp
      rw [this]; exact hμ.below
    filter_upwards [h0] with x hx
    exact max_eq_left (by linarith)
  unfold Lfun
  rw [integral_congr_ae hae, integral_sub hμ.integrable (integrable_const t)]
  simp [mean]

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

lemma mrl_eq (t : ℝ) :
    StochasticOrders.MeanResidualLife.mrl μ id t =
      if 0 < (μ (Set.Ioi t)).toReal then Lfun μ t / (μ (Set.Ioi t)).toReal else 0 := by
  unfold StochasticOrders.MeanResidualLife.mrl
  have hset : {ω : ℝ | t < id ω} = Set.Ioi t := rfl
  have hint : ∫ ω in {ω : ℝ | t < id ω}, (id ω - t) ∂μ = Lfun μ t := by
    rw [hset, ← integral_indicator measurableSet_Ioi]
    unfold Lfun
    congr 1
    funext x
    by_cases hx : t < x
    · rw [Set.indicator_of_mem (by simpa using hx)]
      simp only [id]
      exact (max_eq_left (by linarith)).symm
    · rw [Set.indicator_of_notMem (by simpa using hx)]
      exact (max_eq_right (by linarith [not_lt.mp hx])).symm
  rw [hint, hset]

lemma cross {μ₁ μ₂ : Measure ℝ}
    (hmrl : StochasticOrders.MeanResidualLife.MrlOrder μ₁ μ₂ id id) (t : ℝ)
    (hF1 : 0 < (μ₁ (Set.Ioi t)).toReal) :
    Lfun μ₁ t * (μ₂ (Set.Ioi t)).toReal ≤ Lfun μ₂ t * (μ₁ (Set.Ioi t)).toReal := by
  have h := hmrl t
  rw [mrl_eq, mrl_eq, if_pos hF1] at h
  by_cases hF2 : 0 < (μ₂ (Set.Ioi t)).toReal
  · rw [if_pos hF2, div_le_div_iff₀ hF1 hF2] at h
    linarith
  · have : (μ₂ (Set.Ioi t)).toReal = 0 :=
      le_antisymm (not_lt.mp hF2) ENNReal.toReal_nonneg
    rw [this, mul_zero]
    exact mul_nonneg (L_nonneg t) ENNReal.toReal_nonneg

lemma F_pos (hμ : OfferDist μ a b) (v : ℝ) (hv : (v : EReal) < b) :
    0 < (μ (Set.Ioi v)).toReal := by
  haveI := hμ.isProb
  exact ENNReal.toReal_pos (Ioi_pos hμ v hv).ne' (measure_ne_top _ _)

lemma L_le {μ₁ μ₂ : Measure ℝ} {a₁ a₂ : ℝ} {b₁ b₂ : EReal}
    (h₁ : OfferDist μ₁ a₁ b₁) (h₂ : OfferDist μ₂ a₂ b₂)
    (hmrl : StochasticOrders.MeanResidualLife.MrlOrder μ₁ μ₂ id id) (s : ℝ) :
    Lfun μ₁ s ≤ Lfun μ₂ s := by
  by_cases hs : (s : EReal) < b₁
  · -- the ratio `L₂ / L₁` is nondecreasing on `(-∞, s]`
    have hmono : ∀ t', t' ≤ s → Lfun μ₂ t' / Lfun μ₁ t' ≤ Lfun μ₂ s / Lfun μ₁ s := by
      intro t' ht'
      have hlt : ∀ t, t ≤ s → (t : EReal) < b₁ :=
        fun t ht => lt_of_le_of_lt (EReal.coe_le_coe_iff.mpr ht) hs
      have hmon : MonotoneOn (fun t => Lfun μ₂ t / Lfun μ₁ t) (Set.Icc t' s) := by
        apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc t' s)
          (f' := fun t => ((-(μ₂ (Set.Ioi t)).toReal) * Lfun μ₁ t -
              Lfun μ₂ t * (-(μ₁ (Set.Ioi t)).toReal)) / (Lfun μ₁ t) ^ 2)
        · apply ContinuousOn.div (L_cont h₂).continuousOn (L_cont h₁).continuousOn
          intro t ht
          exact (L_pos h₁ t (hlt t ht.2)).ne'
        · intro t ht
          rw [interior_Icc] at ht
          exact ((hasDerivAt_L h₂ t).div (hasDerivAt_L h₁ t)
            (L_pos h₁ t (hlt t ht.2.le)).ne').hasDerivWithinAt
        · intro t ht
          rw [interior_Icc] at ht
          apply div_nonneg _ (sq_nonneg _)
          have := cross hmrl t (F_pos h₁ t (hlt t ht.2.le))
          linarith
      exact hmon ⟨le_rfl, ht'⟩ ⟨ht', le_rfl⟩ ht'
    by_contra hcon
    push Not at hcon
    set D := Lfun μ₁ s - Lfun μ₂ s with hD
    have hDpos : 0 < D := by linarith
    set C := Lfun μ₂ s * mean μ₁ - Lfun μ₁ s * mean μ₂ with hC
    set t' := min (min s 0) (-(|C| / D) - 1) with ht'
    have ht's : t' ≤ s := le_trans (min_le_left _ _) (min_le_left _ _)
    have ht'0 : t' ≤ 0 := le_trans (min_le_left _ _) (min_le_right _ _)
    have ht'K : t' ≤ -(|C| / D) - 1 := min_le_right _ _
    have hL1t := L_eq_mean_sub h₁ t' (le_trans ht'0 h₁.a_nonneg)
    have hL2t := L_eq_mean_sub h₂ t' (le_trans ht'0 h₂.a_nonneg)
    have hpos1 : 0 < Lfun μ₁ t' := L_pos h₁ t' (lt_of_le_of_lt (EReal.coe_le_coe_iff.mpr ht's) hs)
    have hpos1s : 0 < Lfun μ₁ s := L_pos h₁ s hs
    have hm := hmono t' ht's
    rw [div_le_div_iff₀ hpos1 hpos1s, hL1t, hL2t] at hm
    rw [hL1t] at hpos1
    -- hm : (m₂ - t') * L₁ s ≤ L₂ s * (m₁ - t')
    have h1 : (-t') * D ≤ C := by rw [hD, hC]; nlinarith
    have h2 : (|C| / D + 1) * D ≤ (-t') * D :=
      mul_le_mul_of_nonneg_right (by linarith) hDpos.le
    have h3 : (|C| / D + 1) * D = |C| + D := by field_simp
    have := le_abs_self C
    linarith
  · push Not at hs
    induction b₁ using EReal.rec with
    | bot => exact absurd h₁.a_le_b (by simp)
    | top => exact absurd hs (by simp)
    | coe r =>
      rw [L_zero h₁ r rfl s (EReal.coe_le_coe_iff.mp hs)]
      exact L_nonneg s

end Lem4Aux

open Lem4Aux in
theorem solution {μ₁ μ₂ : Measure ℝ} {a₁ a₂ : ℝ} {b₁ b₂ : EReal}
    (h₁ : OfferDist μ₁ a₁ b₁) (h₂ : OfferDist μ₂ a₂ b₂)
    (hmrl : StochasticOrders.MeanResidualLife.MrlOrder μ₁ μ₂ id id) :
    mean μ₁ ≤ mean μ₂ ∧ b₁ ≤ b₂ ∧ ∀ s : ℝ, Lfun μ₁ s ≤ Lfun μ₂ s := by
  have hL := L_le h₁ h₂ hmrl
  refine ⟨?_, ?_, hL⟩
  · have := hL 0
    rw [L_eq_mean_sub h₁ 0 h₁.a_nonneg, L_eq_mean_sub h₂ 0 h₂.a_nonneg] at this
    linarith
  · by_contra hcon
    push Not at hcon
    induction b₂ using EReal.rec with
    | bot => exact absurd h₂.a_le_b (by simp)
    | top => exact absurd hcon (by simp)
    | coe r =>
      have h0 := L_zero h₂ r rfl r le_rfl
      have hp := L_pos h₁ r hcon
      have := hL r
      linarith
