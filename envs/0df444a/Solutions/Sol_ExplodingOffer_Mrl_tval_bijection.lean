-- Prove2me | solution 1 for ExplodingOffer.Mrl.tval_bijection
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T23:06:44.189466+00:00
-- url     : https://prove2.me/submissions/7fdba486-b5e8-4df0-863b-515a5442134f

import Mathlib
import Definitions.Def_ExplodingOffer_Mrl_Model

open MeasureTheory
open ExplodingOffer.Mrl

namespace TvalAux

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

lemma invL_contOn (hμ : OfferDist μ a b) (W : ℝ) (hW : (W : EReal) < b) :
    ContinuousOn (fun v => 1 / Lfun μ v) (Set.Ici 0 ∩ Set.Iic W) := by
  apply ContinuousOn.div continuousOn_const (L_cont hμ).continuousOn
  intro v hv
  have : 0 < Lfun μ v := by
    have h1 := L_pos hμ W hW
    have h2 := L_anti hμ hv.2
    linarith
  exact this.ne'

lemma intervalInt (hμ : OfferDist μ a b) (W : ℝ) (hW0 : 0 ≤ W) (hW : (W : EReal) < b)
    (x y : ℝ) (hx : x ∈ Set.Icc 0 W) (hy : y ∈ Set.Icc 0 W) :
    IntervalIntegrable (fun v => 1 / Lfun μ v) MeasureTheory.volume x y := by
  apply ContinuousOn.intervalIntegrable
  apply (invL_contOn hμ W hW).mono
  intro z hz
  rw [Set.mem_uIcc] at hz
  constructor
  · rcases hz with h | h
    · exact le_trans hx.1 h.1
    · exact le_trans hy.1 h.1
  · rcases hz with h | h
    · exact le_trans h.2 hy.2
    · exact le_trans h.2 hx.2

lemma Tval_strictMono (hμ : OfferDist μ a b) :
    StrictMonoOn (Tval μ) {V : ℝ | 0 ≤ V ∧ (V : EReal) < b} := by
  intro V hV W hW hVW
  have hI0V := intervalInt hμ W hW.1 hW.2 0 V ⟨le_rfl, hW.1⟩ ⟨hV.1, hVW.le⟩
  have hIVW := intervalInt hμ W hW.1 hW.2 V W ⟨hV.1, hVW.le⟩ ⟨hW.1, le_rfl⟩
  have hsplit : Tval μ W = Tval μ V + ∫ v in V..W, 1 / Lfun μ v := by
    unfold Tval
    rw [intervalIntegral.integral_add_adjacent_intervals hI0V hIVW]
  have hpos : 0 < ∫ v in V..W, 1 / Lfun μ v := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on hIVW _ hVW
    intro x hx
    have : 0 < Lfun μ x := by
      have h1 := L_pos hμ W hW.2
      have h2 := L_anti hμ hx.2.le
      linarith
    positivity
  linarith

lemma Tval_zero : Tval μ 0 = 0 := by simp [Tval]

lemma Tval_contOn (hμ : OfferDist μ a b) (W : ℝ) (hW0 : 0 ≤ W) (hW : (W : EReal) < b) :
    ContinuousOn (Tval μ) (Set.Icc 0 W) := by
  have h := intervalIntegral.continuousOn_primitive_interval (μ := MeasureTheory.volume)
    (f := fun v => 1 / Lfun μ v) (a := 0) (b := W) ?_
  · rw [Set.uIcc_of_le hW0] at h
    exact h
  · rw [Set.uIcc_of_le hW0]
    apply ContinuousOn.integrableOn_Icc
    apply (invL_contOn hμ W hW).mono
    intro z hz; exact ⟨hz.1, hz.2⟩

lemma b_pos_of_coe (hμ : OfferDist μ a b) (r : ℝ) (hb : b = (r : EReal)) : 0 < r := by
  have h1 := hμ.a_le_b
  have h2 := hμ.b_ne_zero
  rw [hb] at h1 h2
  have : a ≤ r := EReal.coe_le_coe_iff.mp h1
  have : r ≠ 0 := by intro h; apply h2; rw [h]; rfl
  have := hμ.a_nonneg
  rcases lt_or_eq_of_le (le_trans this (by assumption : a ≤ r)) with h | h
  · exact h
  · exact absurd h.symm ‹r ≠ 0›

lemma unbounded (hμ : OfferDist μ a b) (y : ℝ) (hy : 0 ≤ y) :
    ∃ W : ℝ, 0 ≤ W ∧ (W : EReal) < b ∧ y ≤ Tval μ W := by
  induction b using EReal.rec with
  | bot => exact absurd hμ.a_le_b (by simp)
  | top =>
    have hL0 : 0 < Lfun μ 0 := L_pos hμ 0 (by simp)
    refine ⟨y * Lfun μ 0, by positivity, EReal.coe_lt_top _, ?_⟩
    set W := y * Lfun μ 0 with hWdef
    have hW0 : 0 ≤ W := by positivity
    have hle : ∫ v in (0:ℝ)..W, (1 / Lfun μ 0) ≤ Tval μ W := by
      unfold Tval
      apply intervalIntegral.integral_mono_on hW0 intervalIntegrable_const
        (intervalInt hμ W hW0 (by simp) 0 W ⟨le_rfl, hW0⟩ ⟨hW0, le_rfl⟩)
      intro v hv
      have hLv : 0 < Lfun μ v := L_pos hμ v (by simp)
      have := L_anti hμ hv.1
      exact one_div_le_one_div_of_le hLv this
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hle
    have : W * (1 / Lfun μ 0) = y := by rw [hWdef]; field_simp
    linarith
  | coe r =>
    haveI := hμ.isProb
    have hr : 0 < r := b_pos_of_coe hμ r rfl
    set W := r - r * Real.exp (-y) with hWdef
    have hexp : Real.exp (-y) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hexp0 : 0 < Real.exp (-y) := Real.exp_pos _
    have hW0 : 0 ≤ W := by rw [hWdef]; nlinarith
    have hWr : W < r := by rw [hWdef]; nlinarith
    have hWb : (W : EReal) < (r : EReal) := EReal.coe_lt_coe_iff.mpr hWr
    refine ⟨W, hW0, hWb, ?_⟩
    have hae : ∀ᵐ x ∂μ, x ≤ r := by
      rw [ae_iff]
      have : {x : ℝ | ¬ x ≤ r} = {x : ℝ | (r : EReal) < (x : EReal)} := by
        ext x; simp [not_le]
      rw [this]; exact hμ.above
    have hLle : ∀ v : ℝ, v ≤ r → Lfun μ v ≤ r - v := by
      intro v hv
      have := integral_mono_ae (intL hμ v) (integrable_const (r - v)) (by
        filter_upwards [hae] with x hx
        exact max_le (by linarith) (by linarith))
      simpa [Lfun] using this
    have hcont : ContinuousOn (fun v : ℝ => 1 / (r - v)) (Set.uIcc 0 W) := by
      apply ContinuousOn.div continuousOn_const (continuousOn_const.sub continuousOn_id)
      intro v hv
      rw [Set.uIcc_of_le hW0] at hv
      have := hv.2
      exact (show (0:ℝ) < r - v by linarith).ne'
    have hle : ∫ v in (0:ℝ)..W, 1 / (r - v) ≤ Tval μ W := by
      unfold Tval
      apply intervalIntegral.integral_mono_on hW0 (hcont.intervalIntegrable)
        (intervalInt hμ W hW0 hWb 0 W ⟨le_rfl, hW0⟩ ⟨hW0, le_rfl⟩)
      intro v hv
      have hLv : 0 < Lfun μ v := L_pos hμ v
        (EReal.coe_lt_coe_iff.mpr (lt_of_le_of_lt hv.2 hWr))
      exact one_div_le_one_div_of_le hLv (hLle v (le_trans hv.2 hWr.le))
    have hcalc : ∫ v in (0:ℝ)..W, 1 / (r - v) = y := by
      have := intervalIntegral.integral_comp_sub_left (a := 0) (b := W)
        (fun x : ℝ => 1 / x) r
      rw [this, sub_zero, integral_one_div_of_pos (by linarith) hr]
      have : r / (r - W) = Real.exp y := by
        rw [hWdef]
        have : r - (r - r * Real.exp (-y)) = r * Real.exp (-y) := by ring
        rw [this, Real.exp_neg]
        field_simp
      rw [this, Real.log_exp]
    linarith

lemma Tinv_eq (hμ : OfferDist μ a b) (y V : ℝ) (hV0 : 0 ≤ V) (hVb : (V : EReal) < b)
    (hTV : Tval μ V = y) : Tinv μ b y = V := by
  unfold Tinv
  apply IsGreatest.csSup_eq
  refine ⟨⟨hV0, hVb, le_of_eq hTV⟩, ?_⟩
  rintro W ⟨hW0, hWb, hWy⟩
  by_contra h
  push Not at h
  have := Tval_strictMono hμ ⟨hV0, hVb⟩ ⟨hW0, hWb⟩ h
  linarith

end TvalAux

open TvalAux in
theorem solution {μ : Measure ℝ} {a : ℝ} {b : EReal} (hμ : OfferDist μ a b) :
    (∀ v : ℝ, 0 ≤ v → (v : EReal) < b → 0 < Lfun μ v) ∧
    StrictMonoOn (Tval μ) {V : ℝ | 0 ≤ V ∧ (V : EReal) < b} ∧
    (∀ y : ℝ, 0 ≤ y →
      0 ≤ Tinv μ b y ∧ (Tinv μ b y : EReal) < b ∧ Tval μ (Tinv μ b y) = y) ∧
    (∀ V : ℝ, 0 ≤ V → (V : EReal) < b → Tinv μ b (Tval μ V) = V) := by
  have h0b : ((0 : ℝ) : EReal) < b := by
    induction b using EReal.rec with
    | bot => exact absurd hμ.a_le_b (by simp)
    | top => simp
    | coe r => exact EReal.coe_lt_coe_iff.mpr (b_pos_of_coe hμ r rfl)
  refine ⟨fun v _ hv => L_pos hμ v hv, Tval_strictMono hμ, ?_, ?_⟩
  · intro y hy
    obtain ⟨W, hW0, hWb, hyW⟩ := unbounded hμ y hy
    obtain ⟨c, hc, hTc⟩ := intermediate_value_Icc hW0 (Tval_contOn hμ W hW0 hWb)
      (show y ∈ Set.Icc (Tval μ 0) (Tval μ W) by rw [Tval_zero]; exact ⟨hy, hyW⟩)
    have hcb : (c : EReal) < b := lt_of_le_of_lt (EReal.coe_le_coe_iff.mpr hc.2) hWb
    rw [Tinv_eq hμ y c hc.1 hcb hTc]
    exact ⟨hc.1, hcb, hTc⟩
  · intro V hV0 hVb
    exact Tinv_eq hμ _ V hV0 hVb rfl
