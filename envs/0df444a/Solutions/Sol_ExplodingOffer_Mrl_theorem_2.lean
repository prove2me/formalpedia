-- Prove2me | solution 1 for ExplodingOffer.Mrl.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T23:25:48.803529+00:00
-- url     : https://prove2.me/submissions/16fad243-83ef-43a5-9e6f-bc5847417438

import Mathlib
import Definitions.Def_StochasticOrders_MeanResidualLife_MrlOrder
import Definitions.Def_ExplodingOffer_Mrl_Model
import Theorems.Thm_ExplodingOffer_Mrl_tval_bijection
import Theorems.Thm_ExplodingOffer_Mrl_eq_5_6
import Theorems.Thm_ExplodingOffer_Mrl_proposition_1
import Theorems.Thm_ExplodingOffer_Mrl_sHat_wellDefined

open MeasureTheory
open ExplodingOffer.Mrl

namespace T2Aux

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

lemma F_pos (hμ : OfferDist μ a b) (v : ℝ) (hv : (v : EReal) < b) :
    0 < (μ (Set.Ioi v)).toReal := by
  haveI := hμ.isProb
  exact ENNReal.toReal_pos (Ioi_pos hμ v hv).ne' (measure_ne_top _ _)

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

lemma L_strictAnti (hμ : OfferDist μ a b) {v w : ℝ} (hvw : v < w) (hw : (w : EReal) < b) :
    Lfun μ w < Lfun μ v := by
  have h := strictAntiOn_of_deriv_neg (convex_Icc v w) (L_cont hμ).continuousOn (by
    intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivAt_L hμ x).deriv]
    have := F_pos hμ x (lt_trans (EReal.coe_lt_coe_iff.mpr hx.2) hw)
    linarith)
  exact h ⟨le_rfl, hvw.le⟩ ⟨hvw.le, le_rfl⟩ hvw

lemma mrl_pos_eq (hμ : OfferDist μ a b) (s : ℝ) (hs : (s : EReal) < b) :
    condMean μ s = s + Lfun μ s / (μ (Set.Ioi s)).toReal := by
  have hF := F_pos hμ s hs
  rw [condMean_eq_add_mrl hμ s hF, mrl_eq, if_pos hF]

lemma condMean_gt (hμ : OfferDist μ a b) (s : ℝ) (hs : (s : EReal) < b) : s < condMean μ s := by
  rw [mrl_pos_eq hμ s hs]
  have := div_pos (L_pos hμ s hs) (F_pos hμ s hs)
  linarith

lemma condMean_le_r (hμ : OfferDist μ a b) (r : ℝ) (hb : b = (r : EReal)) (s : ℝ)
    (hs : (s : EReal) < b) : condMean μ s ≤ r := by
  haveI := hμ.isProb
  have hF := F_pos hμ s hs
  have hL : Lfun μ s ≤ (r - s) * (μ (Set.Ioi s)).toReal := by
    have hae : ∀ᵐ x ∂μ, max (x - s) 0 ≤ (Set.Ioi s).indicator (fun _ => r - s) x := by
      have h0 : ∀ᵐ x ∂μ, x ≤ r := by
        rw [ae_iff]
        have : {x : ℝ | ¬ x ≤ r} = {x : ℝ | b < (x : EReal)} := by
          ext x; simp [hb, not_le]
        rw [this]; exact hμ.above
      filter_upwards [h0] with x hx
      by_cases hxs : s < x
      · rw [Set.indicator_of_mem (by simpa using hxs)]
        exact max_le (by linarith) (by
          have : s < r := by rw [hb] at hs; exact EReal.coe_lt_coe_iff.mp hs
          linarith)
      · rw [Set.indicator_of_notMem (by simpa using hxs), max_eq_right (by linarith [not_lt.mp hxs])]
    have := integral_mono_ae (intL hμ s) ((integrable_const (r - s)).indicator measurableSet_Ioi) hae
    rw [integral_indicator_const _ measurableSet_Ioi, smul_eq_mul, Measure.real_def] at this
    unfold Lfun; linarith
  rw [mrl_pos_eq hμ s hs]
  have : Lfun μ s / (μ (Set.Ioi s)).toReal ≤ r - s := by
    rw [div_le_iff₀ hF]; exact hL
  linarith

lemma hasDerivAt_h (hμ : OfferDist μ a b) (u s : ℝ) (hs : (s : EReal) < b) :
    HasDerivAt (fun x => (u - x) / Lfun μ x)
      ((μ (Set.Ioi s)).toReal * (u - condMean μ s) / (Lfun μ s) ^ 2) s := by
  have hLs := L_pos hμ s hs
  have hF := F_pos hμ s hs
  have h := ((hasDerivAt_id s).const_sub u).div (hasDerivAt_L hμ s) hLs.ne'
  apply h.congr_deriv
  rw [mrl_pos_eq hμ s hs]
  field_simp
  simp only [id]
  ring

end T2Aux

open T2Aux in
theorem solution {μ : Measure ℝ} {a : ℝ} {b : EReal} (hμ : OfferDist μ a b)
    {lam T u : ℝ} (hlam : 0 < lam) (hT : 0 < T) (hu : 0 < u)
    {sh : ℝ} (hsh : IsSHat μ a b u sh) :
    QuasiconcaveOn ℝ (Set.Icc 0 u) (fun s => surplus μ b lam T u s (optDeadline μ b lam T s)) ∧
    IsOptimalPackage μ b lam T u (min (Tinv μ b (lam * T)) sh)
      (optDeadline μ b lam T (min (Tinv μ b (lam * T)) sh)) ∧
    ((u ≠ mean μ ∨ a = 0) → ∀ s tD : ℝ, IsOptimalPackage μ b lam T u s tD →
      s = min (Tinv μ b (lam * T)) sh ∧
      tD = optDeadline μ b lam T (min (Tinv μ b (lam * T)) sh)) := by
  haveI := hμ.isProb
  obtain ⟨hLpos, hmono, hinv, hleft⟩ := tval_bijection hμ
  obtain ⟨hV0, hVb, hTV⟩ := hinv (lam * T) (by positivity)
  obtain ⟨hp1, _⟩ := proposition_1 hμ hlam hT hu
  obtain ⟨hcm, hcma, _, hshu⟩ := sHat_wellDefined hμ
  have hshu' : sh ≤ u := hshu u sh hu hsh
  set V := Tinv μ b (lam * T) with hVdef
  set m := min V sh with hmdef
  set f := fun s => surplus μ b lam T u s (optDeadline μ b lam T s) with hfdef
  set h := fun x => (u - x) / Lfun μ x with hhdef
  set K := Lfun μ V with hKdef
  have hK : 0 < K := L_pos hμ V hVb
  have hbot : b ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot a) hμ.a_le_b
  -- basic facts on `ŝ`
  have hsh0 : 0 ≤ sh := by
    rcases hsh with ⟨hbu, he⟩ | ⟨_, _, has, _, _⟩ | ⟨_, he⟩
    · rw [he]; exact EReal.toReal_nonneg (le_trans (EReal.coe_nonneg.mpr hμ.a_nonneg) hμ.a_le_b)
    · exact le_trans hμ.a_nonneg has
    · rw [he]
  have hm0 : 0 ≤ m := le_min hV0 hsh0
  have hmV : m ≤ V := min_le_left _ _
  have hmsh : m ≤ sh := min_le_right _ _
  have hmu : m ≤ u := le_trans hmsh hshu'
  have hlt_b : ∀ x, x ≤ V → (x : EReal) < b := fun x hx =>
    lt_of_le_of_lt (EReal.coe_le_coe_iff.mpr hx) hVb
  -- (F1) the surplus of `(s, t*_D(s))` for `s ≤ 𝒯⁻¹(λT)`
  have F1 : ∀ s, 0 ≤ s → s ≤ u → s ≤ V → f s = K * h s := by
    intro s hs0 hsu hsV
    have hsb := hlt_b s hsV
    have hTs : Tval μ s ≤ lam * T := by
      rw [← hTV]; exact hmono.monotoneOn ⟨hs0, hsb⟩ ⟨hV0, hVb⟩ hsV
    obtain ⟨hmin, _, h0, hT'⟩ := (hp1 s hs0 hsu).1
    have h56 := (eq_5_6 hμ hlam hT h0 hT' hmin hsb u).2
    have hopt : optDeadline μ b lam T s = T - Tval μ s / lam := by
      unfold optDeadline; rw [if_pos hsb, max_eq_left]
      rw [sub_nonneg, div_le_iff₀ hlam]; linarith
    have hv0 : valueToGo μ b lam T s (optDeadline μ b lam T s) 0 = V := by
      unfold valueToGo; rw [if_pos h0, if_pos hsb, hopt, hVdef]; congr 1; field_simp; ring
    simp only [hfdef, hhdef]; rw [h56, hv0]; ring
  -- (F2) the surplus of `(s, t*_D(s))` for `s ≥ 𝒯⁻¹(λT)`
  have F2 : ∀ s, V ≤ s → f s = u - s := by
    intro s hVs
    have hopt : optDeadline μ b lam T s = 0 := by
      unfold optDeadline
      split_ifs with hsb
      · apply max_eq_right
        have hs0 : 0 ≤ s := le_trans hV0 hVs
        have : lam * T ≤ Tval μ s := by
          rw [← hTV]; exact hmono.monotoneOn ⟨hV0, hVb⟩ ⟨hs0, hsb⟩ hVs
        rw [sub_nonpos, le_div_iff₀ hlam]; linarith
      · rfl
    simp only [hfdef]; rw [hopt]; simp [surplus, noAcceptProb]
  -- signs of `u − E[X | X ≥ x]`
  have sign1 : ∀ x, 0 ≤ x → x < sh → (x : EReal) < b →
      condMean μ x ≤ u ∧ ((u ≠ mean μ ∨ a = 0) → condMean μ x < u) := by
    intro x hx0 hxsh hxb
    rcases hsh with ⟨hbu, he⟩ | ⟨hmu', hub, hash, hshb, hc⟩ | ⟨hlt, he⟩
    · have htop : b ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top u) hbu
      have hbr : b = ((b.toReal : ℝ) : EReal) := (EReal.coe_toReal htop hbot).symm
      set r := b.toReal with hr
      have hru : r ≤ u := by rw [hbr] at hbu; exact EReal.coe_le_coe_iff.mp hbu
      have hab : a < r := by
        have := a_lt_b hμ; rw [hbr] at this; exact EReal.coe_lt_coe_iff.mp this
      have hxr : x < r := by rw [hbr] at hxb; exact EReal.coe_lt_coe_iff.mp hxb
      set y := max x a with hy
      have hyr : y < r := max_lt hxr hab
      have hcxy : condMean μ x = condMean μ y := by
        rcases le_total x a with hxa | hxa
        · rw [hy, max_eq_right hxa, condMean_eq_mean hμ x hxa, hcma]
        · rw [hy, max_eq_left hxa]
      have hzb : (((y + r) / 2 : ℝ) : EReal) < b := by
        rw [hbr]; exact EReal.coe_lt_coe_iff.mpr (by linarith)
      have h1 := hcm ⟨le_max_right _ _, by rw [hbr]; exact EReal.coe_lt_coe_iff.mpr hyr⟩
        ⟨by linarith [le_max_right x a], hzb⟩ (show y < (y + r) / 2 by linarith)
      have h2 := condMean_le_r hμ r hbr _ hzb
      have : condMean μ x < u := by linarith
      exact ⟨this.le, fun _ => this⟩
    · by_cases hxa : a ≤ x
      · have := hcm ⟨hxa, hxb⟩ ⟨hash, hshb⟩ hxsh
        rw [hc] at this
        exact ⟨this.le, fun _ => this⟩
      · push Not at hxa
        rw [condMean_eq_mean hμ x hxa.le]
        refine ⟨hmu', fun hc' => ?_⟩
        rcases hc' with hne | ha0
        · exact lt_of_le_of_ne hmu' (Ne.symm hne)
        · linarith
    · rw [he] at hxsh; linarith
  have sign2 : ∀ x, sh < x → (x : EReal) < b → u < condMean μ x := by
    intro x hshx hxb
    rcases hsh with ⟨hbu, he⟩ | ⟨hmu', hub, hash, hshb, hc⟩ | ⟨hlt, he⟩
    · have htop : b ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top u) hbu
      have hbr : b = ((b.toReal : ℝ) : EReal) := (EReal.coe_toReal htop hbot).symm
      rw [hbr] at hxb
      have := EReal.coe_lt_coe_iff.mp hxb
      rw [he] at hshx; linarith
    · have := hcm ⟨hash, hshb⟩ ⟨le_trans hash hshx.le, hxb⟩ hshx
      rw [hc] at this; exact this
    · have : mean μ ≤ condMean μ x := by
        rcases le_total x a with hxa | hxa
        · rw [condMean_eq_mean hμ x hxa]
        · rw [← hcma]
          exact hcm.monotoneOn ⟨le_rfl, a_lt_b hμ⟩ ⟨hxa, hxb⟩ hxa
      linarith
  -- monotonicity of `h(s) = (u − s)/ℒ(s)`
  have hcont : ∀ p q, q ≤ V → ContinuousOn h (Set.Icc p q) := by
    intro p q hq
    apply ContinuousOn.div (continuousOn_const.sub continuousOn_id) (L_cont hμ).continuousOn
    intro x hx; exact (L_pos hμ x (hlt_b x (le_trans hx.2 hq))).ne'
  have hderiv : ∀ x, x < V →
      deriv h x = (μ (Set.Ioi x)).toReal * (u - condMean μ x) / (Lfun μ x) ^ 2 :=
    fun x hx => (hasDerivAt_h hμ u x (hlt_b x hx.le)).deriv
  have hdiff : ∀ p q, q ≤ V → DifferentiableOn ℝ h (interior (Set.Icc p q)) := by
    intro p q hq x hx
    rw [interior_Icc] at hx
    exact (hasDerivAt_h hμ u x (hlt_b x (le_trans hx.2.le hq))).differentiableAt.differentiableWithinAt
  have hmonoL : MonotoneOn h (Set.Icc 0 m) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 m) (hcont 0 m hmV) (hdiff 0 m hmV)
    intro x hx
    rw [interior_Icc] at hx
    rw [hderiv x (lt_of_lt_of_le hx.2 hmV)]
    have hxb := hlt_b x (le_trans hx.2.le hmV)
    have := (sign1 x hx.1.le (lt_of_lt_of_le hx.2 hmsh) hxb).1
    have hF := F_pos hμ x hxb
    exact div_nonneg (mul_nonneg hF.le (by linarith)) (sq_nonneg _)
  have hstrictL : (u ≠ mean μ ∨ a = 0) → StrictMonoOn h (Set.Icc 0 m) := by
    intro hc
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 m) (hcont 0 m hmV)
    intro x hx
    rw [interior_Icc] at hx
    rw [hderiv x (lt_of_lt_of_le hx.2 hmV)]
    have hxb := hlt_b x (le_trans hx.2.le hmV)
    have := (sign1 x hx.1.le (lt_of_lt_of_le hx.2 hmsh) hxb).2 hc
    have hF := F_pos hμ x hxb
    have hL := L_pos hμ x hxb
    exact div_pos (mul_pos hF (by linarith)) (by positivity)
  have hantiR : sh < V → StrictAntiOn h (Set.Icc sh V) := by
    intro hshV
    apply strictAntiOn_of_deriv_neg (convex_Icc sh V) (hcont sh V le_rfl)
    intro x hx
    rw [interior_Icc] at hx
    rw [hderiv x hx.2]
    have hxb := hlt_b x hx.2.le
    have := sign2 x hx.1 hxb
    have hF := F_pos hμ x hxb
    have hL := L_pos hμ x hxb
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hF (by linarith)) (by positivity)
  -- comparisons of `f`
  have right_lt : ∀ s, m < s → s ≤ u → f s < f m := by
    intro s hms hsu
    have hs0 : 0 ≤ s := le_trans hm0 hms.le
    rcases lt_or_ge sh V with hshV | hVsh
    · have hmsh' : m = sh := min_eq_right hshV.le
      by_cases hsV : s ≤ V
      · rw [F1 s hs0 hsu hsV, F1 m hm0 hmu hmV]
        apply mul_lt_mul_of_pos_left _ hK
        rw [hmsh'] at hms ⊢
        exact hantiR hshV ⟨le_rfl, hshV.le⟩ ⟨hms.le, hsV⟩ hms
      · push Not at hsV
        have hVu : V ≤ u := le_trans hsV.le hsu
        have e1 := F2 s hsV.le
        have e2 := F2 V le_rfl
        have e3 := F1 V hV0 hVu le_rfl
        have e4 := F1 m hm0 hmu hmV
        have hlt : h V < h m := by
          rw [hmsh']; exact hantiR hshV ⟨le_rfl, hshV.le⟩ ⟨hshV.le, le_rfl⟩ hshV
        have := mul_lt_mul_of_pos_left hlt hK
        rw [e1, e4]
        have : u - s < u - V := by linarith
        linarith
    · have hmV' : m = V := min_eq_left hVsh
      rw [F2 s (by rw [← hmV']; exact hms.le), F2 m (by rw [hmV'])]
      linarith
  have left_le : ∀ s, 0 ≤ s → s ≤ m → f s ≤ f m := by
    intro s hs0 hsm
    rw [F1 s hs0 (le_trans hsm hmu) (le_trans hsm hmV), F1 m hm0 hmu hmV]
    exact mul_le_mul_of_nonneg_left (hmonoL ⟨hs0, hsm⟩ ⟨hm0, le_rfl⟩ hsm) hK.le
  have left_lt : (u ≠ mean μ ∨ a = 0) → ∀ s, 0 ≤ s → s < m → f s < f m := by
    intro hc s hs0 hsm
    rw [F1 s hs0 (le_trans hsm.le hmu) (le_trans hsm.le hmV), F1 m hm0 hmu hmV]
    exact mul_lt_mul_of_pos_left (hstrictL hc ⟨hs0, hsm.le⟩ ⟨hm0, le_rfl⟩ hsm) hK
  have fmax : ∀ s, 0 ≤ s → s ≤ u → f s ≤ f m := fun s hs0 hsu =>
    (le_or_gt s m).elim (left_le s hs0) (fun hlt => (right_lt s hlt hsu).le)
  have hfeas_m := (hp1 m hm0 hmu).1
  have hs_nonneg : ∀ s' tD', Feasible μ b lam T u s' tD' → 0 ≤ s' := fun s' tD' hf' =>
    le_trans (hinv _ (mul_nonneg hlam.le (by linarith [hf'.2.2.2]))).1 hf'.1
  refine ⟨?_, ?_, ?_⟩
  · -- quasi-concavity
    have fmonoL : MonotoneOn f (Set.Icc 0 m) := fun x hx y hy hxy => by
      rw [F1 x hx.1 (le_trans hx.2 hmu) (le_trans hx.2 hmV),
        F1 y hy.1 (le_trans hy.2 hmu) (le_trans hy.2 hmV)]
      exact mul_le_mul_of_nonneg_left (hmonoL hx hy hxy) hK.le
    have fantiR : ∀ x y, m ≤ x → x ≤ y → y ≤ u → f y ≤ f x := by
      intro x y hmx hxy hyu
      have hx0 : 0 ≤ x := le_trans hm0 hmx
      rcases lt_or_ge sh V with hshV | hVsh
      · have hmsh' : m = sh := min_eq_right hshV.le
        rw [hmsh'] at hmx
        by_cases hyV : y ≤ V
        · rw [F1 x hx0 (le_trans hxy hyu) (le_trans hxy hyV), F1 y (le_trans hx0 hxy) hyu hyV]
          exact mul_le_mul_of_nonneg_left
            ((hantiR hshV).antitoneOn ⟨hmx, le_trans hxy hyV⟩ ⟨le_trans hmx hxy, hyV⟩ hxy) hK.le
        · push Not at hyV
          by_cases hxV : V ≤ x
          · rw [F2 x hxV, F2 y (le_trans hxV hxy)]; linarith
          · push Not at hxV
            have hVu : V ≤ u := le_trans hyV.le hyu
            rw [F2 y hyV.le, F1 x hx0 (le_trans hxy hyu) hxV.le]
            have e3 := F1 V hV0 hVu le_rfl
            have e2 := F2 V le_rfl
            have := mul_le_mul_of_nonneg_left
              ((hantiR hshV).antitoneOn ⟨hmx, hxV.le⟩ ⟨hshV.le, le_rfl⟩ hxV.le) hK.le
            linarith
      · have hmV' : m = V := min_eq_left hVsh
        rw [hmV'] at hmx
        rw [F2 x hmx, F2 y (le_trans hmx hxy)]; linarith
    intro r
    rw [convex_iff_ordConnected]
    refine ⟨fun x hx z hz y hy => ?_⟩
    refine ⟨⟨le_trans hx.1.1 hy.1, le_trans hy.2 hz.1.2⟩, ?_⟩
    by_cases hym : y ≤ m
    · exact le_trans hx.2 (fmonoL ⟨hx.1.1, le_trans hy.1 hym⟩ ⟨le_trans hx.1.1 hy.1, hym⟩ hy.1)
    · push Not at hym
      exact le_trans hz.2 (fantiR y z hym.le hy.2 hz.1.2)
  · -- optimality
    refine ⟨hfeas_m, ?_⟩
    intro s' tD' hf'
    have hs'0 := hs_nonneg s' tD' hf'
    exact le_trans ((hp1 s' hs'0 hf'.2.1).2 tD' hf') (fmax s' hs'0 hf'.2.1)
  · -- uniqueness
    intro hc s tD hst
    obtain ⟨hfs, hmaxs⟩ := hst
    have hs0 := hs_nonneg s tD hfs
    have hsu := hfs.2.1
    have h1 : f m ≤ surplus μ b lam T u s tD := hmaxs _ _ hfeas_m
    have h2 : surplus μ b lam T u s tD ≤ f s := (hp1 s hs0 hsu).2 tD hfs
    have hsm : s = m := by
      rcases lt_trichotomy s m with hlt | heq | hgt
      · have := left_lt hc s hs0 hlt; linarith
      · exact heq
      · have := right_lt s hgt hsu; linarith
    refine ⟨hsm, ?_⟩
    rw [hsm] at hfs h1
    obtain ⟨hmin, _, htD0, htDT⟩ := hfs
    have hmb := hlt_b m hmV
    have hTm : Tval μ m ≤ lam * T := by
      rw [← hTV]; exact hmono.monotoneOn ⟨hm0, hmb⟩ ⟨hV0, hVb⟩ hmV
    have hopt : optDeadline μ b lam T m = T - Tval μ m / lam := by
      unfold optDeadline; rw [if_pos hmb, max_eq_left]
      rw [sub_nonneg, div_le_iff₀ hlam]; linarith
    by_contra hne
    have hge : T - Tval μ m / lam ≤ tD := by
      by_contra hlt
      push Not at hlt
      have hy : Tval μ m < lam * (T - tD) := by
        rw [lt_sub_comm, div_lt_iff₀ hlam] at hlt; linarith
      obtain ⟨hy0, hyb, hyT⟩ := hinv (lam * (T - tD)) (mul_nonneg hlam.le (by linarith))
      have : m < Tinv μ b (lam * (T - tD)) := by
        by_contra hc'
        push Not at hc'
        have := hmono.monotoneOn ⟨hy0, hyb⟩ ⟨hm0, hmb⟩ hc'
        linarith
      unfold minAccept at hmin
      linarith
    have hgt : T - Tval μ m / lam < tD := lt_of_le_of_ne hge (by rw [← hopt]; exact Ne.symm hne)
    have hargV : lam * T < Tval μ m + lam * tD := by
      have := mul_lt_mul_of_pos_left hgt hlam
      have e : lam * (T - Tval μ m / lam) = lam * T - Tval μ m := by field_simp
      linarith
    obtain ⟨hW0, hWb, hTW⟩ := hinv (Tval μ m + lam * tD) (by have := mul_pos hlam hT; linarith)
    have hVW : V < Tinv μ b (Tval μ m + lam * tD) := by
      by_contra hc'
      push Not at hc'
      have := hmono.monotoneOn ⟨hW0, hWb⟩ ⟨hV0, hVb⟩ hc'
      linarith
    have hLW : Lfun μ (Tinv μ b (Tval μ m + lam * tD)) < K := L_strictAnti hμ hVW hWb
    -- `m < u`
    have hmu_lt : m < u := by
      rcases hsh with ⟨hbu, he⟩ | ⟨hmu', hub, hash, hshb, hcc⟩ | ⟨hlt, he⟩
      · have : (m : EReal) < u := lt_of_lt_of_le hmb hbu
        exact EReal.coe_lt_coe_iff.mp this
      · have := condMean_gt hμ sh hshb
        rw [hcc] at this; linarith
      · rw [he] at hmsh; linarith
    have h56 := (eq_5_6 hμ hlam hT htD0 htDT hmin hmb u).2
    have hv0 : valueToGo μ b lam T m tD 0 = Tinv μ b (Tval μ m + lam * tD) := by
      unfold valueToGo; rw [if_pos htD0, if_pos hmb]; congr 1; ring
    rw [h56, hv0, F1 m hm0 hmu hmV] at h1
    have hLm := L_pos hμ m hmb
    have : (u - m) * (Lfun μ (Tinv μ b (Tval μ m + lam * tD)) / Lfun μ m) <
        K * ((u - m) / Lfun μ m) := by
      rw [mul_div_assoc', mul_div_assoc', mul_comm K]
      apply div_lt_div_of_pos_right _ hLm
      exact mul_lt_mul_of_pos_left hLW (by linarith)
    simp only [hhdef] at h1
    linarith
