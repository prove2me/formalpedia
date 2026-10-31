-- Prove2me | solution 1 for ExplodingOffer.Mrl.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T23:03:48.122984+00:00
-- url     : https://prove2.me/submissions/99abd39d-b8f5-424d-bac2-f449575747e8

import Mathlib
import Definitions.Def_StochasticOrders_MeanResidualLife_MrlOrder
import Definitions.Def_ExplodingOffer_Mrl_Model
import Theorems.Thm_ExplodingOffer_Mrl_theorem_2
import Theorems.Thm_ExplodingOffer_Mrl_tval_bijection
import Theorems.Thm_ExplodingOffer_Mrl_eq_5_6
import Theorems.Thm_ExplodingOffer_Mrl_theorem_3_order_steps

open MeasureTheory
open ExplodingOffer.Mrl

namespace MrlT3Aux

lemma mean_le_b {μ : Measure ℝ} {a : ℝ} {b : EReal} (hμ : OfferDist μ a b) (r : ℝ)
    (hb : b = (r : EReal)) : mean μ ≤ r := by
  haveI := hμ.isProb
  have hae : ∀ᵐ x ∂μ, x ≤ r := by
    rw [ae_iff]
    have : {x : ℝ | ¬ x ≤ r} = {x : ℝ | b < (x : EReal)} := by
      ext x; simp [hb, not_le]
    rw [this]; exact hμ.above
  have := integral_mono_ae hμ.integrable (integrable_const r) hae
  simpa [mean] using this

lemma a_le_mean {μ : Measure ℝ} {a : ℝ} {b : EReal} (hμ : OfferDist μ a b) : a ≤ mean μ := by
  haveI := hμ.isProb
  have hae : ∀ᵐ x ∂μ, a ≤ x := by
    rw [ae_iff]
    have : {x : ℝ | ¬ a ≤ x} = Set.Iio a := by ext x; simp
    rw [this]; exact hμ.below
  have := integral_mono_ae (integrable_const a) hμ.integrable hae
  simpa [mean] using this

lemma L_at_a {μ : Measure ℝ} {a : ℝ} {b : EReal} (hμ : OfferDist μ a b) :
    Lfun μ a = mean μ - a := by
  haveI := hμ.isProb
  have hae : ∀ᵐ x ∂μ, max (x - a) 0 = x - a := by
    have h0 : ∀ᵐ x ∂μ, a ≤ x := by
      rw [ae_iff]
      have : {x : ℝ | ¬ a ≤ x} = Set.Iio a := by ext x; simp
      rw [this]; exact hμ.below
    filter_upwards [h0] with x hx
    exact max_eq_left (by linarith)
  unfold Lfun
  rw [integral_congr_ae hae, integral_sub hμ.integrable (integrable_const a)]
  simp [mean]

lemma L_gt {μ : Measure ℝ} {a : ℝ} {b : EReal} (hμ : OfferDist μ a b) {V : ℝ}
    (hV : a < V) (hVb : (V : EReal) ≤ b) : mean μ - V < Lfun μ V := by
  haveI := hμ.isProb
  have hint1 : Integrable (fun x => x - V) μ := hμ.integrable.sub (integrable_const V)
  have hint2 : Integrable (fun x => max (V - x) 0) μ :=
    ((integrable_const V).sub hμ.integrable).pos_part
  have hpt : (fun x : ℝ => max (x - V) 0) = fun x => (x - V) + max (V - x) 0 := by
    funext x
    rcases le_total x V with h | h
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  have hpos : 0 < ∫ x, max (V - x) 0 ∂μ := by
    refine (integral_pos_iff_support_of_nonneg (f := fun x : ℝ => max (V - x) 0)
      (fun x => le_max_right _ _) hint2).mpr ?_
    have hsub : Set.Ioo a V ⊆ Function.support (fun x : ℝ => max (V - x) 0) := by
      intro x hx
      simp only [Function.mem_support]
      rw [max_eq_left (by linarith [hx.2])]
      linarith [hx.2]
    exact lt_of_lt_of_le (hμ.noGap a V le_rfl hV hVb) (measure_mono hsub)
  have : Lfun μ V = (mean μ - V) + ∫ x, max (V - x) 0 ∂μ := by
    unfold Lfun
    rw [hpt, integral_add hint1 hint2, integral_sub hμ.integrable (integrable_const V)]
    simp [mean]
  linarith

lemma sh_eq_of_b_le {μ : Measure ℝ} {a : ℝ} {b : EReal} (hμ : OfferDist μ a b) {u sh : ℝ}
    (h : IsSHat μ a b u sh) (r : ℝ) (hb : b = (r : EReal)) (hbu : r ≤ u) : sh = r := by
  rcases h with ⟨_, he⟩ | ⟨_, hub, _⟩ | ⟨hlt, _⟩
  · rw [he, hb]; simp
  · rw [hb] at hub; exact absurd (EReal.coe_lt_coe_iff.mp hub) (not_lt.mpr hbu)
  · have := mean_le_b hμ r hb; linarith

lemma sh_nonneg {μ : Measure ℝ} {a : ℝ} {b : EReal} (hμ : OfferDist μ a b) {u sh : ℝ}
    (h : IsSHat μ a b u sh) : 0 ≤ sh := by
  rcases h with ⟨hbu, he⟩ | ⟨_, _, has, _⟩ | ⟨_, he⟩
  · rw [he]
    apply EReal.toReal_nonneg
    exact le_trans (EReal.coe_nonneg.mpr hμ.a_nonneg) hμ.a_le_b
  · exact le_trans hμ.a_nonneg has
  · rw [he]

lemma a_le_sh {μ : Measure ℝ} {a : ℝ} {b : EReal} (hμ : OfferDist μ a b) {u sh : ℝ}
    (h : IsSHat μ a b u sh) (hm : ¬ u < mean μ) : a ≤ sh := by
  rcases h with ⟨hbu, he⟩ | ⟨_, _, has, _⟩ | ⟨hlt, _⟩
  · rw [he]
    induction b using EReal.rec with
    | bot => exact absurd hμ.a_le_b (by simp)
    | top => exact absurd hbu (by simp)
    | coe r => simpa using hμ.a_le_b
  · exact has
  · exact absurd hlt hm

/-- If the exploding package `(𝒯⁻¹(λT), 0)` is optimal, then `𝒯⁻¹(λT) ≤ ŝ`. -/
lemma exploding_le_sh {μ : Measure ℝ} {a : ℝ} {b : EReal} (hμ : OfferDist μ a b)
    {lam T u : ℝ} (hlam : 0 < lam) (hT : 0 < T) (hu : 0 < u)
    {sh : ℝ} (hsh : IsSHat μ a b u sh)
    (hopt : IsOptimalPackage μ b lam T u (Tinv μ b (lam * T)) 0) :
    Tinv μ b (lam * T) ≤ sh := by
  obtain ⟨_, _, huniq⟩ := theorem_2 hμ hlam hT hu hsh
  by_cases hc : u ≠ mean μ ∨ a = 0
  · have := (huniq hc _ _ hopt).1
    exact min_eq_left_iff.mp this.symm
  · push Not at hc
    obtain ⟨hum, _⟩ := hc
    obtain ⟨hL, hmono, hinv, hleft⟩ := tval_bijection hμ
    obtain ⟨hV0, hVb, hTV⟩ := hinv (lam * T) (by positivity)
    set V := Tinv μ b (lam * T) with hVdef
    by_contra hlt
    push Not at hlt
    have has : a ≤ sh := a_le_sh hμ hsh (by rw [hum]; exact lt_irrefl _)
    have haV : a < V := lt_of_le_of_lt has hlt
    have ha0 := hμ.a_nonneg
    have hab : (a : EReal) < b := lt_trans (EReal.coe_lt_coe_iff.mpr haV) hVb
    have hTa_lt : Tval μ a < lam * T := by
      rw [← hTV]; exact hmono ⟨ha0, hab⟩ ⟨hV0, hVb⟩ haV
    have hTa0 : 0 ≤ Tval μ a := by
      have h0b : ((0:ℝ) : EReal) < b := lt_of_le_of_lt (EReal.coe_le_coe_iff.mpr ha0) hab
      have := hmono.monotoneOn ⟨le_refl (0:ℝ), h0b⟩ ⟨ha0, hab⟩ ha0
      simpa [Tval] using this
    set tD := T - Tval μ a / lam with htD
    have htD0 : 0 ≤ tD := by
      rw [htD, sub_nonneg, div_le_iff₀ hlam]; linarith
    have htDT : tD ≤ T := by
      rw [htD]; have : 0 ≤ Tval μ a / lam := div_nonneg hTa0 hlam.le; linarith
    have hlamT : lam * (T - tD) = Tval μ a := by
      rw [htD]; field_simp; ring
    have hmin : minAccept μ b lam T tD = a := by
      unfold minAccept; rw [hlamT]; exact hleft a ha0 hab
    have hfeas : Feasible μ b lam T u a tD :=
      ⟨le_of_eq hmin, by rw [hum]; exact a_le_mean hμ, htD0, htDT⟩
    have hle := hopt.2 a tD hfeas
    have h56 := (eq_5_6 hμ hlam hT htD0 htDT (le_of_eq hmin) hab u).2
    have hv0 : valueToGo μ b lam T a tD 0 = V := by
      unfold valueToGo
      rw [if_pos htD0, if_pos hab, hVdef]
      congr 1
      rw [htD]; field_simp; ring
    have hsV : surplus μ b lam T u V 0 = u - V := by
      simp [surplus, noAcceptProb]
    rw [h56, hv0, hsV] at hle
    have hLa : Lfun μ a = mean μ - a := L_at_a hμ
    have hLa_pos : 0 < Lfun μ a := hL a ha0 hab
    have hLV : mean μ - V < Lfun μ V := L_gt hμ haV hVb.le
    have : (u - a) * (Lfun μ V / Lfun μ a) = Lfun μ V := by
      rw [hum, ← hLa]; field_simp
    rw [this] at hle
    rw [hum] at hle
    linarith

end MrlT3Aux

open MrlT3Aux in
theorem solution {μ₁ μ₂ : Measure ℝ} {a₁ a₂ : ℝ} {b₁ b₂ : EReal}
    (h₁ : OfferDist μ₁ a₁ b₁) (h₂ : OfferDist μ₂ a₂ b₂)
    {lam T u : ℝ} (hlam : 0 < lam) (hT : 0 < T) (hu : 0 < u)
    (hmrl : StochasticOrders.MeanResidualLife.MrlOrder μ₁ μ₂ id id)
    {sh₁ sh₂ : ℝ} (hsh₁ : IsSHat μ₁ a₁ b₁ u sh₁) (hsh₂ : IsSHat μ₂ a₂ b₂ u sh₂)
    {s₁ t₁ s₂ t₂ : ℝ}
    (ho₁ : IsOptimalPackage μ₁ b₁ lam T u s₁ t₁)
    (ho₂ : IsOptimalPackage μ₂ b₂ lam T u s₂ t₂) :
    ((u ≠ mean μ₂ ∨ a₂ = 0) →
      (s₁ = sh₁ ∧ t₁ = T - Tval μ₁ sh₁ / lam ∧ sh₁ < Tinv μ₁ b₁ (lam * T)) →
        (s₂ = sh₂ ∧ t₂ = T - Tval μ₂ sh₂ / lam ∧ sh₂ < Tinv μ₂ b₂ (lam * T)) ∧
        s₂ ≤ s₁ ∧ 0 < t₁ ∧ t₁ ≤ t₂) ∧
    ((u ≠ mean μ₁ ∨ a₁ = 0) →
      (s₂ = Tinv μ₂ b₂ (lam * T) ∧ t₂ = 0) →
        (s₁ = Tinv μ₁ b₁ (lam * T) ∧ t₁ = 0) ∧ s₁ ≤ s₂ ∧ t₁ = 0 ∧ t₂ = 0) := by
  obtain ⟨_, hmono1, hinv1, _⟩ := tval_bijection h₁
  obtain ⟨_, hmono2, hinv2, _⟩ := tval_bijection h₂
  obtain ⟨hV10, hV1b, hTV1⟩ := hinv1 (lam * T) (by positivity)
  obtain ⟨hV20, hV2b, hTV2⟩ := hinv2 (lam * T) (by positivity)
  obtain ⟨hTv, hTinv, hshord⟩ := theorem_3_order_steps h₁ h₂ hmrl hlam hT
  set V₁ := Tinv μ₁ b₁ (lam * T) with hV1def
  set V₂ := Tinv μ₂ b₂ (lam * T) with hV2def
  -- if `b₁ ≤ u` then `ŝ₁ = b₁`
  have hcase1 : ¬ (u : EReal) < b₁ → ∃ r : ℝ, b₁ = (r : EReal) ∧ sh₁ = r := by
    intro hnb
    push Not at hnb
    induction b₁ using EReal.rec with
    | bot => exact absurd h₁.b_ne_zero (by
        exfalso; have := h₁.a_le_b; simp at this)
    | top => exact absurd hnb (by simp)
    | coe r =>
      refine ⟨r, rfl, sh_eq_of_b_le h₁ hsh₁ r rfl (EReal.coe_le_coe_iff.mp hnb)⟩
  constructor
  · rintro hc ⟨hs1, ht1, hlt1⟩
    have hub1 : (u : EReal) < b₁ := by
      by_contra hnb
      obtain ⟨r, hr, he⟩ := hcase1 hnb
      rw [hr] at hV1b
      have := EReal.coe_lt_coe_iff.mp hV1b
      linarith
    have h21 : sh₂ ≤ sh₁ := hshord u sh₁ sh₂ hu hub1 hsh₁ hsh₂
    have hlt2 : sh₂ < V₂ := lt_of_le_of_lt h21 (lt_of_lt_of_le hlt1 hTinv)
    obtain ⟨_, _, huniq2⟩ := theorem_2 h₂ hlam hT hu hsh₂
    obtain ⟨hs2, ht2⟩ := huniq2 hc s₂ t₂ ho₂
    rw [min_eq_right hlt2.le] at hs2 ht2
    have hsh20 := sh_nonneg h₂ hsh₂
    have hsh10 := sh_nonneg h₁ hsh₁
    have hsh2b : (sh₂ : EReal) < b₂ := lt_trans (EReal.coe_lt_coe_iff.mpr hlt2) hV2b
    have hsh1b : (sh₁ : EReal) < b₁ := lt_trans (EReal.coe_lt_coe_iff.mpr hlt1) hV1b
    have hsh1b2 : (sh₁ : EReal) < b₂ :=
      lt_trans (EReal.coe_lt_coe_iff.mpr (lt_of_lt_of_le hlt1 hTinv)) hV2b
    have hT2 : Tval μ₂ sh₂ < lam * T := by
      rw [← hTV2]; exact hmono2 ⟨hsh20, hsh2b⟩ ⟨hV20, hV2b⟩ hlt2
    have hT1 : Tval μ₁ sh₁ < lam * T := by
      rw [← hTV1]; exact hmono1 ⟨hsh10, hsh1b⟩ ⟨hV10, hV1b⟩ hlt1
    have ht2' : t₂ = T - Tval μ₂ sh₂ / lam := by
      rw [ht2]; unfold optDeadline
      rw [if_pos hsh2b, max_eq_left]
      rw [sub_nonneg, div_le_iff₀ hlam]; linarith
    have hT21 : Tval μ₂ sh₂ ≤ Tval μ₁ sh₁ :=
      le_trans (hmono2.monotoneOn ⟨hsh20, hsh2b⟩ ⟨hsh10, hsh1b2⟩ h21) (hTv sh₁ hsh10 hsh1b)
    refine ⟨⟨hs2, ht2', hlt2⟩, by rw [hs2, hs1]; exact h21, ?_, ?_⟩
    · rw [ht1, sub_pos, div_lt_iff₀ hlam]; linarith
    · rw [ht1, ht2']
      have := div_le_div_of_nonneg_right hT21 hlam.le
      linarith
  · rintro hc ⟨hs2, ht2⟩
    have hopt2 : IsOptimalPackage μ₂ b₂ lam T u V₂ 0 := by rw [← hs2, ← ht2]; exact ho₂
    have hV2sh : V₂ ≤ sh₂ := exploding_le_sh h₂ hlam hT hu hsh₂ hopt2
    have hV1sh : V₁ ≤ sh₁ := by
      by_cases hub1 : (u : EReal) < b₁
      · exact le_trans hTinv (le_trans hV2sh (hshord u sh₁ sh₂ hu hub1 hsh₁ hsh₂))
      · obtain ⟨r, hr, he⟩ := hcase1 hub1
        rw [hr] at hV1b
        rw [he]; exact (EReal.coe_lt_coe_iff.mp hV1b).le
    obtain ⟨_, _, huniq1⟩ := theorem_2 h₁ hlam hT hu hsh₁
    obtain ⟨hs1, ht1⟩ := huniq1 hc s₁ t₁ ho₁
    rw [min_eq_left hV1sh] at hs1 ht1
    have ht1' : t₁ = 0 := by
      rw [ht1]; unfold optDeadline
      rw [if_pos hV1b, hTV1, mul_div_cancel_left₀ _ hlam.ne', sub_self, max_self]
    refine ⟨⟨hs1, ht1'⟩, by rw [hs1, hs2]; exact hTinv, ht1', ht2⟩
