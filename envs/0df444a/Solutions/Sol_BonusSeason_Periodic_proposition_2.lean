-- Prove2me | solution 1 for BonusSeason.Periodic.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-30T17:24:16.919231+00:00
-- url     : https://prove2.me/submissions/f6b7309f-fc76-49a7-9567-6c1819c6e588

import Mathlib
import Definitions.Def_BonusSeason_Periodic_Model

set_option autoImplicit false

namespace BSP812

open BonusSeason.Periodic

/-! ## Generic linear-algebra existence -/

lemma ex1 (a κ : ℝ) (h : κ ≠ 1) : ∃ x : ℝ, x = a + κ * x := by
  refine ⟨a / (1 - κ), ?_⟩
  have h' : 1 - κ ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  field_simp
  ring

lemma ex2 (a b c d : ℝ) (h : c * d ≠ 1) : ∃ x y : ℝ, x = a + c * y ∧ y = b + d * x := by
  obtain ⟨x, hx⟩ := ex1 (a + c * b) (c * d) h
  exact ⟨x, b + d * x, by linear_combination hx, rfl⟩

lemma fin {D c k Q : ℝ} (hc : 0 < c) (hk : 0 ≤ k) (h : D * c = k * Q) (hQ : Q ≤ 0) : D ≤ 0 := by
  have h1 : k * Q ≤ 0 := by nlinarith
  by_contra hD
  push_neg at hD
  nlinarith [mul_pos hD hc]

/-! ## Matching function facts -/

lemma m_zero_left {m : ℝ → ℝ → ℝ} (hm : MatchingA1 m) {b : ℝ} (hb : 0 ≤ b) : m 0 b = 0 := by
  have h := hm.1 0 b le_rfl hb
  exact le_antisymm (h.2.trans (min_le_left _ _)) h.1

lemma m_zero_right {m : ℝ → ℝ → ℝ} (hm : MatchingA1 m) {a : ℝ} (ha : 0 ≤ a) : m a 0 = 0 := by
  have h := hm.1 a 0 ha le_rfl
  exact le_antisymm (h.2.trans (min_le_right _ _)) h.1

lemma m_mono {m : ℝ → ℝ → ℝ} (hm : MatchingA1 m) {a a' b b' : ℝ} (ha : 0 ≤ a) (haa : a ≤ a')
    (hb : 0 ≤ b) (hbb : b ≤ b') : m a b ≤ m a' b' := by
  rcases ha.eq_or_lt with rfl | ha
  · rw [m_zero_left hm hb]; exact (hm.1 a' b' haa (hb.trans hbb)).1
  rcases hb.eq_or_lt with rfl | hb
  · rw [m_zero_right hm ha.le]; exact (hm.1 a' b' (ha.le.trans haa) hbb).1
  have h1 : m a b ≤ m a' b := (hm.2.2.1 b hb).monotoneOn ha (ha.trans_le haa) haa
  have h2 : m a' b ≤ m a' b' :=
    (hm.2.2.2.1 a' (ha.trans_le haa)).monotoneOn hb (hb.trans_le hbb) hbb
  exact h1.trans h2

lemma m_pos {m : ℝ → ℝ → ℝ} (hm : MatchingA1 m) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 < m a b := by
  have h1 : m (a / 2) b < m a b :=
    (hm.2.2.1 b hb) (show (0:ℝ) < a / 2 by positivity) ha (by linarith)
  have h2 := (hm.1 (a / 2) b (by positivity) hb.le).1
  linarith

lemma m_lip {m : ℝ → ℝ → ℝ} (hm : MatchingA1 m) {a b d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hd : 0 ≤ d) : m (a + d) (b + d) ≤ m a b + d := by
  rcases ha.eq_or_lt with rfl | ha
  · rw [m_zero_left hm hb]
    have h1 := (hm.1 (0 + d) (b + d) (by linarith) (by linarith)).2
    have h2 := min_le_left (0 + d) (b + d)
    linarith
  rcases hb.eq_or_lt with rfl | hb
  · rw [m_zero_right hm ha.le]
    have h1 := (hm.1 (a + d) (0 + d) (by linarith) (by linarith)).2
    have h2 := min_le_right (a + d) (0 + d)
    linarith
  have hm0 : 0 ≤ m a b := (hm.1 a b ha.le hb.le).1
  have hab := (hm.1 a b ha.le hb.le).2
  rcases le_total a b with hle | hle
  · obtain ⟨l, hl⟩ : ∃ l : ℝ, l = (a + d) / a := ⟨_, rfl⟩
    have hl0 : 0 < l := by rw [hl]; positivity
    have e1 : l * a = a + d := by rw [hl]; field_simp
    have e2 : l * ((b + d) / l) = b + d := by field_simp
    have hb' : 0 ≤ (b + d) / l := by positivity
    have hbb : (b + d) / l ≤ b := by
      rw [div_le_iff₀ hl0, hl, mul_div_assoc', le_div_iff₀ ha]; nlinarith
    have hmin : m a b ≤ a := hab.trans (min_le_left _ _)
    calc m (a + d) (b + d) = m (l * a) (l * ((b + d) / l)) := by rw [e1, e2]
      _ = l * m a ((b + d) / l) := hm.2.1 l a _ hl0 ha.le hb'
      _ ≤ l * m a b := mul_le_mul_of_nonneg_left (m_mono hm ha.le le_rfl hb' hbb) hl0.le
      _ ≤ m a b + d := by
        rw [hl, div_mul_eq_mul_div, div_le_iff₀ ha]; nlinarith
  · obtain ⟨l, hl⟩ : ∃ l : ℝ, l = (b + d) / b := ⟨_, rfl⟩
    have hl0 : 0 < l := by rw [hl]; positivity
    have e1 : l * b = b + d := by rw [hl]; field_simp
    have e2 : l * ((a + d) / l) = a + d := by field_simp
    have ha' : 0 ≤ (a + d) / l := by positivity
    have haa : (a + d) / l ≤ a := by
      rw [div_le_iff₀ hl0, hl, mul_div_assoc', le_div_iff₀ hb]; nlinarith
    have hmin : m a b ≤ b := hab.trans (min_le_right _ _)
    calc m (a + d) (b + d) = m (l * ((a + d) / l)) (l * b) := by rw [e1, e2]
      _ = l * m ((a + d) / l) b := hm.2.1 l _ b hl0 ha' hb.le
      _ ≤ l * m a b := mul_le_mul_of_nonneg_left (m_mono hm ha' haa hb.le le_rfl) hl0.le
      _ ≤ m a b + d := by
        rw [hl, div_mul_eq_mul_div, div_le_iff₀ hb]; nlinarith

/-! ## Market state facts -/

lemma sum_eq {P : Params} {m : ℝ → ℝ → ℝ} {L : MarketState} (hL : L.Solves P m) :
    L.NL₁ + L.N0₁ = P.N := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hpop2, eNL1, -, eN01, -⟩ := hL
  linear_combination eNL1 + eN01 - (1 - P.δ) * hpop2

lemma nl_identity {P : Params} {m : ℝ → ℝ → ℝ} {L : MarketState} (hL : L.Solves P m) :
    (P.N - L.N0₁) * (1 - ((1 - P.δ) * (1 - P.p)) ^ 2) =
      m (L.M0₁ P) L.N0₁ * ((1 - P.δ) * (1 - P.p)) ^ 2 +
        m (L.M0₂ P) L.N0₂ * ((1 - P.δ) * (1 - P.p)) := by
  have hs := sum_eq hL
  obtain ⟨-, -, -, -, -, -, -, -, -, -, eNL1, eNL2, -, -⟩ := hL
  linear_combination eNL1 + ((1 - P.δ) * (1 - P.p)) * eNL2 -
    (1 - ((1 - P.δ) * (1 - P.p)) ^ 2) * hs

lemma N0₁_le {P : Params} (hP : P.Standing) {m : ℝ → ℝ → ℝ} (hm : MatchingA1 m)
    {L L' : MarketState} (hL : L.Solves P m) (hL' : L'.Solves P m) (hle : L.N0₁ ≤ L'.N0₁) :
    L'.N0₁ ≤ L.N0₁ := by
  have i1 := nl_identity hL
  have i2 := nl_identity hL'
  obtain ⟨hN01, hN02, -, -, -, -, hM01, hM02, -, -, -, -, -, eN02⟩ := hL
  obtain ⟨hN01', hN02', -, -, -, -, hM01', hM02', -, -, -, -, -, eN02'⟩ := hL'
  obtain ⟨-, -, -, -, -, -, -, -, hδ0, hδ1, hp0, hp1, -, -⟩ := hP
  have hMM : L'.M0₁ P = L.M0₁ P + (L'.N0₁ - L.N0₁) := by
    unfold MarketState.M0₁; ring
  have hd : 0 ≤ L'.N0₁ - L.N0₁ := by linarith
  have hlip : m (L'.M0₁ P) L'.N0₁ ≤ m (L.M0₁ P) L.N0₁ + (L'.N0₁ - L.N0₁) := by
    have h := m_lip hm hM01 hN01 hd
    rwa [← hMM, show L.N0₁ + (L'.N0₁ - L.N0₁) = L'.N0₁ by ring] at h
  have hmono1 : m (L.M0₁ P) L.N0₁ ≤ m (L'.M0₁ P) L'.N0₁ :=
    m_mono hm hM01 (by rw [hMM]; linarith) hN01 hle
  have hN02le : L.N0₂ ≤ L'.N0₂ := by
    rw [eN02, eN02']
    have h := mul_nonneg (show 0 ≤ (L'.N0₁ - L.N0₁) -
      (m (L'.M0₁ P) L'.N0₁ - m (L.M0₁ P) L.N0₁) by linarith) (show 0 ≤ 1 - P.δ by linarith)
    nlinarith
  have hM02le : L.M0₂ P ≤ L'.M0₂ P := by unfold MarketState.M0₂; linarith
  have hmono2 : m (L.M0₂ P) L.N0₂ ≤ m (L'.M0₂ P) L'.N0₂ := m_mono hm hM02 hM02le hN02 hN02le
  have hk0 : 0 ≤ (1 - P.δ) * (1 - P.p) := by nlinarith
  have hk1 : (1 - P.δ) * (1 - P.p) < 1 := by nlinarith
  have hk2 : 0 < 1 - ((1 - P.δ) * (1 - P.p)) ^ 2 := by nlinarith
  have t1 := mul_nonneg (sub_nonneg.2 hmono1) (sq_nonneg ((1 - P.δ) * (1 - P.p)))
  have t2 := mul_nonneg (sub_nonneg.2 hmono2) hk0
  by_contra hc
  push_neg at hc
  nlinarith [mul_pos (sub_pos.2 hc) hk2]

lemma N0_unique {P : Params} (hP : P.Standing) {m : ℝ → ℝ → ℝ} (hm : MatchingA1 m)
    {L L' : MarketState} (hL : L.Solves P m) (hL' : L'.Solves P m) :
    L.N0₁ = L'.N0₁ ∧ L.N0₂ = L'.N0₂ := by
  have h1 : L.N0₁ = L'.N0₁ := by
    rcases le_total L.N0₁ L'.N0₁ with h | h
    · exact le_antisymm h (N0₁_le hP hm hL hL' h)
    · exact le_antisymm (N0₁_le hP hm hL' hL h) h
  refine ⟨h1, ?_⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, eN02⟩ := hL
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, eN02'⟩ := hL'
  have hM : L.M0₁ P = L'.M0₁ P := by unfold MarketState.M0₁; rw [h1]
  rw [eN02, eN02', hM, h1]

lemma N0_ne {P : Params} (hP : P.Standing) {m : ℝ → ℝ → ℝ} (hm : MatchingA1 m)
    {L : MarketState} (hL : L.Solves P m) : L.N0₁ ≠ L.N0₂ := by
  intro heq
  have hs := sum_eq hL
  obtain ⟨hN01, hN02, hNL1, hNL2, -, -, hM01, -, -, -, eNL1, eNL2, -, eN02⟩ := hL
  obtain ⟨hM, hN, -, -, -, -, -, -, hδ0, hδ1, hp0, hp1, -, -⟩ := hP
  have hμ : m (L.M0₂ P) L.N0₂ = m (L.M0₁ P) L.N0₁ := by
    unfold MarketState.M0₁ MarketState.M0₂; rw [heq]
  rw [hμ] at eNL1
  rw [← heq] at eN02
  have key : m (L.M0₁ P) L.N0₁ * ((1 + (1 - P.δ) * (1 - P.p)) * (1 - P.δ) * P.p) = 0 := by
    linear_combination P.δ * eNL1 + P.δ * ((1 - P.δ) * (1 - P.p)) * eNL2 +
      (1 - ((1 - P.δ) * (1 - P.p)) ^ 2) * eN02 - (1 - ((1 - P.δ) * (1 - P.p)) ^ 2) * P.δ * hs
  have hpos : 0 < (1 + (1 - P.δ) * (1 - P.p)) * (1 - P.δ) * P.p := by
    have : 0 < 1 - P.δ := by linarith
    have : 0 < 1 - P.p := by linarith
    positivity
  have hμ0 : m (L.M0₁ P) L.N0₁ = 0 := by
    rcases mul_eq_zero.1 key with h | h
    · exact h
    · linarith
  have hNL : L.NL₁ * (1 - ((1 - P.δ) * (1 - P.p)) ^ 2) = 0 := by
    linear_combination eNL1 + ((1 - P.δ) * (1 - P.p)) * eNL2 +
      ((1 - P.δ) * (1 - P.p)) * (1 + (1 - P.δ) * (1 - P.p)) * hμ0
  have hk0 : 0 ≤ (1 - P.δ) * (1 - P.p) := by nlinarith
  have hk1 : (1 - P.δ) * (1 - P.p) < 1 := by nlinarith
  have hk2 : 0 < 1 - ((1 - P.δ) * (1 - P.p)) ^ 2 := by nlinarith
  have hNL0 : L.NL₁ = 0 := by
    rcases mul_eq_zero.1 hNL with h | h
    · exact h
    · linarith
  have hu : L.N0₁ = P.N := by linarith
  have hM' : L.M0₁ P = P.M := by unfold MarketState.M0₁; rw [hu]; ring
  have := m_pos hm hM hN
  rw [← hM', ← hu, hμ0] at this
  exact lt_irrefl _ this

lemma frac_bounds {m : ℝ → ℝ → ℝ} (hm : MatchingA1 m) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (0 ≤ m a b / a ∧ m a b / a ≤ 1) ∧ (0 ≤ m a b / b ∧ m a b / b ≤ 1) := by
  have h := hm.1 a b ha hb
  exact ⟨⟨div_nonneg h.1 ha, div_le_one_of_le₀ (h.2.trans (min_le_left _ _)) ha⟩,
    ⟨div_nonneg h.1 hb, div_le_one_of_le₀ (h.2.trans (min_le_right _ _)) hb⟩⟩

lemma h_bounds {P : Params} (hP : P.Standing) {m : ℝ → ℝ → ℝ} (hm : MatchingA1 m)
    {L : MarketState} (hL : L.Solves P m) :
    (0 ≤ L.h₁ P m ∧ L.h₁ P m ≤ 1) ∧ (0 ≤ L.h₂ P m ∧ L.h₂ P m ≤ 1) := by
  obtain ⟨hN01, hN02, -, -, -, -, hM01, hM02, -⟩ := hL
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hθ0, hθ1⟩ := hP
  obtain ⟨⟨f10, f11⟩, ⟨g10, g11⟩⟩ := frac_bounds hm hM01 hN01
  obtain ⟨⟨f20, f21⟩, ⟨g20, g21⟩⟩ := frac_bounds hm hM02 hN02
  unfold MarketState.h₁ MarketState.h₂ MarketState.g₁ MarketState.g₂ MarketState.f₁
    MarketState.f₂
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · nlinarith [mul_nonneg hθ0.le g10, mul_nonneg (sub_nonneg.2 hθ1.le) f10]
  · nlinarith [mul_le_mul_of_nonneg_left g11 hθ0.le,
      mul_le_mul_of_nonneg_left f11 (sub_nonneg.2 hθ1.le)]
  · nlinarith [mul_nonneg hθ0.le g20, mul_nonneg (sub_nonneg.2 hθ1.le) f20]
  · nlinarith [mul_le_mul_of_nonneg_left g21 hθ0.le,
      mul_le_mul_of_nonneg_left f21 (sub_nonneg.2 hθ1.le)]

/-! ## Nash bargaining -/

lemma rpow_split {θ u v : ℝ} (h0 : 0 < θ) (h1 : θ < 1) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    u ^ θ * v ^ (1 - θ) =
      (θ ^ θ * (1 - θ) ^ (1 - θ)) * ((u / θ) ^ θ * (v / (1 - θ)) ^ (1 - θ)) := by
  rw [Real.div_rpow hu h0.le, Real.div_rpow hv (by linarith)]
  have a : (0:ℝ) < θ ^ θ := Real.rpow_pos_of_pos h0 _
  have b : (0:ℝ) < (1 - θ) ^ (1 - θ) := Real.rpow_pos_of_pos (by linarith) _
  field_simp

lemma G_le {θ u v : ℝ} (h0 : 0 < θ) (h1 : θ < 1) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (u / θ) ^ θ * (v / (1 - θ)) ^ (1 - θ) ≤ u + v := by
  have h := Real.geom_mean_le_arith_mean2_weighted h0.le (by linarith : 0 ≤ 1 - θ)
    (div_nonneg hu h0.le) (div_nonneg hv (by linarith : (0:ℝ) ≤ 1 - θ)) (by ring : θ + (1 - θ) = 1)
  have hne : (1 - θ) ≠ 0 := by linarith
  calc _ ≤ θ * (u / θ) + (1 - θ) * (v / (1 - θ)) := h
    _ = u + v := by field_simp

lemma G_top {θ S : ℝ} (h0 : 0 < θ) (h1 : θ < 1) (hS : 0 ≤ S) :
    ((θ * S) / θ) ^ θ * (((1 - θ) * S) / (1 - θ)) ^ (1 - θ) = S := by
  rw [mul_div_cancel_left₀ _ h0.ne', mul_div_cancel_left₀ _ (by linarith : (1 - θ) ≠ 0),
    ← Real.rpow_add' hS (by rw [add_sub_cancel]; norm_num), add_sub_cancel, Real.rpow_one]

lemma nash_iff {θ a b x : ℝ} (h0 : 0 < θ) (h1 : θ < 1) :
    IsNashTransfer θ a b x ↔ (0 ≤ a + x ∧ 0 ≤ b - x ∧ a + x = θ * (a + b)) := by
  have hc : 0 < θ ^ θ * (1 - θ) ^ (1 - θ) :=
    mul_pos (Real.rpow_pos_of_pos h0 _) (Real.rpow_pos_of_pos (by linarith) _)
  unfold IsNashTransfer
  constructor
  · rintro ⟨hy, hz, hmax⟩
    refine ⟨hy, hz, ?_⟩
    have hS : 0 ≤ a + b := by linarith
    have hθS : 0 ≤ θ * (a + b) := mul_nonneg h0.le hS
    have h1S : 0 ≤ (1 - θ) * (a + b) := mul_nonneg (by linarith) hS
    have hmx := hmax (θ * (a + b) - a) (by linarith) (by linarith)
    have e1 : a + (θ * (a + b) - a) = θ * (a + b) := by ring
    have e2 : b - (θ * (a + b) - a) = (1 - θ) * (a + b) := by ring
    rw [e1, e2, rpow_split h0 h1 hθS h1S, rpow_split h0 h1 hy hz, G_top h0 h1 hS] at hmx
    have hle := G_le h0 h1 hy hz
    have hge : a + b ≤ ((a + x) / θ) ^ θ * ((b - x) / (1 - θ)) ^ (1 - θ) :=
      le_of_mul_le_mul_left hmx hc
    have hne : (1 - θ) ≠ 0 := by linarith
    have hG : ((a + x) / θ) ^ θ * ((b - x) / (1 - θ)) ^ (1 - θ) =
        θ * ((a + x) / θ) + (1 - θ) * ((b - x) / (1 - θ)) := by
      have : θ * ((a + x) / θ) + (1 - θ) * ((b - x) / (1 - θ)) = a + b := by
        field_simp; ring
      rw [this]; linarith
    rw [Real.geom_mean_eq_arith_mean2_weighted_iff_of_pos h0 (by linarith)
      (div_nonneg hy h0.le) (div_nonneg hz (by linarith : (0:ℝ) ≤ 1 - θ)) (by ring)] at hG
    rw [div_eq_div_iff h0.ne' hne] at hG
    linarith
  · rintro ⟨hy, hz, he⟩
    refine ⟨hy, hz, fun x' h1' h2' => ?_⟩
    have hS : 0 ≤ a + b := by linarith
    have e2 : b - x = (1 - θ) * (a + b) := by linarith
    have hθS : 0 ≤ θ * (a + b) := mul_nonneg h0.le hS
    have h1S : 0 ≤ (1 - θ) * (a + b) := mul_nonneg (by linarith) hS
    rw [rpow_split h0 h1 h1' h2', he, e2, rpow_split h0 h1 hθS h1S, G_top h0 h1 hS]
    apply mul_le_mul_of_nonneg_left _ hc.le
    have := G_le h0 h1 h1' h2'
    linarith

/-! ## Optimality of the periodic plan -/

lemma keys (β δ p xL xH Γ₁ Γ₂ z1 z2 W1 W2 x1L x2L : ℝ)
    (hz1 : z1 = 1 - xL + β * (δ * Γ₂ + (1 - δ) * ((1 - p) * z2 + p * (1 - xH + β * Γ₁))))
    (hz2 : z2 = 1 - xL + β * (δ * Γ₁ + (1 - δ) * ((1 - p) * z1 + p * Γ₁)))
    (e1 : x1L = 1 - xL + β * (δ * Γ₂ + (1 - δ) * ((1 - p) * x2L + p * W1)))
    (e2 : x2L = 1 - xL + β * (δ * Γ₁ + (1 - δ) * ((1 - p) * x1L + p * W2))) :
    (x1L - z1) * (1 - (β * (1 - δ)) ^ 2 * (1 - p) ^ 2) =
        β * (1 - δ) * p * ((W1 - (1 - xH + β * Γ₁)) + β * (1 - δ) * (1 - p) * (W2 - Γ₁)) ∧
      (x2L - z2) * (1 - (β * (1 - δ)) ^ 2 * (1 - p) ^ 2) =
        β * (1 - δ) * p * (β * (1 - δ) * (1 - p) * (W1 - (1 - xH + β * Γ₁)) + (W2 - Γ₁)) := by
  constructor
  · linear_combination e1 - hz1 + β * (1 - δ) * (1 - p) * (e2 - hz2)
  · linear_combination β * (1 - δ) * (1 - p) * (e1 - hz1) + (e2 - hz2)

set_option maxHeartbeats 1000000 in
lemma opt_iff (P : Params) (hP : P.Standing) (Γ₁ Γ₂ z1 z2 : ℝ)
    (hz1 : z1 = 1 - P.xL + P.β * (P.δ * Γ₂ +
      (1 - P.δ) * ((1 - P.p) * z2 + P.p * (1 - P.xH + P.β * Γ₁))))
    (hz2 : z2 = 1 - P.xL + P.β * (P.δ * Γ₁ + (1 - P.δ) * ((1 - P.p) * z1 + P.p * Γ₁))) :
    (∀ (a : Plan) (Y : JointValues), PlanValues P Γ₁ Γ₂ a Y → Y.x1L ≤ z1 ∧ Y.x2L ≤ z2) ↔
      (0 ≤ 1 - P.xH + P.β * Γ₁ - Γ₂ ∧
        (1 - P.xH + P.β * Γ₂ - Γ₁) + P.β * (1 - P.δ) * (1 - P.xH + P.β * Γ₁ - Γ₂) ≤ 0) := by
  obtain ⟨-, -, -, -, -, -, hβ0, hβ1, hδ0, hδ1, hp0, hp1, -, -⟩ := hP
  have hbh0 : 0 < P.β * (1 - P.δ) := mul_pos hβ0 (by linarith)
  have hbh1 : P.β * (1 - P.δ) < 1 :=
    mul_lt_one_of_nonneg_of_lt_one_left hβ0.le hβ1 (by linarith)
  have hq0 : 0 < 1 - P.p := by linarith
  have hbq0 : 0 < P.β * (1 - P.δ) * (1 - P.p) := mul_pos hbh0 hq0
  have hbq1 : P.β * (1 - P.δ) * (1 - P.p) < 1 :=
    mul_lt_one_of_nonneg_of_lt_one_left hbh0.le hbh1 (by linarith)
  have hsq : (P.β * (1 - P.δ) * (1 - P.p)) ^ 2 < 1 := pow_lt_one₀ hbq0.le hbq1 two_ne_zero
  have hD : 0 < 1 - (P.β * (1 - P.δ)) ^ 2 * (1 - P.p) ^ 2 := by
    rw [← mul_pow]; linarith
  have hb2 : 0 < 1 - (P.β * (1 - P.δ)) ^ 2 := by
    have := pow_lt_one₀ hbh0.le hbh1 two_ne_zero; linarith
  have hk : 0 ≤ P.β * (1 - P.δ) * P.p := by positivity
  have hne : P.β * (1 - P.δ) * (1 - P.p) * (P.β * (1 - P.δ) * (1 - P.p)) ≠ 1 :=
    (mul_lt_one_of_nonneg_of_lt_one_left hbq0.le hbq1 hbq1.le).ne
  have hne' : P.β * (1 - P.δ) * (P.β * (1 - P.δ)) ≠ 1 :=
    (mul_lt_one_of_nonneg_of_lt_one_left hbh0.le hbh1 hbh1.le).ne
  constructor
  · intro H
    constructor
    · -- the plan (true, true): quit whenever dissatisfied
      obtain ⟨x, y, hx, hy⟩ := ex2 (1 - P.xL + P.β * (P.δ * Γ₂ + (1 - P.δ) * P.p * Γ₂))
        (1 - P.xL + P.β * (P.δ * Γ₁ + (1 - P.δ) * P.p * Γ₁))
        (P.β * (1 - P.δ) * (1 - P.p)) (P.β * (1 - P.δ) * (1 - P.p)) hne
      have e1 : x = 1 - P.xL + P.β * (P.δ * Γ₂ + (1 - P.δ) * ((1 - P.p) * y + P.p * Γ₂)) := by
        linear_combination hx
      have e2 : y = 1 - P.xL + P.β * (P.δ * Γ₁ + (1 - P.δ) * ((1 - P.p) * x + P.p * Γ₁)) := by
        linear_combination hy
      have hY : PlanValues P Γ₁ Γ₂ (true, true) ⟨x, y, 1 - P.xH + P.β * Γ₂, 1 - P.xH + P.β * Γ₁⟩ := by
        simp only [PlanValues, ↓reduceIte]
        exact ⟨e1, e2, by ring, by ring⟩
      have h1 := (H _ _ hY).1
      obtain ⟨k1, -⟩ := keys P.β P.δ P.p P.xL P.xH Γ₁ Γ₂ z1 z2 Γ₂ Γ₁ x y hz1 hz2 e1 e2
      by_contra hc
      push_neg at hc
      have hpos : 0 < (x - z1) * (1 - (P.β * (1 - P.δ)) ^ 2 * (1 - P.p) ^ 2) := by
        rw [k1, sub_self, mul_zero, add_zero]
        exact mul_pos (by positivity) (by linarith)
      have := mul_le_mul_of_nonneg_right (sub_nonpos.2 h1) hD.le
      linarith
    · -- the plan (false, false): never quit
      obtain ⟨u, v, hu, hv⟩ := ex2 (1 - P.xH + P.β * P.δ * Γ₂) (1 - P.xH + P.β * P.δ * Γ₁)
        (P.β * (1 - P.δ)) (P.β * (1 - P.δ)) hne'
      obtain ⟨x, y, hx, hy⟩ := ex2 (1 - P.xL + P.β * (P.δ * Γ₂ + (1 - P.δ) * P.p * v))
        (1 - P.xL + P.β * (P.δ * Γ₁ + (1 - P.δ) * P.p * u))
        (P.β * (1 - P.δ) * (1 - P.p)) (P.β * (1 - P.δ) * (1 - P.p)) hne
      have e1 : x = 1 - P.xL + P.β * (P.δ * Γ₂ + (1 - P.δ) * ((1 - P.p) * y + P.p * v)) := by
        linear_combination hx
      have e2 : y = 1 - P.xL + P.β * (P.δ * Γ₁ + (1 - P.δ) * ((1 - P.p) * x + P.p * u)) := by
        linear_combination hy
      have hY : PlanValues P Γ₁ Γ₂ (false, false) ⟨x, y, u, v⟩ := by
        simp only [PlanValues, Bool.false_eq_true, ↓reduceIte]
        exact ⟨e1, e2, by linear_combination hu, by linear_combination hv⟩
      have h1 := (H _ _ hY).1
      obtain ⟨k1, -⟩ := keys P.β P.δ P.p P.xL P.xH Γ₁ Γ₂ z1 z2 v u x y hz1 hz2 e1 e2
      have hE : (u - Γ₁) * (1 - (P.β * (1 - P.δ)) ^ 2) =
          (1 - P.xH + P.β * Γ₂ - Γ₁) + P.β * (1 - P.δ) * (1 - P.xH + P.β * Γ₁ - Γ₂) := by
        linear_combination hu + P.β * (1 - P.δ) * hv
      have hW : v - (1 - P.xH + P.β * Γ₁) = P.β * (1 - P.δ) * (u - Γ₁) := by
        linear_combination hv
      rw [hW] at k1
      have hEle : u - Γ₁ ≤ 0 := by
        by_contra hc
        push_neg at hc
        have hpos : 0 < (x - z1) * (1 - (P.β * (1 - P.δ)) ^ 2 * (1 - P.p) ^ 2) := by
          rw [k1]
          have : 0 < P.β * (1 - P.δ) * (u - Γ₁) := mul_pos hbh0 hc
          have : 0 < P.β * (1 - P.δ) * (1 - P.p) * (u - Γ₁) := mul_pos hbq0 hc
          exact mul_pos (by positivity) (by linarith)
        have := mul_le_mul_of_nonneg_right (sub_nonpos.2 h1) hD.le
        linarith
      rw [← hE]
      have := mul_le_mul_of_nonneg_right hEle hb2.le
      linarith
  · rintro ⟨hA2, hA12⟩ ⟨a1, a2⟩ Y hY
    have hA1 : 1 - P.xH + P.β * Γ₂ - Γ₁ ≤ 0 := by
      have := mul_nonneg hbh0.le hA2
      linarith
    cases a1 <;> cases a2 <;>
      simp only [PlanValues, Bool.false_eq_true, ↓reduceIte] at hY <;>
      obtain ⟨e1, e2, e3, e4⟩ := hY
    · -- (false, false)
      obtain ⟨k1, k2⟩ := keys P.β P.δ P.p P.xL P.xH Γ₁ Γ₂ z1 z2 Y.x2H Y.x1H Y.x1L Y.x2L
        hz1 hz2 e1 e2
      have hE : (Y.x1H - Γ₁) * (1 - (P.β * (1 - P.δ)) ^ 2) =
          (1 - P.xH + P.β * Γ₂ - Γ₁) + P.β * (1 - P.δ) * (1 - P.xH + P.β * Γ₁ - Γ₂) := by
        linear_combination e3 + P.β * (1 - P.δ) * e4
      have hW : Y.x2H - (1 - P.xH + P.β * Γ₁) = P.β * (1 - P.δ) * (Y.x1H - Γ₁) := by
        linear_combination e4
      have hEle : Y.x1H - Γ₁ ≤ 0 := by
        by_contra hc
        push_neg at hc
        have := mul_pos hc hb2
        linarith
      rw [hW] at k1 k2
      have t1 := mul_le_mul_of_nonneg_left hEle hbh0.le
      have t2 := mul_le_mul_of_nonneg_left hEle hbq0.le
      have t3 := mul_le_mul_of_nonneg_left t1 hbq0.le
      exact ⟨sub_nonpos.1 (fin hD hk k1 (by linarith)), sub_nonpos.1 (fin hD hk k2 (by linarith))⟩
    · -- (false, true): the periodic plan itself
      obtain ⟨k1, k2⟩ := keys P.β P.δ P.p P.xL P.xH Γ₁ Γ₂ z1 z2 Y.x2H Γ₁ Y.x1L Y.x2L
        hz1 hz2 e1 e2
      have hW : Y.x2H - (1 - P.xH + P.β * Γ₁) = 0 := by linear_combination e4
      rw [hW, sub_self] at k1 k2
      exact ⟨sub_nonpos.1 (fin hD hk k1 (by simp)), sub_nonpos.1 (fin hD hk k2 (by simp))⟩
    · -- (true, false)
      obtain ⟨k1, k2⟩ := keys P.β P.δ P.p P.xL P.xH Γ₁ Γ₂ z1 z2 Γ₂ Y.x1H Y.x1L Y.x2L
        hz1 hz2 e1 e2
      have hW : Y.x1H - Γ₁ = 1 - P.xH + P.β * Γ₂ - Γ₁ := by linear_combination e3
      rw [hW] at k1 k2
      have t1 := mul_le_mul_of_nonneg_left hA1 hbq0.le
      have t2 := mul_le_mul_of_nonneg_left hA2 hbq0.le
      exact ⟨sub_nonpos.1 (fin hD hk k1 (by linarith)), sub_nonpos.1 (fin hD hk k2 (by linarith))⟩
    · -- (true, true)
      obtain ⟨k1, k2⟩ := keys P.β P.δ P.p P.xL P.xH Γ₁ Γ₂ z1 z2 Γ₂ Γ₁ Y.x1L Y.x2L
        hz1 hz2 e1 e2
      rw [sub_self] at k1 k2
      have t2 := mul_le_mul_of_nonneg_left hA2 hbq0.le
      exact ⟨sub_nonpos.1 (fin hD hk k1 (by linarith)), sub_nonpos.1 (fin hD hk k2 (by linarith))⟩

/-! ## Thresholds -/

lemma sign_lemma {D X c R : ℝ} (hD : 0 < D) (hc : 0 < c) (key : D * X = c * R) :
    X ≤ 0 ↔ R ≤ 0 := by
  constructor
  · intro h
    by_contra h'
    push_neg at h'
    nlinarith [mul_pos hc h', mul_nonneg hD.le (neg_nonneg.2 h)]
  · intro h
    by_contra h'
    push_neg at h'
    nlinarith [mul_pos hD h', mul_nonneg hc.le (neg_nonneg.2 h)]

lemma th_high (xL xH bh p h1 h2 S1 S2 : ℝ) (hxL : xL < 1) (hbh0 : 0 < bh) (hbh1 : bh < 1)
    (hp0 : 0 < p) (hp1 : p < 1) (h10 : 0 ≤ h1) (h11 : h1 ≤ 1) (h20 : 0 ≤ h2) (h21 : h2 ≤ 1)
    (hS1 : S1 = (1 - xL) + bh * p * (1 - xH) + bh * ((1 - p) - h2) * S2)
    (hS2 : S2 = (1 - xL) + bh * (1 - p) * (1 - h1) * S1) :
    0 ≤ (1 - xH) - h2 * S2 ↔
      (xH - xL) / (1 - xL) ≤ (1 - h2 - bh * (1 - p) * (1 - h1) * (h2 + bh * (1 - p) * (1 - h2))) /
        (1 - bh ^ 2 * (1 - p) ^ 2 * (1 - h1) * (1 - h2)) := by
  have hs : 0 < 1 - xL := by linarith
  have a1 : 0 ≤ bh ^ 2 * (1 - p) * (1 - h1) := by
    have : 0 ≤ 1 - p := by linarith
    have : 0 ≤ 1 - h1 := by linarith
    positivity
  have a2 : bh ^ 2 * (1 - p) * (1 - h1) ≤ bh ^ 2 := by
    have : (1 - p) * (1 - h1) ≤ 1 := by nlinarith
    nlinarith [sq_nonneg bh]
  have hbb : bh ^ 2 < 1 := by nlinarith
  have hD : 0 < 1 - bh ^ 2 * (1 - p) * (1 - h1) * ((1 - p) - h2) := by
    have : (1 - p) - h2 ≤ 1 := by linarith
    nlinarith [mul_le_mul_of_nonneg_left this a1]
  have hD' : 0 < 1 - bh ^ 2 * (1 - p) ^ 2 * (1 - h1) * (1 - h2) := by
    have : (1 - p) * (1 - h2) ≤ 1 := by nlinarith
    have : 0 ≤ 1 - h2 := by linarith
    nlinarith [mul_le_mul_of_nonneg_left (show (1 - p) * (1 - h2) ≤ 1 by nlinarith) a1]
  have key : (1 - bh ^ 2 * (1 - p) * (1 - h1) * ((1 - p) - h2)) * ((1 - xH) - h2 * S2) =
      (1 - xL) * (1 - h2 - bh * (1 - p) * (1 - h1) * (h2 + bh * (1 - p) * (1 - h2))) -
        (xH - xL) * (1 - bh ^ 2 * (1 - p) ^ 2 * (1 - h1) * (1 - h2)) := by
    linear_combination (-h2) * hS2 + (-h2 * bh * (1 - p) * (1 - h1)) * hS1
  rw [div_le_div_iff₀ hs hD']
  constructor
  · intro h
    nlinarith [mul_nonneg hD.le h]
  · intro h
    by_contra hc
    push_neg at hc
    nlinarith [mul_pos hD (show 0 < -((1 - xH) - h2 * S2) by linarith)]

lemma th_low (xL xH bh p h1 h2 S1 S2 : ℝ) (hxL : xL < 1) (hbh0 : 0 < bh) (hbh1 : bh < 1)
    (hp0 : 0 < p) (hp1 : p < 1) (h10 : 0 ≤ h1) (h11 : h1 ≤ 1) (h20 : 0 ≤ h2) (h21 : h2 ≤ 1)
    (hS1 : S1 = (1 - xL) + bh * p * (1 - xH) + bh * ((1 - p) - h2) * S2)
    (hS2 : S2 = (1 - xL) + bh * (1 - p) * (1 - h1) * S1) :
    (1 - xH) * (1 + bh) - h1 * S1 - bh * h2 * S2 ≤ 0 ↔
      (1 - h1) * (1 - bh * (1 - p)) * (1 + bh * (1 - h2)) /
          (1 + bh * (1 - h1) * (p - bh * (1 - p) * (1 - h2))) ≤ (xH - xL) / (1 - xL) := by
  have hs : 0 < 1 - xL := by linarith
  have a1 : 0 ≤ bh ^ 2 * (1 - p) * (1 - h1) := by
    have : 0 ≤ 1 - p := by linarith
    have : 0 ≤ 1 - h1 := by linarith
    positivity
  have a2 : bh ^ 2 * (1 - p) * (1 - h1) ≤ bh ^ 2 := by
    have : (1 - p) * (1 - h1) ≤ 1 := by nlinarith
    nlinarith [sq_nonneg bh]
  have hbb : bh ^ 2 < 1 := by nlinarith
  have hD : 0 < 1 - bh ^ 2 * (1 - p) * (1 - h1) * ((1 - p) - h2) := by
    have : (1 - p) - h2 ≤ 1 := by linarith
    nlinarith [mul_le_mul_of_nonneg_left this a1]
  have hL : 0 < 1 + bh * (1 - h1) * (p - bh * (1 - p) * (1 - h2)) := by
    have : 0 ≤ bh * (1 - h1) * p := by
      have : 0 ≤ 1 - h1 := by linarith
      positivity
    have : 1 - h2 ≤ 1 := by linarith
    have : 0 ≤ 1 - h2 := by linarith
    nlinarith [mul_le_mul_of_nonneg_left this a1]
  have hq : 0 < 1 + bh * (1 - p) := by
    have : 0 < 1 - p := by linarith
    positivity
  have key : (1 - bh ^ 2 * (1 - p) * (1 - h1) * ((1 - p) - h2)) *
      ((1 - xH) * (1 + bh) - h1 * S1 - bh * h2 * S2) =
      (1 + bh * (1 - p)) * ((1 - xL) * ((1 - h1) * (1 - bh * (1 - p)) * (1 + bh * (1 - h2))) -
        (xH - xL) * (1 + bh * (1 - h1) * (p - bh * (1 - p) * (1 - h2)))) := by
    linear_combination (-h1 - bh ^ 2 * (1 - p) * h2 * (1 - h1)) * hS1 +
      (-bh * (h2 + ((1 - p) - h2) * h1)) * hS2
  rw [div_le_div_iff₀ hL hs, sign_lemma hD hq key]
  generalize (1 - h1) * (1 - bh * (1 - p)) * (1 + bh * (1 - h2)) = N
  generalize 1 + bh * (1 - h1) * (p - bh * (1 - p) * (1 - h2)) = Dn
  constructor <;> intro h <;> linarith

/-! ## Contracts -/

lemma pv_odd (P : Params) (hP : P.Standing) (c : PeriodicContract) :
    pvOdd P c = c.b₁ + (c.w₁ + P.βhat * c.w₂) / (1 - P.βhat ^ 2 * (1 - P.p) ^ 2) := by
  obtain ⟨-, -, -, -, -, -, hβ0, hβ1, hδ0, hδ1, hp0, hp1, -, -⟩ := hP
  have hbh0 : 0 < P.βhat := by unfold Params.βhat; nlinarith
  have hbh1 : P.βhat < 1 := by unfold Params.βhat; nlinarith
  have hr0 : 0 ≤ P.βhat ^ 2 * (1 - P.p) ^ 2 := by positivity
  have hr1 : P.βhat ^ 2 * (1 - P.p) ^ 2 < 1 := by
    have : (1 - P.p) ^ 2 < 1 := by nlinarith
    have : P.βhat ^ 2 < 1 := by nlinarith
    nlinarith [sq_nonneg (1 - P.p)]
  have hs : HasSum (fun k : ℕ => (P.βhat ^ 2 * (1 - P.p) ^ 2) ^ k * (c.w₁ + P.βhat * c.w₂) +
      (if k = 0 then c.b₁ else 0))
      ((1 - P.βhat ^ 2 * (1 - P.p) ^ 2)⁻¹ * (c.w₁ + P.βhat * c.w₂) + c.b₁) :=
    HasSum.add ((hasSum_geometric_of_lt_one hr0 hr1).mul_right _) (hasSum_ite_eq 0 c.b₁)
  have hfun : (fun k : ℕ => P.βhat ^ (2 * k) * (1 - P.p) ^ (2 * k) *
      (c.oddStream (2 * k) + P.βhat * c.oddStream (2 * k + 1))) =
      fun k : ℕ => (P.βhat ^ 2 * (1 - P.p) ^ 2) ^ k * (c.w₁ + P.βhat * c.w₂) +
        (if k = 0 then c.b₁ else 0) := by
    funext k
    rcases k with _ | k
    · have e0 : c.oddStream (2 * 0) = c.b₁ + c.w₁ := by simp [PeriodicContract.oddStream]
      have e1 : c.oddStream (2 * 0 + 1) = c.w₂ := by simp [PeriodicContract.oddStream]
      rw [e0, e1, if_pos rfl]
      ring
    · have e1 : c.oddStream (2 * (k + 1)) = c.w₁ := by
        simp [PeriodicContract.oddStream]
      have e2 : c.oddStream (2 * (k + 1) + 1) = c.w₂ := by
        simp [PeriodicContract.oddStream]
      rw [e1, e2, if_neg (Nat.succ_ne_zero k), pow_mul, pow_mul, ← mul_pow]
      ring
  unfold pvOdd
  rw [hfun, hs.tsum_eq]
  ring

lemma pv_even (P : Params) (hP : P.Standing) (c : PeriodicContract) :
    pvEven P c = c.b₂ + c.w₂ +
      P.βhat * (1 - P.p) * (c.w₁ + P.βhat * c.w₂) / (1 - P.βhat ^ 2 * (1 - P.p) ^ 2) := by
  obtain ⟨-, -, -, -, -, -, hβ0, hβ1, hδ0, hδ1, hp0, hp1, -, -⟩ := hP
  have hbh0 : 0 < P.βhat := by unfold Params.βhat; nlinarith
  have hbh1 : P.βhat < 1 := by unfold Params.βhat; nlinarith
  have hr0 : 0 ≤ P.βhat ^ 2 * (1 - P.p) ^ 2 := by positivity
  have hr1 : P.βhat ^ 2 * (1 - P.p) ^ 2 < 1 := by
    have : (1 - P.p) ^ 2 < 1 := by nlinarith
    have : P.βhat ^ 2 < 1 := by nlinarith
    nlinarith [sq_nonneg (1 - P.p)]
  have hs : HasSum (fun k : ℕ => (P.βhat ^ 2 * (1 - P.p) ^ 2) ^ k *
      (P.βhat * (1 - P.p) * (c.w₁ + P.βhat * c.w₂)))
      ((1 - P.βhat ^ 2 * (1 - P.p) ^ 2)⁻¹ * (P.βhat * (1 - P.p) * (c.w₁ + P.βhat * c.w₂))) :=
    (hasSum_geometric_of_lt_one hr0 hr1).mul_right _
  have hfun : (fun k : ℕ => P.βhat ^ (2 * k + 1) * (1 - P.p) ^ (2 * k + 1) *
      (c.evenStream (2 * k + 1) + P.βhat * c.evenStream (2 * k + 2))) =
      fun k : ℕ => (P.βhat ^ 2 * (1 - P.p) ^ 2) ^ k *
        (P.βhat * (1 - P.p) * (c.w₁ + P.βhat * c.w₂)) := by
    funext k
    have e1 : c.evenStream (2 * k + 1) = c.w₁ := by
      simp [PeriodicContract.evenStream]
    have e2 : c.evenStream (2 * k + 2) = c.w₂ := by
      have : 2 * k + 2 = 2 * (k + 1) := by ring
      rw [this]
      simp [PeriodicContract.evenStream]
    have e3 : (1 - P.p) ^ (2 * k + 1) = (1 - P.p) * ((1 - P.p) ^ 2) ^ k := by
      rw [pow_succ, pow_mul, mul_comm]
    rw [e1, e2, e3, mul_pow]
    ring
  have h0 : c.evenStream 0 = c.b₂ + c.w₂ := by simp [PeriodicContract.evenStream]
  unfold pvEven
  rw [hfun, hs.tsum_eq, h0]
  ring

lemma contract_exists (P : Params) (hP : P.Standing) (X : Values) :
    ∃ c : PeriodicContract, IncentiveCompatible P X c ∧ pvOdd P c = X.P₁ ∧ pvEven P c = X.P₂ := by
  have hP' := hP
  obtain ⟨-, -, -, hxL, hxLH, hxH, hβ0, hβ1, hδ0, hδ1, hp0, hp1, -, -⟩ := hP'
  have hbh : P.βhat = P.β * (1 - P.δ) := rfl
  obtain ⟨w2, hw2⟩ : ∃ w : ℝ, w = X.U₂ - P.β * X.U₁ + P.xH := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ z : ℝ, z = X.U₁ - P.β * P.δ * X.U₂ - P.β ^ 2 * (1 - P.δ) * X.U₁ +
      P.xH * (1 + P.β * (1 - P.δ)) := ⟨_, rfl⟩
  obtain ⟨w1, hw1⟩ : ∃ w : ℝ, w = Z - P.β * (1 - P.δ) * w2 := ⟨_, rfl⟩
  have hκ0 : 0 ≤ P.β ^ 2 * (1 - P.δ) * ((1 - P.δ) * (1 - P.p) ^ 2) := by
    have : 0 ≤ 1 - P.δ := by linarith
    positivity
  have hκ1 : P.β ^ 2 * (1 - P.δ) * ((1 - P.δ) * (1 - P.p) ^ 2) < 1 := by
    have a : (1 - P.p) ^ 2 < 1 := by nlinarith
    have b : (1 - P.δ) ^ 2 < 1 := by nlinarith
    have c : P.β ^ 2 < 1 := by nlinarith
    have : P.β ^ 2 * (1 - P.δ) * ((1 - P.δ) * (1 - P.p) ^ 2) =
      P.β ^ 2 * ((1 - P.δ) ^ 2 * (1 - P.p) ^ 2) := by ring
    rw [this]
    have : (1 - P.δ) ^ 2 * (1 - P.p) ^ 2 < 1 := by nlinarith [sq_nonneg (1 - P.p)]
    nlinarith [sq_nonneg P.β, sq_nonneg ((1 - P.δ) * (1 - P.p))]
  obtain ⟨T, hT⟩ := ex1 (w1 - P.xL + P.β * (1 - P.δ) * (w2 - (1 - P.p) * P.xL - P.p * P.xH) +
      P.β * P.δ * X.U₂ + P.β ^ 2 * (1 - P.δ) * ((1 - (1 - P.δ) * (1 - P.p) ^ 2) * X.U₁))
    (P.β ^ 2 * (1 - P.δ) * ((1 - P.δ) * (1 - P.p) ^ 2)) (by linarith)
  refine ⟨⟨X.P₁ - Z / (1 - P.βhat ^ 2 * (1 - P.p) ^ 2),
    X.P₂ - w2 - P.βhat * (1 - P.p) * Z / (1 - P.βhat ^ 2 * (1 - P.p) ^ 2), w1, w2⟩, ?_, ?_, ?_⟩
  · unfold IncentiveCompatible
    dsimp only
    refine ⟨?_, ⟨T, ?_, ?_⟩, ?_⟩
    · rw [hw2]; linarith
    · linear_combination hT
    · have e : (T - X.U₁) * (1 - P.β ^ 2 * (1 - P.δ) * ((1 - P.δ) * (1 - P.p) ^ 2)) =
          (P.xH - P.xL) * (1 + P.β * (1 - P.δ) * (1 - P.p)) := by
        linear_combination hT + hw1 + hZ
      have : 0 ≤ (P.xH - P.xL) * (1 + P.β * (1 - P.δ) * (1 - P.p)) := by
        have : 0 ≤ 1 - P.δ := by linarith
        have : 0 ≤ 1 - P.p := by linarith
        have : 0 ≤ P.xH - P.xL := by linarith
        positivity
      by_contra hc
      push_neg at hc
      nlinarith [mul_pos (sub_pos.2 hc) (sub_pos.2 hκ1)]
    · have e : w1 - P.xH + P.β * (1 - P.δ) * (w2 - P.xH) + P.β * P.δ * X.U₂ +
          P.β ^ 2 * (1 - P.δ) * X.U₁ = X.U₁ := by
        linear_combination hw1 + hZ
      linarith
  · rw [pv_odd P hP]
    dsimp only
    rw [hw1, hbh]
    ring
  · rw [pv_even P hP]
    dsimp only
    rw [hw1, hbh]
    ring

/-! ## Non-existence outside the thresholds -/

set_option maxHeartbeats 1000000 in
lemma dir2 (P : Params) (hP : P.Standing) (m : ℝ → ℝ → ℝ) (hm : MatchingA1 m)
    (L : MarketState) (hL : L.Solves P m) :
    P.matchImportance < alphaLow P m L ∨ alphaHigh P m L < P.matchImportance →
      ¬ PeriodicEquilibrium P m := by
  intro hout heq
  obtain ⟨L', X, c, hL', -, hX, hopt, -, -, -⟩ := heq
  obtain ⟨hu1, hu2⟩ := N0_unique hP hm hL hL'
  have hlow : alphaLow P m L' = alphaLow P m L := by
    unfold alphaLow MarketState.h₁ MarketState.h₂ MarketState.g₁ MarketState.g₂
      MarketState.f₁ MarketState.f₂ MarketState.M0₁ MarketState.M0₂
    rw [hu1, hu2]
  have hhigh : alphaHigh P m L' = alphaHigh P m L := by
    unfold alphaHigh MarketState.h₁ MarketState.h₂ MarketState.g₁ MarketState.g₂
      MarketState.f₁ MarketState.f₂ MarketState.M0₁ MarketState.M0₂
    rw [hu1, hu2]
  obtain ⟨⟨h10, h11⟩, ⟨h20, h21⟩⟩ := h_bounds hP hm hL'
  have hP' := hP
  obtain ⟨-, -, -, hxL, hxLH, hxH, hβ0, hβ1, hδ0, hδ1, hp0, hp1, hθ0, hθ1⟩ := hP'
  obtain ⟨eJ1, eJ2, eV1, eV2, eW1, eW2, eU1, eU2, n1, n2⟩ := hX
  rw [nash_iff hθ0 hθ1] at n1 n2
  obtain ⟨-, -, n1⟩ := n1
  obtain ⟨-, -, n2⟩ := n2
  have hh1 : L'.h₁ P m = P.θ * L'.g₁ P m + (1 - P.θ) * L'.f₁ P m := rfl
  have hh2 : L'.h₂ P m = P.θ * L'.g₂ P m + (1 - P.θ) * L'.f₂ P m := rfl
  have hΓ1 : (X.U₁ + X.V₁) - P.β * (X.U₂ + X.V₂) =
      L'.h₁ P m * (X.J₁ - P.β * X.V₂ + X.W₁ - P.β * X.U₂) := by
    rw [hh1]; linear_combination eU1 + eV1 + (L'.g₁ P m - L'.f₁ P m) * n1
  have hΓ2 : (X.U₂ + X.V₂) - P.β * (X.U₁ + X.V₁) =
      L'.h₂ P m * (X.J₂ - P.β * X.V₁ + X.W₂ - P.β * X.U₁) := by
    rw [hh2]; linear_combination eU2 + eV2 + (L'.g₂ P m - L'.f₂ P m) * n2
  have hz2 : X.J₂ + X.W₂ = 1 - P.xL + P.β * (P.δ * (X.U₁ + X.V₁) +
      (1 - P.δ) * ((1 - P.p) * (X.J₁ + X.W₁) + P.p * (X.U₁ + X.V₁))) := by
    linear_combination eJ2 + eW2
  have hz1 : X.J₁ + X.W₁ = 1 - P.xL + P.β * (P.δ * (X.U₂ + X.V₂) +
      (1 - P.δ) * ((1 - P.p) * (X.J₂ + X.W₂) + P.p * (1 - P.xH + P.β * (X.U₁ + X.V₁)))) := by
    linear_combination eJ1 + eW1 - P.β * (1 - P.δ) * (1 - P.p) * hz2
  have hopt' := (opt_iff P hP _ _ _ _ hz1 hz2).mp hopt
  have hS1 : (X.J₁ - P.β * X.V₂ + X.W₁ - P.β * X.U₂) =
      (1 - P.xL) + P.β * (1 - P.δ) * P.p * (1 - P.xH) +
        P.β * (1 - P.δ) * ((1 - P.p) - L'.h₂ P m) * (X.J₂ - P.β * X.V₁ + X.W₂ - P.β * X.U₁) := by
    linear_combination hz1 - P.β * (1 - P.δ) * hΓ2
  have hS2 : (X.J₂ - P.β * X.V₁ + X.W₂ - P.β * X.U₁) =
      (1 - P.xL) + P.β * (1 - P.δ) * (1 - P.p) * (1 - L'.h₁ P m) *
        (X.J₁ - P.β * X.V₂ + X.W₁ - P.β * X.U₂) := by
    linear_combination hz2 - P.β * (1 - P.δ) * (1 - P.p) * hΓ1
  have hbh0 : 0 < P.β * (1 - P.δ) := mul_pos hβ0 (by linarith)
  have hbh1 : P.β * (1 - P.δ) < 1 :=
    mul_lt_one_of_nonneg_of_lt_one_left hβ0.le hβ1 (by linarith)
  have hA2 : 0 ≤ (1 - P.xH) - L'.h₂ P m * (X.J₂ - P.β * X.V₁ + X.W₂ - P.β * X.U₁) := by
    have := hopt'.1
    linarith
  have e : (1 - P.xH + P.β * (X.U₂ + X.V₂) - (X.U₁ + X.V₁)) +
      P.β * (1 - P.δ) * (1 - P.xH + P.β * (X.U₁ + X.V₁) - (X.U₂ + X.V₂)) =
      (1 - P.xH) * (1 + P.β * (1 - P.δ)) - L'.h₁ P m * (X.J₁ - P.β * X.V₂ + X.W₁ - P.β * X.U₂) -
        P.β * (1 - P.δ) * L'.h₂ P m * (X.J₂ - P.β * X.V₁ + X.W₂ - P.β * X.U₁) := by
    linear_combination (-1 : ℝ) * hΓ1 - P.β * (1 - P.δ) * hΓ2
  have hA12 : (1 - P.xH) * (1 + P.β * (1 - P.δ)) -
      L'.h₁ P m * (X.J₁ - P.β * X.V₂ + X.W₁ - P.β * X.U₂) -
        P.β * (1 - P.δ) * L'.h₂ P m * (X.J₂ - P.β * X.V₁ + X.W₂ - P.β * X.U₁) ≤ 0 := by
    rw [← e]; exact hopt'.2
  have hhi : P.matchImportance ≤ alphaHigh P m L' :=
    (th_high P.xL P.xH (P.β * (1 - P.δ)) P.p (L'.h₁ P m) (L'.h₂ P m) _ _ (by linarith)
      hbh0 hbh1 hp0 hp1 h10 h11 h20 h21 hS1 hS2).mp hA2
  have hlo : alphaLow P m L' ≤ P.matchImportance :=
    (th_low P.xL P.xH (P.β * (1 - P.δ)) P.p (L'.h₁ P m) (L'.h₂ P m) _ _ (by linarith)
      hbh0 hbh1 hp0 hp1 h10 h11 h20 h21 hS1 hS2).mp hA12
  rw [hhigh] at hhi
  rw [hlow] at hlo
  rcases hout with h | h <;> linarith

/-! ## Existence inside the thresholds -/

set_option maxHeartbeats 4000000 in
lemma dir1 (P : Params) (hP : P.Standing) (m : ℝ → ℝ → ℝ) (hm : MatchingA1 m)
    (L : MarketState) (hL : L.Solves P m) :
    alphaLow P m L < P.matchImportance ∧ P.matchImportance < alphaHigh P m L →
      PeriodicEquilibrium P m := by
  rintro ⟨hlo, hhi⟩
  obtain ⟨⟨h10, h11⟩, ⟨h20, h21⟩⟩ := h_bounds hP hm hL
  have hP' := hP
  obtain ⟨-, -, -, hxL, hxLH, hxH, hβ0, hβ1, hδ0, hδ1, hp0, hp1, hθ0, hθ1⟩ := hP'
  have hbh0 : 0 < P.β * (1 - P.δ) := mul_pos hβ0 (by linarith)
  have hbh1 : P.β * (1 - P.δ) < 1 :=
    mul_lt_one_of_nonneg_of_lt_one_left hβ0.le hβ1 (by linarith)
  have hq0 : 0 < 1 - P.p := by linarith
  have hc_le : P.β * (1 - P.δ) * ((1 - P.p) - L.h₂ P m) ≤ P.β * (1 - P.δ) := by
    have : (1 - P.p) - L.h₂ P m ≤ 1 := by linarith
    have := mul_le_mul_of_nonneg_left this hbh0.le
    linarith
  have hc_ge : -(P.β * (1 - P.δ)) ≤ P.β * (1 - P.δ) * ((1 - P.p) - L.h₂ P m) := by
    have : -1 ≤ (1 - P.p) - L.h₂ P m := by linarith
    have := mul_le_mul_of_nonneg_left this hbh0.le
    linarith
  have hd0 : 0 ≤ P.β * (1 - P.δ) * (1 - P.p) * (1 - L.h₁ P m) := by
    have : 0 ≤ 1 - L.h₁ P m := by linarith
    positivity
  have hd1 : P.β * (1 - P.δ) * (1 - P.p) * (1 - L.h₁ P m) ≤ P.β * (1 - P.δ) := by
    have h1 : (1 - P.p) * (1 - L.h₁ P m) ≤ 1 := by
      have : 0 ≤ 1 - L.h₁ P m := by linarith
      have := mul_le_mul_of_nonneg_left (show 1 - L.h₁ P m ≤ 1 by linarith) hq0.le
      linarith
    have := mul_le_mul_of_nonneg_left h1 hbh0.le
    linarith
  have hcd : P.β * (1 - P.δ) * ((1 - P.p) - L.h₂ P m) *
      (P.β * (1 - P.δ) * (1 - P.p) * (1 - L.h₁ P m)) < 1 := by
    have t1 := mul_le_mul_of_nonneg_right hc_le hd0
    have t2 := mul_le_mul_of_nonneg_left hd1 hbh0.le
    have t3 : P.β * (1 - P.δ) * (P.β * (1 - P.δ)) < 1 :=
      mul_lt_one_of_nonneg_of_lt_one_left hbh0.le hbh1 hbh1.le
    linarith
  obtain ⟨S1, S2, hS1, hS2⟩ := ex2 ((1 - P.xL) + P.β * (1 - P.δ) * P.p * (1 - P.xH)) (1 - P.xL)
    (P.β * (1 - P.δ) * ((1 - P.p) - L.h₂ P m)) (P.β * (1 - P.δ) * (1 - P.p) * (1 - L.h₁ P m))
    hcd.ne
  have hS1pos : 0 < S1 := by
    have e : S1 * (1 - P.β * (1 - P.δ) * ((1 - P.p) - L.h₂ P m) *
        (P.β * (1 - P.δ) * (1 - P.p) * (1 - L.h₁ P m))) =
        (1 - P.xL) * (1 + P.β * (1 - P.δ) * ((1 - P.p) - L.h₂ P m)) +
          P.β * (1 - P.δ) * P.p * (1 - P.xH) := by
      linear_combination hS1 + P.β * (1 - P.δ) * ((1 - P.p) - L.h₂ P m) * hS2
    have hpos : 0 < (1 - P.xL) * (1 + P.β * (1 - P.δ) * ((1 - P.p) - L.h₂ P m)) +
        P.β * (1 - P.δ) * P.p * (1 - P.xH) := by
      have : 0 < 1 + P.β * (1 - P.δ) * ((1 - P.p) - L.h₂ P m) := by linarith
      have : 0 < 1 - P.xL := by linarith
      have : 0 < 1 - P.xH := by linarith
      positivity
    by_contra hc
    push_neg at hc
    have := mul_le_mul_of_nonneg_right hc (sub_pos.2 hcd).le
    linarith
  have hS2pos : 0 < S2 := by
    have := mul_nonneg hd0 hS1pos.le
    rw [hS2]; linarith
  have hββ : P.β * P.β ≠ 1 := (mul_lt_one_of_nonneg_of_lt_one_left hβ0.le hβ1 hβ1.le).ne
  obtain ⟨U1, U2, hU1, hU2⟩ := ex2 (P.θ * L.g₁ P m * S1) (P.θ * L.g₂ P m * S2) P.β P.β hββ
  obtain ⟨V1, V2, hV1, hV2⟩ :=
    ex2 ((1 - P.θ) * L.f₁ P m * S1) ((1 - P.θ) * L.f₂ P m * S2) P.β P.β hββ
  have hκ : P.β ^ 2 * (1 - P.δ) * ((1 - P.δ) * (1 - P.p) ^ 2) ≠ 1 := by
    have e : P.β ^ 2 * (1 - P.δ) * ((1 - P.δ) * (1 - P.p) ^ 2) =
        (P.β * (1 - P.δ) * (1 - P.p)) ^ 2 := by ring
    rw [e]
    exact (pow_lt_one₀ (by positivity)
      (mul_lt_one_of_nonneg_of_lt_one_left hbh0.le hbh1 (by linarith)) two_ne_zero).ne
  obtain ⟨W1, hW1⟩ := ex1 (-P.xL - P.β * (1 - P.δ) * ((1 - P.p) * P.xL + P.p * P.xH) +
      P.β * P.δ * U2 + P.β ^ 2 * (1 - P.δ) * ((1 - (1 - P.δ) * (1 - P.p) ^ 2) * U1))
    (P.β ^ 2 * (1 - P.δ) * ((1 - P.δ) * (1 - P.p) ^ 2)) hκ
  obtain ⟨W2, hW2⟩ : ∃ w : ℝ, w = -P.xL + P.β * ((1 - P.δ) * (1 - P.p) * W1 +
      (1 - (1 - P.δ) * (1 - P.p)) * U1) := ⟨_, rfl⟩
  obtain ⟨J1, hJ1⟩ : ∃ j : ℝ, j = S1 + P.β * (U2 + V2) - W1 := ⟨_, rfl⟩
  obtain ⟨J2, hJ2⟩ : ∃ j : ℝ, j = 1 + P.β * ((1 - P.δ) * (1 - P.p) * J1 +
      (1 - (1 - P.δ) * (1 - P.p)) * V1) := ⟨_, rfl⟩
  obtain ⟨P1, hP1⟩ : ∃ x : ℝ, x = J1 - P.β * V2 - (1 - P.θ) * S1 := ⟨_, rfl⟩
  obtain ⟨P2, hP2⟩ : ∃ x : ℝ, x = J2 - P.β * V1 - (1 - P.θ) * S2 := ⟨_, rfl⟩
  have hh1 : L.h₁ P m = P.θ * L.g₁ P m + (1 - P.θ) * L.f₁ P m := rfl
  have hh2 : L.h₂ P m = P.θ * L.g₂ P m + (1 - P.θ) * L.f₂ P m := rfl
  have hΓ1 : (U1 + V1) - P.β * (U2 + V2) = L.h₁ P m * S1 := by
    rw [hh1]; linear_combination hU1 + hV1
  have hΓ2 : (U2 + V2) - P.β * (U1 + V1) = L.h₂ P m * S2 := by
    rw [hh2]; linear_combination hU2 + hV2
  have hJW2 : J2 + W2 = S2 + P.β * (U1 + V1) := by
    linear_combination hJ2 + hW2 + P.β * (1 - P.δ) * (1 - P.p) * hJ1 - hS2 -
      P.β * (1 - P.δ) * (1 - P.p) * hΓ1
  have hz2 : J2 + W2 = 1 - P.xL + P.β * (P.δ * (U1 + V1) +
      (1 - P.δ) * ((1 - P.p) * (J1 + W1) + P.p * (U1 + V1))) := by
    linear_combination hJ2 + hW2
  have hz1 : J1 + W1 = 1 - P.xL + P.β * (P.δ * (U2 + V2) +
      (1 - P.δ) * ((1 - P.p) * (J2 + W2) + P.p * (1 - P.xH + P.β * (U1 + V1)))) := by
    linear_combination hJ1 - P.β * (1 - P.δ) * (1 - P.p) * hJW2 + hS1 + P.β * (1 - P.δ) * hΓ2
  have hXs : Values.Solves ⟨J1, J2, V1, V2, W1, W2, U1, U2, P1, P2⟩ P L m := by
    unfold Values.Solves
    dsimp only
    have ha1 : W1 - P.β * U2 + P1 = P.θ * S1 := by linear_combination hP1 + hJ1
    have hb1 : J1 - P.β * V2 - P1 = (1 - P.θ) * S1 := by linear_combination -hP1
    have ha2 : W2 - P.β * U1 + P2 = P.θ * S2 := by linear_combination hP2 + hJW2
    have hb2 : J2 - P.β * V1 - P2 = (1 - P.θ) * S2 := by linear_combination -hP2
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · linear_combination hz1 + P.β * (1 - P.δ) * (1 - P.p) * hz2 - hW1
    · linear_combination hJ2
    · linear_combination hV1 + L.f₁ P m * hP1
    · linear_combination hV2 + L.f₂ P m * hP2
    · linear_combination hW1
    · linear_combination hW2
    · linear_combination hU1 - L.g₁ P m * (hP1 + hJ1)
    · linear_combination hU2 - L.g₂ P m * (hP2 + hJW2)
    · rw [nash_iff hθ0 hθ1]
      refine ⟨by rw [ha1]; exact mul_nonneg hθ0.le hS1pos.le,
        by rw [hb1]; exact mul_nonneg (by linarith) hS1pos.le, ?_⟩
      linear_combination hP1 + (1 - P.θ) * hJ1
    · rw [nash_iff hθ0 hθ1]
      refine ⟨by rw [ha2]; exact mul_nonneg hθ0.le hS2pos.le,
        by rw [hb2]; exact mul_nonneg (by linarith) hS2pos.le, ?_⟩
      linear_combination hP2 + (1 - P.θ) * hJW2
  have hA2' : 0 ≤ (1 - P.xH) - L.h₂ P m * S2 :=
    (th_high P.xL P.xH (P.β * (1 - P.δ)) P.p (L.h₁ P m) (L.h₂ P m) S1 S2 (by linarith)
      hbh0 hbh1 hp0 hp1 h10 h11 h20 h21 hS1 hS2).mpr hhi.le
  have hA12' : (1 - P.xH) * (1 + P.β * (1 - P.δ)) - L.h₁ P m * S1 -
      P.β * (1 - P.δ) * L.h₂ P m * S2 ≤ 0 :=
    (th_low P.xL P.xH (P.β * (1 - P.δ)) P.p (L.h₁ P m) (L.h₂ P m) S1 S2 (by linarith)
      hbh0 hbh1 hp0 hp1 h10 h11 h20 h21 hS1 hS2).mpr hlo.le
  have hA2 : 0 ≤ 1 - P.xH + P.β * (U1 + V1) - (U2 + V2) := by linarith
  have e : (1 - P.xH + P.β * (U2 + V2) - (U1 + V1)) +
      P.β * (1 - P.δ) * (1 - P.xH + P.β * (U1 + V1) - (U2 + V2)) =
      (1 - P.xH) * (1 + P.β * (1 - P.δ)) - L.h₁ P m * S1 -
        P.β * (1 - P.δ) * L.h₂ P m * S2 := by
    linear_combination (-1 : ℝ) * hΓ1 - P.β * (1 - P.δ) * hΓ2
  have hA12 : (1 - P.xH + P.β * (U2 + V2) - (U1 + V1)) +
      P.β * (1 - P.δ) * (1 - P.xH + P.β * (U1 + V1) - (U2 + V2)) ≤ 0 := by
    rw [e]; exact hA12'
  have hopt : PeriodicPlanOptimal P ⟨J1, J2, V1, V2, W1, W2, U1, U2, P1, P2⟩ :=
    (opt_iff P hP (U1 + V1) (U2 + V2) (J1 + W1) (J2 + W2) hz1 hz2).mpr ⟨hA2, hA12⟩
  obtain ⟨c, hIC, hpv1, hpv2⟩ := contract_exists P hP ⟨J1, J2, V1, V2, W1, W2, U1, U2, P1, P2⟩
  unfold PeriodicEquilibrium
  exact ⟨L, ⟨J1, J2, V1, V2, W1, W2, U1, U2, P1, P2⟩, c, hL, N0_ne hP hm hL, hXs, hopt, hIC,
    hpv1, hpv2⟩

end BSP812

open BonusSeason.Periodic in
theorem solution (P : Params) (hP : P.Standing) (m : ℝ → ℝ → ℝ) (hm : MatchingA1 m)
    (L : MarketState) (hL : L.Solves P m) :
    (alphaLow P m L < P.matchImportance ∧ P.matchImportance < alphaHigh P m L →
      PeriodicEquilibrium P m) ∧
    (P.matchImportance < alphaLow P m L ∨ alphaHigh P m L < P.matchImportance →
      ¬ PeriodicEquilibrium P m) := by
  exact ⟨BSP812.dir1 P hP m hm L hL, BSP812.dir2 P hP m hm L hL⟩
