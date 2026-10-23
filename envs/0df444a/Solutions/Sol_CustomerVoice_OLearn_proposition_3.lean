-- Prove2me | solution 1 for CustomerVoice.OLearn.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T20:42:47.317613+00:00
-- url     : https://prove2.me/submissions/b90563d2-4b08-4c8e-9858-ce3b79814ce4

import Mathlib
import Definitions.Def_CustomerVoice_OLearn_Setting
import Theorems.Thm_CustomerVoice_OLearn_seller_acceptance
import Theorems.Thm_CustomerVoice_OLearn_qStar_cases
import Theorems.Thm_CustomerVoice_OLearn_ic_necessary
import Theorems.Thm_CustomerVoice_OLearn_ic_case_low
import Theorems.Thm_CustomerVoice_OLearn_ic_case_high
import Theorems.Thm_CustomerVoice_OLearn_lambdaH1_le_lambdaH2_iff

open CustomerVoice.OLearn in
theorem solution (M : Model) (hM : M.Standing) :
    ((∃ bel : ℝ → CustomerVoice.ALearn.BType, M.OSepEq M.qO bel) ↔ M.θH / M.θL ≥ M.Lambda) ∧
    (M.θH / M.θL ≥ M.Lambda → M.γ ≤ M.s / M.k → M.OSepEq M.qO M.belLow) ∧
    (M.θH / M.θL ≥ M.Lambda → M.s / M.k ≤ M.γ → M.OSepEq M.qO M.belHigh) := by
  have hM' := hM
  obtain ⟨hL, hLH, -, -, hg0, hg1, hk, hs⟩ := hM'
  have hH0 : 0 < M.θH := by linarith
  have hθpos : ∀ t, 0 < M.θ t := by intro t; cases t <;> simp [Model.θ] <;> linarith
  have hD : 0 < M.s + M.γ * M.k := by positivity
  -- basic facts about the first-best requests
  have hq0 : ∀ t, 0 ≤ M.qO t := by
    intro t; have := hθpos t
    unfold Model.qO Model.qStar; apply le_min <;> positivity
  have hq2k : ∀ t, 2 * M.k * M.qO t ≤ M.θ t := by
    intro t
    have h : M.qO t ≤ M.θ t / (2 * M.k) := by unfold Model.qO Model.qStar; exact min_le_right _ _
    rwa [le_div_iff₀ (by positivity), mul_comm] at h
  have hqacc : ∀ t, M.accepts (M.θ t) (M.qO t) := by
    intro t
    refine (seller_acceptance M hM t (M.qO t) (hq0 t)).2 ?_
    unfold Model.qO Model.qStar; exact min_le_left _ _
  have hqne : M.qO .H ≠ M.qO .L := by
    intro h
    have eH : M.qO .H = min (M.γ * M.θH / (M.s + M.γ * M.k)) (M.θH / (2 * M.k)) := rfl
    have eL : M.qO .L = min (M.γ * M.θL / (M.s + M.γ * M.k)) (M.θL / (2 * M.k)) := rfl
    rw [eH, eL] at h
    have hc1 : 0 < M.γ / (M.s + M.γ * M.k) := by positivity
    have e1 : ∀ θ, M.γ * θ / (M.s + M.γ * M.k) = M.γ / (M.s + M.γ * M.k) * θ := by
      intro θ; ring
    have e2 : ∀ θ, θ / (2 * M.k) = 1 / (2 * M.k) * θ := by intro θ; ring
    rw [e1 M.θH, e1 M.θL, e2 M.θH, e2 M.θL] at h
    rcases le_total (M.γ / (M.s + M.γ * M.k)) (1 / (2 * M.k)) with hc | hc
    · rw [min_eq_left (mul_le_mul_of_nonneg_right hc hH0.le),
        min_eq_left (mul_le_mul_of_nonneg_right hc hL.le)] at h
      have := mul_left_cancel₀ hc1.ne' h; linarith
    · rw [min_eq_right (mul_le_mul_of_nonneg_right hc hH0.le),
        min_eq_right (mul_le_mul_of_nonneg_right hc hL.le)] at h
      have := mul_left_cancel₀ (by positivity : (1 / (2 * M.k)) ≠ 0) h; linarith
  -- payoff facts
  have mu_nonneg : ∀ q θ θh, 0 ≤ M.mu q θ θh := by
    intro q θ θh; unfold Model.mu
    have := le_max_right (θ * q - θh * q) 0
    have := le_max_right (θ * q - M.k * q ^ 2) 0
    have : 0 ≤ 1 - M.γ := by linarith
    positivity
  have mu_mono : ∀ θ θh q p, 0 ≤ q → q ≤ p → θh ≤ θ → 2 * M.k * p ≤ θ →
      M.mu q θ θh ≤ M.mu p θ θh := by
    intro θ θh q p h0 h1 h2 h3
    unfold Model.mu
    have hp0 : 0 ≤ p := le_trans h0 h1
    have hkq : M.k * q ≤ M.k * p := mul_le_mul_of_nonneg_left h1 hk.le
    have a1 : 0 ≤ θ * q - θh * q := by nlinarith
    have a2 : 0 ≤ θ * p - θh * p := by nlinarith
    have a3 : 0 ≤ θ * q - M.k * q ^ 2 := by nlinarith
    have a4 : 0 ≤ θ * p - M.k * p ^ 2 := by nlinarith
    rw [max_eq_left a1, max_eq_left a2, max_eq_left a3, max_eq_left a4]
    have : θ * q - M.k * q ^ 2 ≤ θ * p - M.k * p ^ 2 := by
      have : θ * p - M.k * p ^ 2 - (θ * q - M.k * q ^ 2) = (p - q) * (θ - M.k * (p + q)) := by ring
      nlinarith [mul_nonneg (sub_nonneg.2 h1) (show 0 ≤ θ - M.k * (p + q) by nlinarith)]
    have h4 : (θ - θh) * q ≤ (θ - θh) * p := mul_le_mul_of_nonneg_left h1 (by linarith)
    nlinarith
  have pay_acc : ∀ bel t q, M.accepts (M.θ (bel q)) q →
      M.pay bel t q = M.mu q (M.θ t) (M.θ (bel q)) := by
    intro bel t q h; unfold Model.pay; simp only [h, if_true]
  have pay_le : ∀ bel t q X, 0 ≤ X → (M.accepts (M.θ (bel q)) q →
      M.mu q (M.θ t) (M.θ (bel q)) ≤ X) → M.pay bel t q ≤ X := by
    intro bel t q X hX h; unfold Model.pay; split_ifs with ha
    · exact h ha
    · exact hX
  -- sufficiency, low case
  have suff_low : M.γ ≤ M.s / M.k → M.ICH' → M.ICL' → M.OSepEq M.qO M.belLow := by
    intro hγ hIH hIL
    have hbH : M.belLow (M.qO .H) = .H := by unfold Model.belLow; simp
    have hbL : M.belLow (M.qO .L) = .L := by unfold Model.belLow; simp [hqne.symm]
    have hbel : ∀ t, M.belLow (M.qO t) = t := by intro t; cases t <;> assumption
    have hon : ∀ t, M.pay M.belLow t (M.qO t) = M.mu (M.qO t) (M.θ t) (M.θ t) := by
      intro t; rw [pay_acc _ _ _ (by rw [hbel t]; exact hqacc t), hbel t]
    have hqL : M.qO .L = M.γ * M.θ .L / (M.s + M.γ * M.k) := (qStar_cases M hM .L).1 hγ
    refine ⟨hq0, hqne, hbel, ?_⟩
    intro t q hq
    rw [hon t]
    by_cases hqH : q = M.qO .H
    · subst hqH
      rw [pay_acc _ _ _ (by rw [hbH]; exact hqacc .H), hbH]
      cases t
      · exact le_rfl
      · exact hIL
    · have hb : M.belLow q = .L := by unfold Model.belLow; simp [hqH]
      apply pay_le _ _ _ _ (mu_nonneg _ _ _)
      rw [hb]
      intro ha
      have hqq : q ≤ M.qO .L := by rw [hqL]; exact (seller_acceptance M hM .L q hq).1 ha
      have h2k := hq2k .L
      cases t
      · refine le_trans (mu_mono _ _ _ _ hq hqq ?_ ?_) hIH
        · simp [Model.θ]; linarith
        · simp [Model.θ] at h2k ⊢; linarith
      · exact mu_mono _ _ _ _ hq hqq le_rfl h2k
  -- sufficiency, high case
  have suff_high : M.s / M.k ≤ M.γ → M.ICH' → M.OSepEq M.qO M.belHigh := by
    intro hγ hIH
    have hbH : M.belHigh (M.qO .H) = .H := by unfold Model.belHigh; simp [hqne]
    have hbL : M.belHigh (M.qO .L) = .L := by unfold Model.belHigh; simp
    have hbel : ∀ t, M.belHigh (M.qO t) = t := by intro t; cases t <;> assumption
    have hon : ∀ t, M.pay M.belHigh t (M.qO t) = M.mu (M.qO t) (M.θ t) (M.θ t) := by
      intro t; rw [pay_acc _ _ _ (by rw [hbel t]; exact hqacc t), hbel t]
    refine ⟨hq0, hqne, hbel, ?_⟩
    intro t q hq
    rw [hon t]
    by_cases hqL : q = M.qO .L
    · subst hqL
      rw [pay_acc _ _ _ (by rw [hbL]; exact hqacc .L), hbL]
      cases t
      · exact hIH
      · exact le_rfl
    · have hb : M.belHigh q = .H := by unfold Model.belHigh; simp [hqL]
      apply pay_le _ _ _ _ (mu_nonneg _ _ _)
      rw [hb]
      intro _
      have hqt : M.qO t = M.θ t / (2 * M.k) := (qStar_cases M hM t).2 hγ
      have hθt := hθpos t
      have hle : M.θ t ≤ M.θ .H := by cases t <;> simp [Model.θ]; linarith
      have hval : M.mu (M.qO t) (M.θ t) (M.θ t) = (1 - M.γ) * (M.θ t ^ 2 / (4 * M.k)) := by
        unfold Model.mu
        rw [hqt, sub_self, max_self]
        have : M.θ t * (M.θ t / (2 * M.k)) - M.k * (M.θ t / (2 * M.k)) ^ 2 = M.θ t ^ 2 / (4 * M.k) := by
          field_simp; ring
        rw [this, max_eq_left (by positivity)]; ring
      rw [hval]
      unfold Model.mu
      rw [max_eq_right (by nlinarith)]
      have hsq : M.θ t * q - M.k * q ^ 2 ≤ M.θ t ^ 2 / (4 * M.k) := by
        have : M.θ t ^ 2 / (4 * M.k) - (M.θ t * q - M.k * q ^ 2) = M.k * (q - M.θ t / (2 * M.k)) ^ 2 := by
          field_simp; ring
        nlinarith [mul_nonneg hk.le (sq_nonneg (q - M.θ t / (2 * M.k)))]
      have : max (M.θ t * q - M.k * q ^ 2) 0 ≤ M.θ t ^ 2 / (4 * M.k) := max_le hsq (by positivity)
      nlinarith
  -- the threshold characterization
  have hr1 : 1 < M.θH / M.θL := by rw [lt_div_iff₀ hL]; linarith
  have hA : M.θH / M.θL ≥ M.Lambda ↔ M.ICH' ∧ M.ICL' := by
    rcases le_total M.γ (M.s / M.k) with hγ | hγ
    · obtain ⟨h1, h2⟩ := ic_case_low M hM hγ
      have hmin : min M.LambdaH1 M.LambdaH2 = M.LambdaH1 :=
        min_eq_left ((lambdaH1_le_lambdaH2_iff M hM).2 hγ)
      unfold Model.Lambda; rw [hmin, h1, h2, ge_iff_le, max_le_iff]
    · obtain ⟨h1, h2⟩ := ic_case_high M hM hγ
      have hsk : M.s ≤ M.γ * M.k := by rwa [div_le_iff₀ hk] at hγ
      have hmin : min M.LambdaH1 M.LambdaH2 = M.LambdaH2 := by
        apply min_eq_right
        unfold Model.LambdaH1 Model.LambdaH2
        rw [div_le_div_iff₀ (by linarith) (by nlinarith)]
        nlinarith [mul_le_mul_of_nonneg_left hsk (show 0 ≤ (1 - M.γ) * (1 - M.γ) by positivity)]
      have hLL : M.LambdaL ≤ M.θH / M.θL := by
        unfold Model.LambdaL
        have : M.s / (M.γ * M.k) ≤ 1 := by rw [div_le_one (by positivity)]; exact hsk
        linarith
      have hICL : M.ICL' := h2.le
      unfold Model.Lambda; rw [hmin, ge_iff_le, max_le_iff, ← ge_iff_le, h1]
      exact ⟨fun h => ⟨h.1, hICL⟩, fun h => ⟨h.1, hLL⟩⟩
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rintro ⟨bel, hb⟩
    exact hA.2 (ic_necessary M hM bel hb)
  · intro h
    obtain ⟨hIH, hIL⟩ := hA.1 h
    rcases le_total M.γ (M.s / M.k) with hγ | hγ
    · exact ⟨_, suff_low hγ hIH hIL⟩
    · exact ⟨_, suff_high hγ hIH⟩
  · intro h hγ
    obtain ⟨hIH, hIL⟩ := hA.1 h
    exact suff_low hγ hIH hIL
  · intro h hγ
    exact suff_high hγ (hA.1 h).1
