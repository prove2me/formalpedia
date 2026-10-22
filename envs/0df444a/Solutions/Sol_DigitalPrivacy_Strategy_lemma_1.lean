-- Prove2me | solution 1 for DigitalPrivacy.Strategy.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:07:45.70829+00:00
-- url     : https://prove2.me/submissions/4ac51b9d-7cae-4db9-9938-0c4f58cb6955

import Mathlib
import Definitions.Def_DigitalPrivacy_Strategy_Setting
set_option autoImplicit false
open DigitalPrivacy.Strategy

lemma vvkeyG (ξ s t T : ℝ) (hξ : 0 < ξ) (hs : 0 < s) (ht : ξ ^ 2 ≤ t) (hT : T = max (ξ * s) (ξ ^ 2)) :
    (t - ξ ^ 2) * (s ^ 2 - t) / t ≤ (T - ξ ^ 2) * (s ^ 2 - T) / T ∧
      ((t - ξ ^ 2) * (s ^ 2 - t) / t = (T - ξ ^ 2) * (s ^ 2 - T) / T → t = T) := by
  have hξ2 : 0 < ξ ^ 2 := by positivity
  have htpos : 0 < t := lt_of_lt_of_le hξ2 ht
  have hTpos : 0 < T := by rw [hT]; exact lt_max_of_lt_right hξ2
  have hdiff : (T - ξ ^ 2) * (s ^ 2 - T) / T - (t - ξ ^ 2) * (s ^ 2 - t) / t
      = (t - T) * (t * T - ξ ^ 2 * s ^ 2) / (t * T) := by
    field_simp; ring
  rcases le_total (ξ * s) (ξ ^ 2) with h | h
  · -- T = ξ^2
    have hT' : T = ξ ^ 2 := by rw [hT]; exact max_eq_right h
    have hs_le : s ≤ ξ := by nlinarith
    have hss : s ^ 2 ≤ ξ ^ 2 := by nlinarith
    have e : (t - T) * (t * T - ξ ^ 2 * s ^ 2) / (t * T) = (t - T) * (t - s ^ 2) / t := by
      rw [hT']; field_simp
    have hnn : 0 ≤ (t - T) * (t - s ^ 2) / t := by
      apply div_nonneg _ htpos.le
      exact mul_nonneg (by linarith) (by linarith)
    constructor
    · have := hdiff; rw [e] at this; linarith
    · intro heq
      have h0 : (t - T) * (t - s ^ 2) / t = 0 := by rw [← e, ← hdiff]; linarith
      rw [div_eq_zero_iff] at h0
      rcases h0 with h0 | h0
      · rcases mul_eq_zero.1 h0 with h1 | h1
        · linarith
        · nlinarith
      · exact absurd h0 htpos.ne'
  · -- T = ξ s
    have hT' : T = ξ * s := by rw [hT]; exact max_eq_left h
    have e : (t - T) * (t * T - ξ ^ 2 * s ^ 2) / (t * T) = (t - T) ^ 2 / t := by
      have : ξ ^ 2 * s ^ 2 = T ^ 2 := by rw [hT']; ring
      rw [this]; field_simp
    have hnn : 0 ≤ (t - T) ^ 2 / t := div_nonneg (sq_nonneg _) htpos.le
    constructor
    · have := hdiff; rw [e] at this; linarith
    · intro heq
      have h0 : (t - T) ^ 2 / t = 0 := by rw [← e, ← hdiff]; linarith
      rw [div_eq_zero_iff] at h0
      rcases h0 with h0 | h0
      · nlinarith [pow_eq_zero_iff (n := 2) (a := t - T) (by norm_num) |>.1 h0]
      · exact absurd h0 htpos.ne'

theorem solution (β ρ ψ P ξ : ℝ) (hB : Basic β ρ ψ P) (hξ : ξ ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ max (Ch β ρ ψ P ξ) 0 ∧
    ∀ C : ℝ, 0 ≤ C →
      profit β ρ ψ P ξ C ≤ profit β ρ ψ P ξ (max (Ch β ρ ψ P ξ) 0) ∧
      (profit β ρ ψ P ξ C = profit β ρ ψ P ξ (max (Ch β ρ ψ P ξ) 0) →
        C = max (Ch β ρ ψ P ξ) 0) := by
  obtain ⟨hβ0, hβ1, hρ0, hρ1, hψ, hP0, hP1⟩ := hB
  obtain ⟨hξ0, hξ1⟩ := hξ
  have hb : 0 < 1 - β := by linarith
  refine ⟨le_max_right _ _, ?_⟩
  intro C hC
  rcases hξ0.eq_or_lt with h0 | hpos
  · subst h0
    have hCh : Ch β ρ ψ P 0 = 0 := by simp [Ch]
    rw [hCh, max_self]
    simp only [profit, abar, if_true]
    constructor
    · nlinarith [mul_nonneg hψ.le hC]
    · intro h
      have : ψ * C = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hψ.ne'
  · have hξne : ξ ≠ 0 := hpos.ne'
    have h1P : 0 < 1 - P + P * ξ := by nlinarith [mul_nonneg (sub_nonneg.2 hP1) (sub_nonneg.2 hξ1)]
    have h1ρ : 0 < 1 + ρ * ξ := by nlinarith [mul_nonneg hρ0 hξ0]
    set s := Real.sqrt ((1 / ψ) * (1 + ρ * ξ) * (1 - P + P * ξ)) with hsdef
    have hin : 0 < (1 / ψ) * (1 + ρ * ξ) * (1 - P + P * ξ) := by positivity
    have hs : 0 < s := Real.sqrt_pos.2 hin
    have hs2 : s ^ 2 = (1 / ψ) * (1 + ρ * ξ) * (1 - P + P * ξ) := Real.sq_sqrt hin.le
    have hψs : (1 + ρ * ξ) * (1 - P + P * ξ) = ψ * s ^ 2 := by
      rw [hs2]; field_simp
    -- profit formula
    have hform : ∀ C : ℝ, 0 ≤ C → profit β ρ ψ P ξ C
        = ψ / (1 - β) * (((1 - β) * C + ξ ^ 2 - ξ ^ 2) * (s ^ 2 - ((1 - β) * C + ξ ^ 2)) / ((1 - β) * C + ξ ^ 2)) := by
      intro C hC
      have hden : 0 < (1 - β) * C + ξ ^ 2 := by positivity
      have habar : abar β ρ ξ C * ((1 - β) * C + ξ ^ 2) = C * (1 + ρ * ξ) := by
        simp only [abar, if_neg hξne]; field_simp
      have : profit β ρ ψ P ξ C = ψ * C * (s ^ 2 - ((1 - β) * C + ξ ^ 2)) / ((1 - β) * C + ξ ^ 2) := by
        rw [eq_div_iff hden.ne']
        simp only [profit]
        linear_combination (1 - P + P * ξ) * habar + C * hψs
      rw [this]
      field_simp
      ring
    set T := max (ξ * s) (ξ ^ 2) with hT
    have hCstar : (1 - β) * max (Ch β ρ ψ P ξ) 0 + ξ ^ 2 = T := by
      have : Ch β ρ ψ P ξ = (1 / (1 - β)) * (-ξ ^ 2 + ξ * s) := rfl
      rw [this, hT]
      rcases le_total (ξ * s) (ξ ^ 2) with h | h
      · have : (1 / (1 - β)) * (-ξ ^ 2 + ξ * s) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
        rw [max_eq_right this, max_eq_right h]; ring
      · have : 0 ≤ (1 / (1 - β)) * (-ξ ^ 2 + ξ * s) := mul_nonneg (by positivity) (by linarith)
        rw [max_eq_left this, max_eq_left h]; field_simp; ring
    have hCs0 : 0 ≤ max (Ch β ρ ψ P ξ) 0 := le_max_right _ _
    have hpc : 0 < ψ / (1 - β) := by positivity
    have ht : ξ ^ 2 ≤ (1 - β) * C + ξ ^ 2 := by nlinarith
    obtain ⟨k1, k2⟩ := vvkeyG ξ s ((1 - β) * C + ξ ^ 2) T hpos hs ht hT
    rw [hform C hC, hform _ hCs0, hCstar]
    refine ⟨?_, ?_⟩
    · exact mul_le_mul_of_nonneg_left (by simpa using k1) hpc.le
    · intro h
      have h' := mul_left_cancel₀ hpc.ne' h
      have := k2 (by simpa using h')
      have : (1 - β) * C = (1 - β) * max (Ch β ρ ψ P ξ) 0 := by linarith
      exact mul_left_cancel₀ hb.ne' this
