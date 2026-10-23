-- Prove2me | solution 1 for CustomerVoice.OLearn.qStar_solves_10
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T20:39:09.575489+00:00
-- url     : https://prove2.me/submissions/7259c632-8f43-40f7-9136-e2808050f1c2

import Mathlib
import Definitions.Def_CustomerVoice_OLearn_Setting

open CustomerVoice.OLearn in
theorem solution (M : Model) (hM : M.Standing) (t : CustomerVoice.ALearn.BType) :
    M.qStar (M.θ t) ∈ Set.Icc 0 (M.γ * M.θ t / (M.s + M.γ * M.k)) ∧
    IsMaxOn (fun q => M.mu q (M.θ t) (M.θ t))
      (Set.Icc 0 (M.γ * M.θ t / (M.s + M.γ * M.k))) (M.qStar (M.θ t)) ∧
    (∀ q ∈ Set.Icc 0 (M.γ * M.θ t / (M.s + M.γ * M.k)),
      M.mu q (M.θ t) (M.θ t) = M.mu (M.qStar (M.θ t)) (M.θ t) (M.θ t) →
        q = M.qStar (M.θ t)) := by
  obtain ⟨hL, hLH, -, -, hg0, hg1, hk, hs⟩ := hM
  have hθ : 0 < M.θ t := by cases t <;> simp [Model.θ] <;> linarith
  generalize M.θ t = θ at hθ ⊢
  have hD : 0 < M.s + M.γ * M.k := by positivity
  set c := M.γ * θ / (M.s + M.γ * M.k) with hc
  have hc0 : 0 < c := by positivity
  have hck : c * M.k < θ := by
    rw [hc, div_mul_eq_mul_div, div_lt_iff₀ hD]; nlinarith [mul_pos hs hθ]
  set q0 := M.qStar θ with hq0
  have hq0' : q0 = min c (θ / (2 * M.k)) := rfl
  have hq0c : q0 ≤ c := by rw [hq0']; exact min_le_left _ _
  have hq0n : 0 ≤ q0 := by rw [hq0']; exact le_min hc0.le (by positivity)
  -- payoff on [0, c]
  have hmu : ∀ q, 0 ≤ q → q ≤ c → M.mu q θ θ = (1 - M.γ) * (θ * q - M.k * q ^ 2) := by
    intro q h0 h1
    unfold Model.mu
    rw [sub_self, max_self, max_eq_left]
    · ring
    · have : M.k * q ≤ M.k * c := mul_le_mul_of_nonneg_left h1 hk.le
      nlinarith
  -- key: f(q0) - f(q) ≥ 0, = 0 only at q0
  have key : ∀ q, 0 ≤ q → q ≤ c →
      (θ * q - M.k * q ^ 2 ≤ θ * q0 - M.k * q0 ^ 2) ∧
      (θ * q - M.k * q ^ 2 = θ * q0 - M.k * q0 ^ 2 → q = q0) := by
    intro q h0 h1
    rcases le_total c (θ / (2 * M.k)) with hcm | hcm
    · have e : q0 = c := by rw [hq0']; exact min_eq_left hcm
      rw [e]
      have hc2 : 2 * M.k * c ≤ θ := by rwa [le_div_iff₀ (by positivity), mul_comm] at hcm
      have id : θ * c - M.k * c ^ 2 - (θ * q - M.k * q ^ 2) = (c - q) * (θ - M.k * (c + q)) := by ring
      have hpos : 0 ≤ θ - M.k * (c + q) := by nlinarith [mul_le_mul_of_nonneg_left h1 hk.le]
      refine ⟨by nlinarith [mul_nonneg (sub_nonneg.2 h1) hpos], fun h => ?_⟩
      have : (c - q) * (θ - M.k * (c + q)) = 0 := by linarith
      rcases mul_eq_zero.1 this with h' | h'
      · linarith
      · nlinarith [mul_le_mul_of_nonneg_left h1 hk.le]
    · have e : q0 = θ / (2 * M.k) := by rw [hq0']; exact min_eq_right hcm
      rw [e]
      have id : θ * (θ / (2 * M.k)) - M.k * (θ / (2 * M.k)) ^ 2 - (θ * q - M.k * q ^ 2)
          = M.k * (q - θ / (2 * M.k)) ^ 2 := by field_simp; ring
      refine ⟨by nlinarith [mul_nonneg hk.le (sq_nonneg (q - θ / (2 * M.k)))], fun h => ?_⟩
      have : M.k * (q - θ / (2 * M.k)) ^ 2 = 0 := by linarith
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 ((mul_eq_zero.1 this).resolve_left hk.ne')
      linarith
  refine ⟨⟨hq0n, hq0c⟩, ?_, ?_⟩
  · intro q hq
    simp only [Set.mem_ofPred_eq]
    rw [hmu q hq.1 hq.2, hmu q0 hq0n hq0c]
    exact mul_le_mul_of_nonneg_left (key q hq.1 hq.2).1 (by linarith)
  · intro q hq h
    rw [hmu q hq.1 hq.2, hmu q0 hq0n hq0c] at h
    exact (key q hq.1 hq.2).2 (mul_left_cancel₀ (by linarith) h)
