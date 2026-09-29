-- Prove2me | solution 1 for Erdos9796Mission.eq_of_dist_eq_three_of_pairwise_ne
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-12T22:52:23.942788+00:00
-- url     : https://prove2.me/submissions/6ca4456e-acd3-444c-bb80-f9793c03e6a9

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Adam McKenna <adam@mysticflounder.ai>
-/

import Definitions.Def_Erdos9796Mission

open Erdos9796Mission

private theorem dist_sq_coord (x y : Plane) :
    dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq]
  simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]

private theorem noncollinear_of_cospherical_of_pairwise_ne
    (px py qx qy rx ry ax ay : ℝ)
    (hPQ : px ≠ qx ∨ py ≠ qy) (hPR : px ≠ rx ∨ py ≠ ry) (hQR : qx ≠ rx ∨ qy ≠ ry)
    (e1 : (ax - px) ^ 2 + (ay - py) ^ 2 = (ax - qx) ^ 2 + (ay - qy) ^ 2)
    (e2 : (ax - px) ^ 2 + (ay - py) ^ 2 = (ax - rx) ^ 2 + (ay - ry) ^ 2) :
    (qx - px) * (ry - py) - (qy - py) * (rx - px) ≠ 0 := by
  intro hD
  have hPQpos : (px - qx) ^ 2 + (py - qy) ^ 2 > 0 := by
    rcases hPQ with h | h
    · have h' : px - qx ≠ 0 := sub_ne_zero.mpr h
      have : (px - qx) ^ 2 > 0 := by positivity
      nlinarith [sq_nonneg (py - qy)]
    · have h' : py - qy ≠ 0 := sub_ne_zero.mpr h
      have : (py - qy) ^ 2 > 0 := by positivity
      nlinarith [sq_nonneg (px - qx)]
  obtain ⟨t, htx, hty⟩ :
      ∃ t : ℝ, rx - px = t * (qx - px) ∧ ry - py = t * (qy - py) := by
    by_cases hqxpx : qx - px = 0
    · have hqypy : qy - py ≠ 0 := by
        intro h
        apply absurd hPQpos
        have e1' : px - qx = 0 := by linarith [hqxpx]
        have e2' : py - qy = 0 := by linarith [h]
        rw [e1', e2']
        norm_num
      refine ⟨(ry - py) / (qy - py), ?_, ?_⟩
      · have hz : (qy - py) * (rx - px) = 0 := by
          rw [hqxpx] at hD
          linarith [hD]
        have hrxpx : rx - px = 0 := by
          rcases mul_eq_zero.mp hz with h | h
          · exact absurd h hqypy
          · exact h
        rw [hrxpx, hqxpx]
        ring
      · field_simp
    · refine ⟨(rx - px) / (qx - px), ?_, ?_⟩
      · field_simp
      · rw [div_mul_eq_mul_div, eq_div_iff hqxpx]
        linear_combination hD
  have key : t * (1 - t) * ((qx - px) ^ 2 + (qy - py) ^ 2) = 0 := by
    have p1 : 2 * ((ax - px) * (qx - px) + (ay - py) * (qy - py))
        = (qx - px) ^ 2 + (qy - py) ^ 2 := by
      nlinarith [e1]
    have p2 : 2 * ((ax - px) * (rx - px) + (ay - py) * (ry - py))
        = (rx - px) ^ 2 + (ry - py) ^ 2 := by
      nlinarith [e2]
    have hrx : rx = px + t * (qx - px) := by linarith
    have hry : ry = py + t * (qy - py) := by linarith
    rw [hrx, hry] at p2
    linear_combination -t * p1 + p2
  have hN : (qx - px) ^ 2 + (qy - py) ^ 2 > 0 := by nlinarith [hPQpos]
  have htt : t = 0 ∨ t = 1 := by
    have h0 : t * (1 - t) = 0 := by
      rcases mul_eq_zero.mp key with h | h
      · exact h
      · exact absurd h hN.ne'
    rcases mul_eq_zero.mp h0 with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  rcases htt with h | h
  · rw [h] at htx hty
    simp only [zero_mul] at htx hty
    rcases hPR with h2 | h2
    · exact h2 (by linarith)
    · exact h2 (by linarith)
  · rw [h] at htx hty
    simp only [one_mul] at htx hty
    rcases hQR with h2 | h2
    · exact h2 (by linarith)
    · exact h2 (by linarith)

theorem solution
    (P Q R A B : Plane)
    (hPQ : P ≠ Q) (hPR : P ≠ R) (hQR : Q ≠ R)
    (hAP_AQ : dist A P = dist A Q) (hAP_AR : dist A P = dist A R)
    (hBP_BQ : dist B P = dist B Q) (hBP_BR : dist B P = dist B R) :
    A = B := by
  have sq : ∀ X Y : Plane, dist X Y ^ 2 = (X 0 - Y 0) ^ 2 + (X 1 - Y 1) ^ 2 :=
    dist_sq_coord
  have eA1 : (A 0 - P 0) ^ 2 + (A 1 - P 1) ^ 2 = (A 0 - Q 0) ^ 2 + (A 1 - Q 1) ^ 2 := by
    rw [← sq, ← sq, hAP_AQ]
  have eA2 : (A 0 - P 0) ^ 2 + (A 1 - P 1) ^ 2 = (A 0 - R 0) ^ 2 + (A 1 - R 1) ^ 2 := by
    rw [← sq, ← sq, hAP_AR]
  have eB1 : (B 0 - P 0) ^ 2 + (B 1 - P 1) ^ 2 = (B 0 - Q 0) ^ 2 + (B 1 - Q 1) ^ 2 := by
    rw [← sq, ← sq, hBP_BQ]
  have eB2 : (B 0 - P 0) ^ 2 + (B 1 - P 1) ^ 2 = (B 0 - R 0) ^ 2 + (B 1 - R 1) ^ 2 := by
    rw [← sq, ← sq, hBP_BR]
  have dPQ : P 0 ≠ Q 0 ∨ P 1 ≠ Q 1 := by
    by_contra hc
    push Not at hc
    exact hPQ (by ext i; fin_cases i <;> simp [hc.1, hc.2])
  have dPR : P 0 ≠ R 0 ∨ P 1 ≠ R 1 := by
    by_contra hc
    push Not at hc
    exact hPR (by ext i; fin_cases i <;> simp [hc.1, hc.2])
  have dQR : Q 0 ≠ R 0 ∨ Q 1 ≠ R 1 := by
    by_contra hc
    push Not at hc
    exact hQR (by ext i; fin_cases i <;> simp [hc.1, hc.2])
  have hD : (Q 0 - P 0) * (R 1 - P 1) - (Q 1 - P 1) * (R 0 - P 0) ≠ 0 :=
    noncollinear_of_cospherical_of_pairwise_ne
      (P 0) (P 1) (Q 0) (Q 1) (R 0) (R 1) (A 0) (A 1) dPQ dPR dQR eA1 eA2
  have hα : (A 0 - B 0) * (Q 0 - P 0) + (A 1 - B 1) * (Q 1 - P 1) = 0 := by
    linear_combination (1 / 2) * eA1 - (1 / 2) * eB1
  have hβ : (A 0 - B 0) * (R 0 - P 0) + (A 1 - B 1) * (R 1 - P 1) = 0 := by
    linear_combination (1 / 2) * eA2 - (1 / 2) * eB2
  have hdxD : (A 0 - B 0) *
      ((Q 0 - P 0) * (R 1 - P 1) - (Q 1 - P 1) * (R 0 - P 0)) = 0 := by
    linear_combination (R 1 - P 1) * hα - (Q 1 - P 1) * hβ
  have hdyD : (A 1 - B 1) *
      ((Q 0 - P 0) * (R 1 - P 1) - (Q 1 - P 1) * (R 0 - P 0)) = 0 := by
    linear_combination (-(R 0 - P 0)) * hα + (Q 0 - P 0) * hβ
  have hdx : A 0 - B 0 = 0 := by
    rcases mul_eq_zero.mp hdxD with h | h
    · exact h
    · exact absurd h hD
  have hdy : A 1 - B 1 = 0 := by
    rcases mul_eq_zero.mp hdyD with h | h
    · exact h
    · exact absurd h hD
  ext i
  fin_cases i
  · change A 0 = B 0
    linarith [hdx]
  · change A 1 = B 1
    linarith [hdy]
