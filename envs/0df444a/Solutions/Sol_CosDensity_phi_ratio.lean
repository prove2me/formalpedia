-- Prove2me | solution 1 for CosDensity.phi_ratio
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:37:18.475913+00:00
-- url     : https://prove2.me/submissions/de38a201-6171-4242-b367-01ee411da769

import Mathlib

theorem solution (p : ℕ) (V CV Q ν κ : ℝ) (hQ : 0 < Q) (hν0 : 0 < ν) (hν1 : ν < 1)
    (hκ : 0 < κ) (hV0 : 0 ≤ V) (hV : V ≤ CV * Q ^ p) :
    1 < (CV + κ) / (CV + κ * ν) ∧
      (CV + κ) / (CV + κ * ν) ≤ (V + κ * Q ^ p) / (V + κ * ν * Q ^ p) := by
  have hB : 0 < Q ^ p := pow_pos hQ p
  have hA : 0 ≤ CV := by
    by_contra hneg
    push_neg at hneg
    have : CV * Q ^ p < 0 := mul_neg_of_neg_of_pos hneg hB
    linarith
  have hκν : 0 < κ * ν := mul_pos hκ hν0
  have hd1 : 0 < CV + κ * ν := by linarith
  have hκνB : 0 < κ * ν * Q ^ p := mul_pos hκν hB
  have hd2 : 0 < V + κ * ν * Q ^ p := by linarith
  constructor
  · rw [one_lt_div hd1]
    nlinarith
  · rw [div_le_div_iff₀ hd1 hd2]
    have h1 : 0 ≤ κ * (1 - ν) := mul_nonneg hκ.le (by linarith)
    have h2 : 0 ≤ CV * Q ^ p - V := by linarith
    nlinarith [mul_nonneg h1 h2]
