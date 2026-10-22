-- Prove2me | solution 1 for DefectCoverUp.USEquilibrium.profit_difference
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T07:12:14.980063+00:00
-- url     : https://prove2.me/submissions/d9de7cd4-fd59-4923-af1c-528683e1226e

import Mathlib
import Definitions.Def_DefectCoverUp_USEquilibrium_Model

open DefectCoverUp.USEquilibrium

lemma cu_CS (P : Params) (hv : P.vbar ≠ 0) (a : ℝ) :
    CS P a = (P.vbar - a) ^ 2 / (2 * P.vbar) := by
  unfold CS
  simp only [intervalIntegral.integral_mul_const]
  rw [intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_id
    intervalIntegrable_const, integral_id, intervalIntegral.integral_const, smul_eq_mul]
  field_simp
  ring

lemma cu_lin (A B b : ℝ) : ∫ t in (0 : ℝ)..b, (A * t + B) = A * b ^ 2 / 2 + B * b := by
  rw [intervalIntegral.integral_add (intervalIntegral.intervalIntegrable_id.const_mul A) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const, smul_eq_mul]
  ring

lemma cu_const (c b : ℝ) : ∫ t in (0 : ℝ)..b, c = b * c := by
  rw [intervalIntegral.integral_const, smul_eq_mul]; ring

theorem solution (P : Params) (hP : P.Standing)
    (h : ℝ) (hh : h ∈ Set.Ioc 0 P.hbar) (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    piRI P h ρ - piNR P h ρ =
      post P ρ * Omega1 P h - P.p * P.l * h / P.vbar := by
  obtain ⟨hp, hr, hrp, hH, hpv, hC, hl0, hl1, -⟩ := hP
  have hv : P.vbar ≠ 0 := by linarith
  have hl : 1 - P.l ≠ 0 := by linarith
  have hH' : P.hbar ≠ 0 := by linarith
  have e2 : ∀ t : ℝ, (P.r + h) * (d P * t + dh P h * P.l) * g P h =
      ((P.r + h) * d P * g P h) * t + (P.r + h) * dh P h * P.l * g P h := by intro t; ring
  unfold piRI piNR piRNI
  simp only [e2, cu_lin, cu_const]
  unfold Omega1 post d dh g atom
  field_simp
  ring
