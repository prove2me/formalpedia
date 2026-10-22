-- Prove2me | solution 1 for DefectCoverUp.USEquilibrium.welfare_difference
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T07:12:14.309753+00:00
-- url     : https://prove2.me/submissions/a4b559f6-fe0f-4a1c-a8c8-0fc9c3b807c8

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
    WRI P h ρ - WRNI P h ρ =
      post P ρ * chi1 P h - P.l * h / P.vbar * (P.vbar - h / 2) - P.C := by
  obtain ⟨hp, hr, hrp, hH, hpv, hC, hl0, hl1, -⟩ := hP
  have hv : P.vbar ≠ 0 := by linarith
  have hl : 1 - P.l ≠ 0 := by linarith
  have hH' : P.hbar ≠ 0 := by linarith
  have e2 : ∀ t : ℝ, (P.r + h) * (d P * t + dh P h * P.l) * g P h =
      ((P.r + h) * d P * g P h) * t + (P.r + h) * dh P h * P.l * g P h := by intro t; ring
  unfold WRI WRNI piRI piRNI SRI SRNI
  simp only [e2, cu_lin, cu_const, cu_CS P hv]
  unfold chi1 post d dh g atom
  field_simp
  ring
