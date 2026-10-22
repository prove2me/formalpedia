-- Prove2me | solution 1 for DefectCoverUp.USEquilibrium.report_without_investigation
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T07:12:15.895129+00:00
-- url     : https://prove2.me/submissions/ad43b46b-62e9-4328-891c-1ac77060ee18

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
    piNR P h ρ ≤ piRNI P h ρ := by
  obtain ⟨hp, hr, hrp, hH, hpv, hC, hl0, hl1, hth0, hth1, hal0, hal1, hK1, hK2, hPD0, hPD1⟩ := hP
  obtain ⟨hh0, hh1⟩ := hh
  obtain ⟨hρ0, hρ1⟩ := hρ
  have hl : 0 < 1 - P.l := by linarith
  have hpost : 0 ≤ post P ρ := by unfold post; nlinarith
  have hg : 0 ≤ g P h := by unfold g; positivity
  have hK : 0 ≤ P.K1 * h + P.K2 := by nlinarith
  unfold piNR
  rw [cu_const]
  have : 0 ≤ post P ρ * P.th * (P.K1 * h + P.K2) * ((1 - P.l - 0) * g P h) := by
    have : 0 ≤ (1 - P.l - 0) * g P h := by nlinarith
    positivity
  linarith
