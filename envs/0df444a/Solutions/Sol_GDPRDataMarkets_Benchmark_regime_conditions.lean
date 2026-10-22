-- Prove2me | solution 1 for GDPRDataMarkets.Benchmark.regime_conditions
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:20:12.454707+00:00
-- url     : https://prove2.me/submissions/620203e8-97e0-46b9-9812-608bccf69dc6

import Mathlib
import Definitions.Def_GDPRDataMarkets_Benchmark_Model
import Definitions.Def_GDPRDataMarkets_Benchmark_Reduced
set_option autoImplicit false
open MeasureTheory
open GDPRDataMarkets.Benchmark

theorem solution (P : Params) (hS : P.Standing) :
    vB P (P1B P) = vbar1B P ∧
    (P.c ≤ vbar1B P ↔ P.c ≤ T1 P) ∧
    (P.c ≤ T1 P → vbar1B P ≤ 1) ∧
    (vN P (p8 P) ≤ 1 ↔ P.c ≤ T2 P) ∧
    (vN P (p8 P) < P.c ↔
      (1 + P.d * P.sigma) / (1 + P.d * P.mu + P.d * P.sigma) < P.c) := by
  obtain ⟨hL, hLH, hd0, hd1, hc0⟩ := hS
  have hσ : 0 < P.sigma := by unfold Params.sigma; linarith
  have hμσ : P.sigma < P.mu := by unfold Params.mu Params.sigma; linarith
  have hμ : 0 < P.mu := by linarith
  have hD1 : 0 < 2 - P.d + 2 * P.d * P.sigma := by nlinarith [mul_pos hd0 hσ]
  have hE : 0 < 4 - P.d + 2 * P.d * P.mu + 2 * P.d * P.sigma := by nlinarith [mul_pos hd0 hσ, mul_pos hd0 hμ]
  have hF : 0 < 2 + P.d + P.d * P.mu + P.d * P.sigma := by nlinarith [mul_pos hd0 hσ, mul_pos hd0 hμ]
  have hG : 0 < 1 + P.d * P.sigma := by nlinarith [mul_pos hd0 hσ]
  have hH : 0 < 1 + P.d * P.mu + P.d * P.sigma := by nlinarith [mul_pos hd0 hσ, mul_pos hd0 hμ]
  have hT : 0 < 2 - P.d + 2 * P.d * P.sigma + 2 * P.d * P.mu := by nlinarith [mul_pos hd0 hσ, mul_pos hd0 hμ]
  have hdm : 0 < P.d * P.mu := mul_pos hd0 hμ
  have hD1' := hD1.ne'
  have hE' := hE.ne'
  have hF' := hF.ne'
  have hG' := hG.ne'
  have hH' := hH.ne'
  have hT' := hT.ne'
  have h1d : (1 + P.d) ≠ 0 := by linarith
  have hT1 : T1 P = (2 - P.d + 2 * P.d * P.sigma) / (2 - P.d + 2 * P.d * P.sigma + 2 * P.d * P.mu) := by
    unfold T1; congr 1; ring
  have key1 : vbar1B P - P.c = ((2 - P.d + 2 * P.d * P.sigma + 2 * P.d * P.mu) / (4 - P.d + 2 * P.d * P.mu + 2 * P.d * P.sigma)) * (T1 P - P.c) := by
    rw [hT1]; unfold vbar1B P1B
    field_simp
    ring
  have key2 : vbar1B P - 1 = 2 * (P.c - P.d * P.mu - 1) / (4 - P.d + 2 * P.d * P.mu + 2 * P.d * P.sigma) := by
    unfold vbar1B P1B
    field_simp
    ring
  have key3 : vN P (p8 P) - 1 = (1 + P.d) / (2 + P.d + P.d * P.mu + P.d * P.sigma) * (P.c - T2 P) := by
    unfold vN p8 T2
    field_simp
    ring
  have key4 : vN P (p8 P) - P.c = ((1 + P.d * P.mu + P.d * P.sigma) / (2 + P.d + P.d * P.mu + P.d * P.sigma)) *
      ((1 + P.d * P.sigma) / (1 + P.d * P.mu + P.d * P.sigma) - P.c) := by
    unfold vN p8
    field_simp
    ring
  have hk1 : 0 < (2 - P.d + 2 * P.d * P.sigma + 2 * P.d * P.mu) / (4 - P.d + 2 * P.d * P.mu + 2 * P.d * P.sigma) := by positivity
  have hk3 : 0 < (1 + P.d) / (2 + P.d + P.d * P.mu + P.d * P.sigma) := by positivity
  have hk4 : 0 < (1 + P.d * P.mu + P.d * P.sigma) / (2 + P.d + P.d * P.mu + P.d * P.sigma) := by positivity
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold vB vbar1B; rfl
  · constructor
    · intro h
      have : 0 ≤ vbar1B P - P.c := by linarith
      rw [key1] at this
      have := (mul_nonneg_iff_of_pos_left hk1).mp this
      linarith
    · intro h
      have : 0 ≤ T1 P - P.c := by linarith
      have := mul_nonneg hk1.le this
      rw [← key1] at this
      linarith
  · intro h
    have hT1le : T1 P ≤ 1 := by
      rw [hT1, div_le_one hT]; nlinarith [hdm]
    have : P.c ≤ 1 + P.d * P.mu := by nlinarith [hdm]
    have : vbar1B P - 1 ≤ 0 := by
      rw [key2]
      apply div_nonpos_of_nonpos_of_nonneg _ hE.le
      linarith
    linarith
  · constructor
    · intro h
      have : vN P (p8 P) - 1 ≤ 0 := by linarith
      rw [key3] at this
      have : P.c - T2 P ≤ 0 := by
        by_contra hh
        push_neg at hh
        have := mul_pos hk3 hh
        linarith
      linarith
    · intro h
      have : (1 + P.d) / (2 + P.d + P.d * P.mu + P.d * P.sigma) * (P.c - T2 P) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hk3.le (by linarith)
      rw [← key3] at this
      linarith
  · constructor
    · intro h
      have : vN P (p8 P) - P.c < 0 := by linarith
      rw [key4] at this
      have : (1 + P.d * P.sigma) / (1 + P.d * P.mu + P.d * P.sigma) - P.c < 0 := by
        by_contra hh
        push_neg at hh
        have := mul_nonneg hk4.le hh
        linarith
      linarith
    · intro h
      have : (1 + P.d * P.mu + P.d * P.sigma) / (2 + P.d + P.d * P.mu + P.d * P.sigma) *
          ((1 + P.d * P.sigma) / (1 + P.d * P.mu + P.d * P.sigma) - P.c) < 0 :=
        mul_neg_of_pos_of_neg hk4 (by linarith)
      rw [← key4] at this
      linarith
