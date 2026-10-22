-- Prove2me | solution 1 for GDPRDataMarkets.Benchmark.eq5_second_period_price
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:17:17.721993+00:00
-- url     : https://prove2.me/submissions/5ab7dfe8-edc2-498d-ba53-bc5148fdc526

import Mathlib
import Definitions.Def_GDPRDataMarkets_Benchmark_Model
set_option autoImplicit false
open MeasureTheory
open GDPRDataMarkets.Benchmark

theorem solution (P : Params) (hS : P.Standing) (σ : Profile) (p1 w : ℝ)
    (hthr : ∀ v ∈ Set.Icc (0 : ℝ) 1, (σ.buy p1 v = true ↔ w ≤ v))
    (hcw : P.c ≤ w) (hw1 : w ≤ 1) :
    ∀ q : ℝ, profit2 P σ p1 q ≤ profit2 P σ p1 ((w - P.c) / 2) := by
  intro q
  obtain ⟨_, _, _, _, hc0⟩ := hS
  have hset : ∀ r : ℝ, 0 ≤ r →
      {v : ℝ | v ∈ Set.Icc (0 : ℝ) 1 ∧ σ.buy p1 v = false ∧ r + P.c ≤ v} = Set.Ico (r + P.c) w := by
    intro r hr
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_Ico]
    constructor
    · rintro ⟨hv, hb, hrv⟩
      refine ⟨hrv, ?_⟩
      by_contra hwv
      push_neg at hwv
      have := (hthr v hv).mpr hwv
      rw [hb] at this
      exact Bool.false_ne_true this
    · rintro ⟨hrv, hvw⟩
      have hv0 : 0 ≤ v := by linarith
      have hv1 : v ≤ 1 := by linarith
      refine ⟨⟨hv0, hv1⟩, ?_, hrv⟩
      by_contra hb
      have hb' : σ.buy p1 v = true := by simpa using hb
      have := (hthr v ⟨hv0, hv1⟩).mp hb'
      linarith
  have hvol : ∀ r : ℝ, 0 ≤ r →
      (volume {v : ℝ | v ∈ Set.Icc (0 : ℝ) 1 ∧ σ.buy p1 v = false ∧ r + P.c ≤ v}).toReal
        = max (w - (r + P.c)) 0 := by
    intro r hr
    rw [hset r hr, Real.volume_Ico, ENNReal.toReal_ofReal']
  unfold profit2
  have hq0 : 0 ≤ (w - P.c) / 2 := by linarith
  rw [hvol _ hq0]
  have hmax : max (w - ((w - P.c) / 2 + P.c)) 0 = (w - P.c) / 2 := by
    rw [max_eq_left (by linarith)]; ring
  rw [hmax]
  by_cases hq : 0 ≤ q
  · rw [hvol q hq]
    have : q * max (w - (q + P.c)) 0 ≤ (w - P.c) / 2 * ((w - P.c) / 2) := by
      rcases le_total 0 (w - (q + P.c)) with h | h
      · rw [max_eq_left h]; nlinarith [sq_nonneg (q - (w - P.c) / 2)]
      · rw [max_eq_right h]; simp; nlinarith
    linarith
  · push_neg at hq
    have hnn : 0 ≤ (volume {v : ℝ | v ∈ Set.Icc (0 : ℝ) 1 ∧ σ.buy p1 v = false ∧ q + P.c ≤ v}).toReal :=
      ENNReal.toReal_nonneg
    have : q * (volume {v : ℝ | v ∈ Set.Icc (0 : ℝ) 1 ∧ σ.buy p1 v = false ∧ q + P.c ≤ v}).toReal ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hq.le hnn
    nlinarith [mul_self_nonneg ((w - P.c) / 2)]
