-- Prove2me | solution 1 for AvramDividend.Classical.avram_a23_affine_modulus_L1_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T09:01:35.004379+00:00
-- url     : https://prove2.me/submissions/e7e9d3d2-b0be-4113-9cc6-bd9bb83f434a

import Mathlib
open Filter

theorem solution
    (a b : ℕ → ℝ)
    (hb : Tendsto b atTop (nhds (0 : ℝ)))
    (ha : ∀ m, 0 ≤ a m)
    (hBound : ∀ ε : ℝ, 0 < ε → ∃ L : ℝ,
      0 ≤ L ∧ ∀ m, a m ≤ ε + L * b m) :
    Tendsto a atTop (nhds (0 : ℝ))  := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have he : 0 < ε / 2 := by linarith
  obtain ⟨L, hL, hUpper⟩ := hBound (ε/2) he
  have hT : Tendsto (fun m => ε/2 + L*b m)
      atTop (nhds (ε/2)) := by
    simpa using (tendsto_const_nhds.add (tendsto_const_nhds.mul hb))
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hT) (ε/2) he
  refine ⟨N, ?_⟩
  intro m hm
  have hS := hN m hm
  rw [Real.dist_eq] at hS
  have hLT : ε/2 + L*b m < ε := by
    have hh := (abs_lt.mp hS).2
    linarith
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (ha m)]
  linarith [hUpper m]
