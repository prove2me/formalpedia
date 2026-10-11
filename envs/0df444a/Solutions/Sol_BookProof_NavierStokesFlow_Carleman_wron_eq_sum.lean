-- Prove2me | solution 1 for BookProof.NavierStokesFlow.Carleman.wron_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:06:16.831632+00:00
-- url     : https://prove2.me/submissions/8ca953bd-2e82-47ef-ba99-711f79f0736a

-- Generated from ChapterNavierStokesCarleman.lean — solution of BookProof.NavierStokesFlow.Carleman.wron_eq_sum
import Mathlib
import Definitions.Def_ChapterNavierStokesCarleman
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.Carleman



open scoped ENNReal



open LpNat DiagonalEsa FullEsa

set_option maxHeartbeats 1000000 in
theorem solution (c w : ℕ → ℂ) (z : ℂ)
    (hrec : ∀ n, tridiagFun c w n = z * w n) (N : ℕ) :
    wron c w N
      = (z - starRingEnd ℂ z) * ∑ n ∈ Finset.range (N + 1), starRingEnd ℂ (w n) * w n := by

  induction N with
  | zero =>
    have h0 : c 0 * w 1 = z * w 0 := hrec 0
    have h0' : starRingEnd ℂ (c 0) * starRingEnd ℂ (w 1) = starRingEnd ℂ z * starRingEnd ℂ (w 0) :=
      by simpa [map_mul] using congrArg (starRingEnd ℂ) h0
    rw [zero_add, Finset.sum_range_one]
    simp only [wron]
    linear_combination starRingEnd ℂ (w 0) * h0 - w 0 * h0'
  | succ N ih =>
    have hN : starRingEnd ℂ (c N) * w N + c (N + 1) * w (N + 2) = z * w (N + 1) := hrec (N + 1)
    have hN' : c N * starRingEnd ℂ (w N) + starRingEnd ℂ (c (N + 1)) * starRingEnd ℂ (w (N + 2))
        = starRingEnd ℂ z * starRingEnd ℂ (w (N + 1)) := by
      simpa [map_add, map_mul] using congrArg (starRingEnd ℂ) hN
    rw [Finset.sum_range_succ, mul_add, ← ih]
    simp only [wron] at *
    linear_combination starRingEnd ℂ (w (N + 1)) * hN - w (N + 1) * hN'
