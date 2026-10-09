-- Prove2me | solution 1 for BookProof.CarlemanUnboundedHop.geoHop_norm_off
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:01:19.584985+00:00
-- url     : https://prove2.me/submissions/286affc6-f2f2-44dc-8bdc-c076e51da487

-- Generated from ChapterCarlemanUnboundedHop.lean — solution of BookProof.CarlemanUnboundedHop.geoHop_norm_off
import Mathlib
import Definitions.Def_ChapterCarlemanUnboundedHop
open BookProof.CarlemanUnboundedHop




open Finset

noncomputable section

variable {a : ℕ → ℕ → ℂ} {u : ℕ → ℂ} {A θ Θ : ℕ → ℝ}

set_option maxHeartbeats 1000000 in
theorem solution {b : ℕ → ℝ} {rho : ℝ} (hrho : 0 ≤ rho) {n k : ℕ} (h : n ≠ k) :
    ‖geoHop b rho n k‖ = (1 + ((min n k : ℕ) : ℝ)) * rho ^ (max n k - min n k) := by

  rw [geoHop, if_neg h, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
