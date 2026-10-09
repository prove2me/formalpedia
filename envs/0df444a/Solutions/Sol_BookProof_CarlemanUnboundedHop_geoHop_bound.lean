-- Prove2me | solution 1 for BookProof.CarlemanUnboundedHop.geoHop_bound
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:01:58.265791+00:00
-- url     : https://prove2.me/submissions/fa076796-21b5-42e3-b1fe-c47dba3a704d

-- Generated from ChapterCarlemanUnboundedHop.lean — solution of BookProof.CarlemanUnboundedHop.geoHop_bound
import Mathlib
import Definitions.Def_ChapterCarlemanUnboundedHop
import Theorems.Thm_BookProof_CarlemanUnboundedHop_geoHop_norm_off
open BookProof.CarlemanUnboundedHop




open Finset

noncomputable section

variable {a : ℕ → ℕ → ℂ} {u : ℕ → ℂ} {A θ Θ : ℕ → ℝ}

set_option maxHeartbeats 1000000 in
theorem solution {b : ℕ → ℝ} {rho : ℝ} (hrho : 0 ≤ rho) (n k : ℕ) (hnk : n < k) :
    ‖geoHop b rho n k‖ ≤ (1 + (n : ℝ)) * rho ^ (k - n) := by

  have hmin : min n k = n := min_eq_left hnk.le
  have hmax : max n k = k := max_eq_right hnk.le
  rw [geoHop_norm_off hrho (Nat.ne_of_lt hnk), hmin, hmax]
