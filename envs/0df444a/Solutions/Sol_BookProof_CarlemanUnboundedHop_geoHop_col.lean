-- Prove2me | solution 1 for BookProof.CarlemanUnboundedHop.geoHop_col
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:02:12.205232+00:00
-- url     : https://prove2.me/submissions/8c264aed-abae-41ff-ac46-50e57f6230e2

-- Generated from ChapterCarlemanUnboundedHop.lean — solution of BookProof.CarlemanUnboundedHop.geoHop_col
import Mathlib
import Definitions.Def_ChapterCarlemanUnboundedHop
import Theorems.Thm_BookProof_CarlemanUnboundedHop_geoHop_norm_off
import Definitions.Def_ChapterNavierStokesDeficiency
open BookProof.NavierStokesFlow.LpNat
open BookProof.CarlemanUnboundedHop




open Finset

noncomputable section

variable {a : ℕ → ℕ → ℂ} {u : ℕ → ℂ} {A θ Θ : ℕ → ℝ}

set_option maxHeartbeats 1000000 in
theorem solution {b : ℕ → ℝ} {rho : ℝ} (hrho : 0 ≤ rho) (hrho1 : rho < 1) (k : ℕ) :
    Memℓp (fun n => geoHop b rho n k) 2 := by

  refine memLpTwo_of_summable_normSq ?_
  refine (summable_nat_add_iff (k + 1)).mp ?_
  have heq : ∀ m : ℕ, ‖geoHop b rho (m + (k + 1)) k‖ ^ 2
      = (1 + (k : ℝ)) ^ 2 * ((rho ^ 2) ^ (m + 1)) := by
    intro m
    have hne : m + (k + 1) ≠ k := by omega
    have hmin : min (m + (k + 1)) k = k := by omega
    have hmax : max (m + (k + 1)) k = m + (k + 1) := by omega
    have hsub : m + (k + 1) - k = m + 1 := by omega
    rw [geoHop_norm_off hrho hne, hmin, hmax, hsub, mul_pow, ← pow_mul, ← pow_mul]
    ring_nf
  have hgeo : Summable (fun m : ℕ => (1 + (k : ℝ)) ^ 2 * ((rho ^ 2) ^ (m + 1))) := by
    have hlt : rho ^ 2 < 1 := by nlinarith
    have hsum : Summable (fun m : ℕ => (rho ^ 2) ^ m) :=
      (hasSum_geometric_of_lt_one (by positivity) hlt).summable
    have := (hsum.mul_left (rho ^ 2)).mul_left ((1 + (k : ℝ)) ^ 2)
    refine this.congr fun m => ?_
    rw [pow_succ]
    ring
  exact hgeo.congr fun m => (heq m).symm
