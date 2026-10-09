-- Prove2me | solution 1 for BookProof.CarlemanUnboundedHop.geo_summable_tail
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:02:39.294648+00:00
-- url     : https://prove2.me/submissions/8c6eb55f-98ac-41f7-8cb1-4b7abec72087

-- Generated from ChapterCarlemanUnboundedHop.lean — solution of BookProof.CarlemanUnboundedHop.geo_summable_tail
import Mathlib
import Definitions.Def_ChapterCarlemanUnboundedHop
open BookProof.CarlemanUnboundedHop




open Finset

noncomputable section

variable {a : ℕ → ℕ → ℂ} {u : ℕ → ℂ} {A θ Θ : ℕ → ℝ}

set_option maxHeartbeats 1000000 in
theorem solution {rho : ℝ} (hrho : 0 ≤ rho) (hrho1 : rho < 1) :
    Summable (fun j : ℕ => rho ^ (j + 1) * (1 - rho)⁻¹) := by

  have hsum : Summable (fun j : ℕ => rho ^ j) :=
    (hasSum_geometric_of_lt_one hrho hrho1).summable
  have := ((hsum.mul_left rho).mul_right (1 - rho)⁻¹)
  refine this.congr fun j => ?_
  rw [pow_succ]
  ring
