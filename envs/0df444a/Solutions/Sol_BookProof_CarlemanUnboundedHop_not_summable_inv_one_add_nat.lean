-- Prove2me | solution 1 for BookProof.CarlemanUnboundedHop.not_summable_inv_one_add_nat
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:02:52.371976+00:00
-- url     : https://prove2.me/submissions/bda69630-a3e7-49ca-ae60-56203b98de57

-- Generated from ChapterCarlemanUnboundedHop.lean — solution of BookProof.CarlemanUnboundedHop.not_summable_inv_one_add_nat
import Mathlib
import Definitions.Def_ChapterCarlemanUnboundedHop
open BookProof.CarlemanUnboundedHop




open Finset

noncomputable section

variable {a : ℕ → ℕ → ℂ} {u : ℕ → ℂ} {A θ Θ : ℕ → ℝ}

set_option maxHeartbeats 1000000 in
theorem solution : ¬ Summable (fun n : ℕ => (1 + (n : ℝ))⁻¹) := by

  intro h
  refine Real.not_summable_natCast_inv ?_
  have h1 : Summable (fun n : ℕ => (((n : ℝ) + 1))⁻¹) := by simpa [add_comm] using h
  exact (summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ))⁻¹) 1).mp (by simpa using h1)
