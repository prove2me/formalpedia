-- Prove2me | solution 1 for BookProof.CarlemanUnboundedHop.cutMass_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:00:03.33193+00:00
-- url     : https://prove2.me/submissions/e92f490f-7231-4d21-b31c-9b241d22d4c9

-- Generated from ChapterCarlemanUnboundedHop.lean — solution of BookProof.CarlemanUnboundedHop.cutMass_nonneg
import Mathlib
import Definitions.Def_ChapterCarlemanUnboundedHop
import Theorems.Thm_BookProof_CarlemanUnboundedHop_Theta_nonneg
open BookProof.CarlemanUnboundedHop




open Finset

noncomputable section

variable {a : ℕ → ℕ → ℂ} {u : ℕ → ℂ} {A θ Θ : ℕ → ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (hθ0 : ∀ r, 0 ≤ θ r)
    (hΘ : ∀ j, HasSum (fun i => θ (i + j + 1)) (Θ j)) (N : ℕ) : 0 ≤ cutMass u Θ N := by

  refine add_nonneg (Finset.sum_nonneg fun n _ => mul_nonneg (Theta_nonneg hθ0 hΘ _)
    (by positivity)) ?_
  exact tsum_nonneg fun i => mul_nonneg (Theta_nonneg hθ0 hΘ _) (by positivity)
