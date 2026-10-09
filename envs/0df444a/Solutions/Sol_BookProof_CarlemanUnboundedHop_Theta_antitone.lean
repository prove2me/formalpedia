-- Prove2me | solution 1 for BookProof.CarlemanUnboundedHop.Theta_antitone
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T22:59:23.968798+00:00
-- url     : https://prove2.me/submissions/c69f27a6-95e8-49a8-9c96-c2af2db768ae

-- Generated from ChapterCarlemanUnboundedHop.lean — solution of BookProof.CarlemanUnboundedHop.Theta_antitone
import Mathlib
import Definitions.Def_ChapterCarlemanUnboundedHop
import Theorems.Thm_BookProof_CarlemanUnboundedHop_Theta_succ_le
open BookProof.CarlemanUnboundedHop




open Finset

noncomputable section

variable {a : ℕ → ℕ → ℂ} {u : ℕ → ℂ} {A θ Θ : ℕ → ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (hθ0 : ∀ r, 0 ≤ θ r)
    (hΘ : ∀ j, HasSum (fun i => θ (i + j + 1)) (Θ j)) : Antitone Θ := by

  refine antitone_nat_of_succ_le fun j => Theta_succ_le hθ0 hΘ j
