-- Prove2me | solution 1 for BookProof.CarlemanUnboundedHop.Theta_succ_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T22:59:11.027522+00:00
-- url     : https://prove2.me/submissions/80c1c416-0d0e-4746-83f6-fad9f5df4c2a

-- Generated from ChapterCarlemanUnboundedHop.lean — solution of BookProof.CarlemanUnboundedHop.Theta_succ_le
import Mathlib
import Definitions.Def_ChapterCarlemanUnboundedHop
open BookProof.CarlemanUnboundedHop




open Finset

noncomputable section

variable {a : ℕ → ℕ → ℂ} {u : ℕ → ℂ} {A θ Θ : ℕ → ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (hθ0 : ∀ r, 0 ≤ θ r)
    (hΘ : ∀ j, HasSum (fun i => θ (i + j + 1)) (Θ j)) (j : ℕ) : Θ (j + 1) ≤ Θ j := by

  have h := (hΘ j).summable.tsum_eq_zero_add
  rw [(hΘ j).tsum_eq] at h
  have h2 : ∑' b : ℕ, θ (b + 1 + j + 1) = Θ (j + 1) := by
    rw [← (hΘ (j + 1)).tsum_eq]
    exact tsum_congr fun b => by congr 1; omega
  rw [h2] at h
  have := hθ0 (0 + j + 1)
  linarith
