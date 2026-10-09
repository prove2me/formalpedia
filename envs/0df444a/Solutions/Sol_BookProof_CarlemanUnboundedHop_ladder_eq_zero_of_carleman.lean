-- Prove2me | solution 1 for BookProof.CarlemanUnboundedHop.ladder_eq_zero_of_carleman
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:00:46.087766+00:00
-- url     : https://prove2.me/submissions/ca3de95f-e5cf-4090-b3fd-60fb0a1084f5

-- Generated from ChapterCarlemanUnboundedHop.lean — solution of BookProof.CarlemanUnboundedHop.ladder_eq_zero_of_carleman
import Mathlib
import Definitions.Def_ChapterCarlemanUnboundedHop
import Theorems.Thm_BookProof_CarlemanUnboundedHop_eq_zero_of_flux_small
import Theorems.Thm_BookProof_CarlemanUnboundedHop_Theta_nonneg
import Theorems.Thm_BookProof_CarlemanUnboundedHop_two_norm_flux_le
import Theorems.Thm_BookProof_CarlemanUnboundedHop_summable_cutMass
import Theorems.Thm_BookProof_CarlemanUnboundedHop_exists_mul_lt_of_not_summable_inv
open BookProof.CarlemanUnboundedHop




open Finset

noncomputable section

variable {a : ℕ → ℕ → ℂ} {u : ℕ → ℂ} {A θ Θ : ℕ → ℝ}

set_option maxHeartbeats 1000000 in
theorem solution {a : ℕ → ℕ → ℂ} {u : ℕ → ℂ} {z : ℂ} {A θ Θ : ℕ → ℝ}
    (hz : z.im ≠ 0) (hherm : IsHermitianKernel a) (hrec : LadderRecInf a u z)
    (hu : Summable fun n => ‖u n‖ ^ 2) (hθ0 : ∀ r, 0 ≤ θ r)
    (hΘ : ∀ j, HasSum (fun i => θ (i + j + 1)) (Θ j)) (hΘsum : Summable Θ)
    (hApos : ∀ n, 0 < A n) (hAmono : Monotone A)
    (hbd : ∀ n k, n < k → ‖a n k‖ ≤ A n * θ (k - n))
    (hcar : ¬ Summable fun n => (A n)⁻¹) :
    ∀ n, u n = 0 := by

  refine eq_zero_of_flux_small hz hherm hrec ?_
  intro ε hε N₀
  obtain ⟨N, hN, hlt⟩ := exists_mul_lt_of_not_summable_inv hApos
    (summable_cutMass hu (Theta_nonneg hθ0 hΘ) hΘsum) hcar
    (2 * ε) (by positivity) N₀
  refine ⟨N, hN, ?_⟩
  have hb := two_norm_flux_le (a := a) hu hθ0 hΘ (fun n => (hApos n).le) hAmono hbd N
  linarith
