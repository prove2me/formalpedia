-- Prove2me | solution 1 for Dusart.chebyshev_theta_k2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-10-16T21:58:24.252385+00:00
-- url     : https://prove2.me/submissions/876fdeb2-a225-45df-93d2-e16cfeb53a9f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Dusart_chebyshev_theta_k2_finite
import Theorems.Thm_Dusart_chebyshev_theta_k2_large

theorem solution :
    ∀ t : ℝ, 3594641 ≤ t → |Chebyshev.theta t - t| ≤ (1 / 5) * t / Real.log t ^ 2 := by
  intro t ht
  rcases le_or_gt t 3584912847 with h | h
  · exact Dusart.chebyshev_theta_k2_finite t ht h
  · exact Dusart.chebyshev_theta_k2_large t (by linarith)
