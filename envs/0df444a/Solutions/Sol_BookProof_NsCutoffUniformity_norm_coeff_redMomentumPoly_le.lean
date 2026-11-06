-- Prove2me | solution 1 for BookProof.NsCutoffUniformity.norm_coeff_redMomentumPoly_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-05T19:48:15.34619+00:00
-- url     : https://prove2.me/submissions/982b5c86-7372-400f-8477-451e5a03c15a

-- Generated from ChapterNsCutoffUniformity.lean — solution of BookProof.NsCutoffUniformity.norm_coeff_redMomentumPoly_le
import Mathlib
import Definitions.Def_ChapterNsCutoffUniformity
import Definitions.Def_ChapterNavierStokesFullEulerianFock
open BookProof.NsCutoffUniformity




open MvPolynomial BookProof.NsFullEuler

noncomputable section

variable {n : ℕ}

variable {n : ℕ}
variable {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution {Λ : ℝ} {k : Fin 3 → ℝ}
    (hk : ∀ j, |k j| ≤ Λ) (p : Fin n) (m : Fin (n * 6) →₀ ℕ) :
    ‖coeff m (redMomentumPoly k n p)‖ ≤ 3 * Λ := by

  rw [redMomentumPoly, coeff_sum]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ j : Fin 3, ‖coeff m (C ((k j : ℝ) : ℂ) * X (ruIdx p j))‖
      ≤ ∑ _j : Fin 3, Λ := by
        refine Finset.sum_le_sum fun j _ => ?_
        refine (norm_coeff_C_mul_X_le _ _ _).trans ?_
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact hk j
    _ = 3 * Λ := by simp [Finset.sum_const]
