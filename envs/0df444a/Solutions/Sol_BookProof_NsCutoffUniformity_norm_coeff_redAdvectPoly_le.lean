-- Prove2me | solution 1 for BookProof.NsCutoffUniformity.norm_coeff_redAdvectPoly_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-05T19:48:11.302204+00:00
-- url     : https://prove2.me/submissions/f1691d71-71b3-47d6-9e89-9e96567d6f79

-- Generated from ChapterNsCutoffUniformity.lean — solution of BookProof.NsCutoffUniformity.norm_coeff_redAdvectPoly_le
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
    (hk : ∀ j, |k j| ≤ Λ) (p : Fin n) (i : Fin 3) (m : Fin (n * 6) →₀ ℕ) :
    ‖coeff m (redAdvectPoly k n p i)‖ ≤ 3 * Λ := by

  rw [redAdvectPoly, coeff_sum]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ j : Fin 3, ‖coeff m (C ((k j : ℝ) : ℂ) * (X (ruIdx p j) * X (ruIdx p i)))‖
      ≤ ∑ _j : Fin 3, Λ := by
        refine Finset.sum_le_sum fun j _ => ?_
        refine (norm_coeff_C_mul_X_mul_X_le _ _ _ _).trans ?_
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact hk j
    _ = 3 * Λ := by simp [Finset.sum_const]
