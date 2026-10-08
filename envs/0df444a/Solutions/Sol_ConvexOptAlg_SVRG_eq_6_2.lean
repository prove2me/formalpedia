-- Prove2me | solution 1 for ConvexOptAlg.SVRG.eq_6_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T15:51:48.322231+00:00
-- url     : https://prove2.me/submissions/dc325a3b-c5e3-4c12-b1dc-a85da442e5f8

import Mathlib
import Definitions.Def_ConvexOptAlg_SVRG_Defs

open scoped InnerProductSpace

open scoped InnerProductSpace in open ConvexOptAlg.SVRG in
theorem solution {n m : ℕ}
    (gs : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (η : ℝ) (x y xstar : EuclideanSpace ℝ (Fin n)) (i : Fin m) :
    ‖(x - η • direction gs x y i) - xstar‖ ^ 2 =
      ‖x - xstar‖ ^ 2 - 2 * η * ⟪direction gs x y i, x - xstar⟫_ℝ +
        η ^ 2 * ‖direction gs x y i‖ ^ 2 := by
  have h : (x - η • direction gs x y i) - xstar = (x - xstar) - η • direction gs x y i := by
    abel
  rw [h, norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    real_inner_comm]
  ring
