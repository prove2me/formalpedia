-- Prove2me | solution 1 for ConvexOptAlg.Subgradient.thm_3_2_step
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-05T18:52:14.279589+00:00
-- url     : https://prove2.me/submissions/ca1eaa00-ea9a-4099-85b3-e93b65177e9c

import Mathlib
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol
import Definitions.Def_ConvexOptAlg_Subgradient_Defs

open ConvexOptAlg.Subgradient
open scoped RealInnerProductSpace

theorem solution {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (η : ℕ → ℝ) (x g : ℕ → EuclideanSpace ℝ (Fin n))
    (T : ℕ) (hrun : IsProjSubgradRun X f η x g T) (xstar : EuclideanSpace ℝ (Fin n))
    (hxstar : xstar ∈ X) (s : ℕ) (hs1 : 1 ≤ s) (hsT : s ≤ T) (hη : 0 < η s) :
    f (x s) - f xstar ≤
      1 / (2 * η s) * (‖x s - xstar‖ ^ 2 - ‖(x s - η s • g s) - xstar‖ ^ 2)
        + η s / 2 * ‖g s‖ ^ 2 := by
  have hsub := (hrun.2 s hs1 hsT).1 xstar hxstar
  have hexp : ‖(x s - η s • g s) - xstar‖ ^ 2 =
      ‖x s - xstar‖ ^ 2 - 2 * η s * ⟪g s, x s - xstar⟫ + η s ^ 2 * ‖g s‖ ^ 2 := by
    have : (x s - η s • g s) - xstar = (x s - xstar) - η s • g s := by abel
    rw [this, norm_sub_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      real_inner_comm]
    ring
  have key : 1 / (2 * η s) * (‖x s - xstar‖ ^ 2 - ‖(x s - η s • g s) - xstar‖ ^ 2)
      + η s / 2 * ‖g s‖ ^ 2 = ⟪g s, x s - xstar⟫ := by
    rw [hexp]
    field_simp
    ring
  rw [key]
  exact hsub
