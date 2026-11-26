-- Prove2me | solution 1 for FD1D.V5.LocalPolicy.massRight_eq_count_mul_rateRight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:23:06.781883+00:00
-- url     : https://prove2.me/submissions/cb526de3-3107-4cc8-96e4-1e9e2c1ec753

import Definitions.Def_FD1D_V5_LocalPolicy
import Definitions.Def_FD1D_V5_LocalInvariants
import Theorems.Thm_FD1D_V5_LocalPolicy_massLeft_eq_count_mul_rateLeft
import Theorems.Thm_FD1D_V5_LocalPolicy_massLeft_swap
import Theorems.Thm_FD1D_V5_LocalPolicy_rateLeft_swap


set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.LocalPolicy
noncomputable section
namespace FD1D.V5.LocalPolicy
theorem _root_.solution
    (a p h : ℝ) (x y : ℕ) :
    massRight a p h x y = (y : ℝ) * rateRight a p h x y := by
  calc
    massRight a p h x y = massLeft a p h y x :=
      (massLeft_swap a p h x y).symm
    _ = (y : ℝ) * rateLeft a p h y x :=
      massLeft_eq_count_mul_rateLeft a p h y x
    _ = (y : ℝ) * rateRight a p h x y := by
      rw [rateLeft_swap]
end FD1D.V5.LocalPolicy
