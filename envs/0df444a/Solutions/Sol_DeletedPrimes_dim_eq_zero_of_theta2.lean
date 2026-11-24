-- Prove2me | solution 1 for DeletedPrimes.dim_eq_zero_of_theta2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:20:35.552699+00:00
-- url     : https://prove2.me/submissions/1701e1ee-3ed7-4072-8d99-2469aa7737ab

import Definitions.Def_DeletedPrimes_Legendre
import Definitions.Def_DeletedPrimes_Exponents
import Definitions.Def_DeletedPrimes_GoodScales
import Definitions.Def_DeletedPrimes_CompositeFloor
import Theorems.Thm_DeletedPrimes_floor_theta2
import Theorems.Thm_DeletedPrimes_dim_nonneg


set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution {S : Set ℕ} (F : Frame S) (Q : Quantization S)
    (L : LandauAtOne S) (h : theta2 S = 0) : dim S = 0 := by
  have hα1 : dim S < 1 := L (by rw [h]; norm_num)
  rcases (dim_nonneg S).lt_or_eq with hα0 | hα0
  · exfalso
    have hfl := floor_theta2 hα0 hα1 F Q
    rw [h] at hfl
    have : 0 < dim S / 2 * min (1 / 2) (1 - dim S) :=
      mul_pos (by linarith) (lt_min (by norm_num) (by linarith))
    linarith
  · exact hα0.symm
end DeletedPrimes
