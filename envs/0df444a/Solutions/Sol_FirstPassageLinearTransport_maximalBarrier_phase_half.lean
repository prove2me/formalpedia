-- Prove2me | solution 1 for FirstPassageLinearTransport.maximalBarrier_phase_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:06:06.100599+00:00
-- url     : https://prove2.me/submissions/33dee49d-0349-406c-8cb1-d39f11922fa4

import Mathlib.Algebra.Ring.GeomSum
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Definitions.Def_FirstPassageLinearTransport_Envelope
import Theorems.Thm_FirstPassageLinearTransport_three_rpow_maximalBarrierHeight
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell



set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution {n M : ℕ} {t : ℝ}
    (ht : 0 ≤ t) (hnShell : n ∈ dyadicShell M) :
    (3 : ℝ) ^ maximalBarrierHeight t M ≤ (n : ℝ) ^ (t / 2) := by
  have hnLowerNat : 2 ^ M ≤ n := (mem_dyadicShell.mp hnShell).1
  have hnLower : (2 : ℝ) ^ M ≤ n := by exact_mod_cast hnLowerNat
  rw [three_rpow_maximalBarrierHeight]
  calc
    (2 : ℝ) ^ (t * (M : ℝ) / 2) =
        ((2 : ℝ) ^ M) ^ (t / 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      congr 1
      ring
    _ ≤ (n : ℝ) ^ (t / 2) :=
      Real.rpow_le_rpow (by positivity) hnLower (by positivity)
end FirstPassageLinearTransport
