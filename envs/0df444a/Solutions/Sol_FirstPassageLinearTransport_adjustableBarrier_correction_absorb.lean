-- Prove2me | solution 1 for FirstPassageLinearTransport.adjustableBarrier_correction_absorb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:41:04.96511+00:00
-- url     : https://prove2.me/submissions/e635466a-95b6-46a9-bed1-4009a6db5c71

import Definitions.Def_FirstPassageLinearTransport_EntropyBarrier
import Definitions.Def_FirstPassageLinearTransport_Envelope
import Definitions.Def_FirstPassageLinearTransport_AdjustableEnvelope
import Theorems.Thm_FirstPassageLinearTransport_three_rpow_adjustableBarrierHeight_sq
import Theorems.Thm_FirstPassageLinearTransport_a0_pos
import Theorems.Thm_FirstPassageLinearTransport_centralOrbitScale_ge_n_rpow_neg_gap
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell



set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {lambda t : ℝ} {M n k : ℕ}
    (ht : 0 ≤ t) (hkM : k ≤ M) (hnShell : n ∈ dyadicShell M)
    (hstartup :
      2 * (2 + Real.sqrt 3) ≤
        (2 : ℝ) ^ ((a0 + t - 2 * lambda * t) * (M : ℝ))) :
    2 * ((2 + Real.sqrt 3) *
        (3 : ℝ) ^ adjustableBarrierHeight lambda t M *
        (3 : ℝ) ^ adjustableBarrierHeight lambda t M) ≤
      centralOrbitScale k * (n : ℝ) ^ (1 + t) := by
  have hnLowerNat : 2 ^ M ≤ n := (mem_dyadicShell.mp hnShell).1
  have hnLower : (2 : ℝ) ^ M ≤ n := by exact_mod_cast hnLowerNat
  have hnPosNat : 0 < n := by
    exact lt_of_lt_of_le (pow_pos (by omega) M) hnLowerNat
  have hnPos : (0 : ℝ) < n := by exact_mod_cast hnPosNat
  have hcentral := centralOrbitScale_ge_n_rpow_neg_gap hkM hnShell
  have hbarrierSq := three_rpow_adjustableBarrierHeight_sq lambda t M
  have hpowNonneg :
      0 ≤ (2 : ℝ) ^ (2 * lambda * t * (M : ℝ)) := by positivity
  have hstartupMul := mul_le_mul_of_nonneg_right hstartup hpowNonneg
  have hleft :
      2 * ((2 + Real.sqrt 3) *
          (3 : ℝ) ^ adjustableBarrierHeight lambda t M *
          (3 : ℝ) ^ adjustableBarrierHeight lambda t M) ≤
        (2 : ℝ) ^ ((a0 + t) * (M : ℝ)) := by
    calc
      2 * ((2 + Real.sqrt 3) *
          (3 : ℝ) ^ adjustableBarrierHeight lambda t M *
          (3 : ℝ) ^ adjustableBarrierHeight lambda t M) =
          (2 * (2 + Real.sqrt 3)) *
            (2 : ℝ) ^ (2 * lambda * t * (M : ℝ)) := by
              rw [← hbarrierSq]
              ring
      _ ≤ (2 : ℝ) ^ ((a0 + t - 2 * lambda * t) * (M : ℝ)) *
          (2 : ℝ) ^ (2 * lambda * t * (M : ℝ)) := hstartupMul
      _ = (2 : ℝ) ^ ((a0 + t) * (M : ℝ)) := by
        rw [← Real.rpow_add (by norm_num)]
        congr 1
        ring
  have hbase :
      (2 : ℝ) ^ ((a0 + t) * (M : ℝ)) ≤ (n : ℝ) ^ (a0 + t) := by
    have hexp : 0 ≤ a0 + t := add_nonneg a0_pos.le ht
    calc
      (2 : ℝ) ^ ((a0 + t) * (M : ℝ)) =
          ((2 : ℝ) ^ M) ^ (a0 + t) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
            congr 1
            ring
      _ ≤ (n : ℝ) ^ (a0 + t) :=
        Real.rpow_le_rpow (by positivity) hnLower hexp
  have hscale :
      (n : ℝ) ^ (a0 + t) ≤
        centralOrbitScale k * (n : ℝ) ^ (1 + t) := by
    have hexp : a0 + t = -driftGap + (1 + t) := by
      unfold driftGap
      ring
    rw [hexp, Real.rpow_add hnPos]
    exact mul_le_mul_of_nonneg_right hcentral (by positivity)
  exact hleft.trans (hbase.trans hscale)
end FirstPassageLinearTransport
