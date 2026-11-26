-- Prove2me | solution 1 for FirstPassageLinearTransport.orbit_timeout_lt_three_pow_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:01:43.653825+00:00
-- url     : https://prove2.me/submissions/75891d0f-8ace-46fe-a447-d3a425334473

import Definitions.Def_FirstPassageLinearTransport_MovingLowParameters
import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Definitions.Def_FirstPassageLinearTransport_TimeoutCore
import Theorems.Thm_FirstPassageLinearTransport_affineCorrection_lt_two_pow_mul_three_pow
import Theorems.Thm_FirstPassageLinearTransport_exact_affine_iterate_scaled
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell



set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Topology
namespace FirstPassageLinearTransport
theorem _root_.solution {m x : ℕ}
    (hx : x ∈ dyadicShell m) :
    orbit m x < 3 ^ (oddCount x m + 1) := by
  have haffine := exact_affine_iterate_scaled x m
  have hcorr := affineCorrection_lt_two_pow_mul_three_pow x m
  have hxupper : x < 2 ^ (m + 1) := (mem_dyadicShell.mp hx).2
  have htwo : 0 < 2 ^ m := pow_pos (by omega) _
  have hthree : 0 < 3 ^ oddCount x m := pow_pos (by omega) _
  have hscaled :
      2 ^ m * orbit m x < 2 ^ m * 3 ^ (oddCount x m + 1) := by
    rw [haffine, pow_succ]
    have hxscaled :
        3 ^ oddCount x m * x <
          3 ^ oddCount x m * (2 * 2 ^ m) := by
      rw [pow_succ] at hxupper
      nlinarith
    nlinarith
  exact Nat.lt_of_mul_lt_mul_left hscaled
end FirstPassageLinearTransport
