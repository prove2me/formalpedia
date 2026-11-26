-- Prove2me | solution 1 for FirstPassageLinearTransport.rawOrbit_rawTime_eq_orbit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:33:10.516132+00:00
-- url     : https://prove2.me/submissions/ad65c229-696e-4d26-a6d5-9bc57bea318e

import Definitions.Def_FirstPassageLinearTransport_Basic
import Definitions.Def_FirstPassageLinearTransport_RawDynamics
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_succ
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_add
import Theorems.Thm_FirstPassageLinearTransport_rawCollatz_eq_shortcut_of_even
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_two_eq_shortcut_of_odd
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_oddCount_succ
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_succ
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero


attribute [local simp] FirstPassageLinearTransport.rawOrbit_zero

set_option autoImplicit true
open FirstPassageLinearTransport
namespace FirstPassageLinearTransport
theorem _root_.solution (n k : ℕ) :
    rawOrbit (rawTime n k) n = orbit k n := by
  induction k with
  | zero => simp [rawTime]
  | succ k ih =>
      rcases Nat.mod_two_eq_zero_or_one (orbit k n) with heven | hodd
      · have hbit : (parityBit n k : ℕ) = 0 := by
          simpa [parityBit] using heven
        have ih' : rawOrbit (k + oddCount n k) n = orbit k n := by
          simpa [rawTime] using ih
        rw [rawTime, oddCount_succ, hbit, add_zero]
        rw [show k + 1 + oddCount n k = 1 + (k + oddCount n k) by omega,
          rawOrbit_add, ih', rawOrbit_succ, rawOrbit_zero, orbit_succ,
          rawCollatz_eq_shortcut_of_even heven]
      · have hbit : (parityBit n k : ℕ) = 1 := by
          simpa [parityBit] using hodd
        have ih' : rawOrbit (k + oddCount n k) n = orbit k n := by
          simpa [rawTime] using ih
        rw [rawTime, oddCount_succ, hbit]
        rw [show k + 1 + (oddCount n k + 1) =
            2 + (k + oddCount n k) by omega,
          rawOrbit_add, ih', orbit_succ,
          rawOrbit_two_eq_shortcut_of_odd hodd]
end FirstPassageLinearTransport
