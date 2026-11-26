-- Prove2me | solution 1 for FirstPassageLinearTransport.firstPassage_final_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:24:19.713394+00:00
-- url     : https://prove2.me/submissions/c91f8b01-22bc-42b0-9607-951bd2441ef4

import Definitions.Def_FirstPassageLinearTransport_Parity
import Definitions.Def_FirstPassageLinearTransport_FirstPassage
import Theorems.Thm_FirstPassageLinearTransport_orbit_succ


set_option autoImplicit true
open FirstPassageLinearTransport
namespace FirstPassageLinearTransport
theorem _root_.solution {Y n k : ℕ}
    (hfp : IsFirstPassage Y n (k + 1)) :
    orbit k n % 2 = 0 := by
  rcases Nat.mod_two_eq_zero_or_one (orbit k n) with heven | hodd
  · exact heven
  · have hprev : Y < orbit k n := hfp.2 k (by omega)
    have hland : orbit (k + 1) n ≤ Y := hfp.1
    have hstep := two_mul_shortcut_of_odd hodd
    rw [← orbit_succ] at hstep
    omega
end FirstPassageLinearTransport
