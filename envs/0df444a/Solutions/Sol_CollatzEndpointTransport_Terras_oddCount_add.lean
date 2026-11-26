-- Prove2me | solution 1 for CollatzEndpointTransport.Terras.oddCount_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:58:00.06659+00:00
-- url     : https://prove2.me/submissions/d6ece946-37d9-4f3e-bf27-164425979f66

import Definitions.Def_CollatzEndpointTransport_Common_TerrasAffineIterate
import Definitions.Def_CollatzEndpointTransport_Common_TerrasIntegerAffine
import Theorems.Thm_CollatzEndpointTransport_Terras_integerCorrection_zero
import Theorems.Thm_CollatzEndpointTransport_Terras_oddCount_succ

attribute [local simp] CollatzEndpointTransport.Terras.integerCorrection_zero

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset
namespace CollatzEndpointTransport.Terras
theorem _root_.solution (k d n : ℕ) :
    oddCount (k + d) n =
      oddCount k n + oddCount d ((T^[k]) n) := by
  induction d with
  | zero => simp [oddCount]
  | succ d ih =>
      rw [Nat.add_succ, oddCount_succ, ih, oddCount_succ]
      have hcomm :
          (T^[k]) ((T^[d]) n) = (T^[d]) ((T^[k]) n) := by
        rw [← Function.iterate_add_apply,
          ← Function.iterate_add_apply, Nat.add_comm]
      rw [Function.iterate_add_apply]
      rw [hcomm]
      omega
end CollatzEndpointTransport.Terras
