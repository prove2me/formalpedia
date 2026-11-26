-- Prove2me | solution 1 for CollatzEndpointTransport.Terras.iterate_lt_three_pow_oddCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:31:47.61827+00:00
-- url     : https://prove2.me/submissions/040e241f-5c29-495f-9fd0-cbdb9bdbac18

import Definitions.Def_CollatzEndpointTransport_Common_TerrasAffineIterate
import Definitions.Def_CollatzEndpointTransport_Common_TerrasIntegerAffine
import Theorems.Thm_CollatzEndpointTransport_Terras_integerCorrection_zero
import Theorems.Thm_CollatzEndpointTransport_Terras_iterate_lt_three_pow_mul_remaining
attribute [local simp] CollatzEndpointTransport.Terras.integerCorrection_zero

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset
namespace CollatzEndpointTransport.Terras
theorem _root_.solution
    {M n : ℕ} (hn : n < 2 ^ M) :
    (T^[M]) n < 3 ^ oddCount M n := by
  simpa using
    (iterate_lt_three_pow_mul_remaining (M := M) (n := n) (j := M)
      (le_refl M) hn)
end CollatzEndpointTransport.Terras
