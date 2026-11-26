-- Prove2me | solution 1 for CollatzEndpointTransport.Terras.oddCount_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:13:14.9134+00:00
-- url     : https://prove2.me/submissions/13d54bbd-e450-4df9-965b-f6a23b850fc1

import Definitions.Def_CollatzEndpointTransport_Common_AffineCorrection
import Definitions.Def_CollatzEndpointTransport_Common_TerrasAffineIterate
import Theorems.Thm_CollatzEndpointTransport_Terras_oddCount_eq_sum_range

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset
namespace CollatzEndpointTransport.Terras
theorem _root_.solution (k n : ℕ) :
    oddCount (k + 1) n =
      oddCount k n +
        if parityBit ((T^[k]) n) then 1 else 0 := by
  rw [oddCount_eq_sum_range, oddCount_eq_sum_range,
    Finset.sum_range_succ]
end CollatzEndpointTransport.Terras
