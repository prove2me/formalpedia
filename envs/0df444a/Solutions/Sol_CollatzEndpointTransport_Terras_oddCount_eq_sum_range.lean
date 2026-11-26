-- Prove2me | solution 1 for CollatzEndpointTransport.Terras.oddCount_eq_sum_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:12:17.4138+00:00
-- url     : https://prove2.me/submissions/f86e3af8-da24-4484-8cc4-6a10d4e9c180

import Definitions.Def_CollatzEndpointTransport_Common_AffineCorrection
import Definitions.Def_CollatzEndpointTransport_Common_TerrasAffineIterate

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset
namespace CollatzEndpointTransport.Terras
theorem _root_.solution (H n : ℕ) :
    oddCount H n =
      ∑ i ∈ Finset.range H,
        if parityBit ((T^[i]) n) then 1 else 0 := by
  classical
  unfold oddCount
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  change (∑ i : Fin H,
      if parityBit ((T^[(i : ℕ)]) n) = true then 1 else 0) =
    ∑ i ∈ Finset.range H,
      if parityBit ((T^[i]) n) then 1 else 0
  simpa using
    (Fin.sum_univ_eq_sum_range
      (fun i => if parityBit ((T^[i]) n) = true then (1 : ℕ) else 0) H)
end CollatzEndpointTransport.Terras
