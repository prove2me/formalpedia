-- Prove2me | solution 1 for CollatzEndpointTransport.Terras.parityLowerCutoff_cast_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:25:12.553549+00:00
-- url     : https://prove2.me/submissions/fc9152c9-5467-4d94-b109-10623602742d

import Mathlib.Algebra.Order.Floor.Semiring
import Definitions.Def_CollatzEndpointTransport_Common_TerrasShellRepetition
import Definitions.Def_CollatzEndpointTransport_Common_TerrasPrefixEvents

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset
namespace CollatzEndpointTransport.Terras
theorem _root_.solution
    {t : ℝ} (htHalf : t ≤ 1 / 2) (H : ℕ) :
    (parityLowerCutoff t H : ℝ) ≤ (1 / 2 - t) * H := by
  exact Nat.floor_le
    (mul_nonneg (sub_nonneg.mpr htHalf) (Nat.cast_nonneg H))
end CollatzEndpointTransport.Terras
