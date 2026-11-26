-- Prove2me | solution 1 for CollatzEndpointTransport.Terras.affineCorrection_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:12:06.760798+00:00
-- url     : https://prove2.me/submissions/46451184-1cf7-4589-91e0-b4c3e4c1f03d

import Definitions.Def_CollatzEndpointTransport_Common_TerrasParityBijection
import Definitions.Def_CollatzEndpointTransport_Common_AffineCorrection
import Theorems.Thm_CollatzEndpointTransport_Terras_affineCorrectionTerm_nonneg

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset
namespace CollatzEndpointTransport.Terras
theorem _root_.solution (k n : ℕ) :
    0 ≤ affineCorrection k n := by
  exact Finset.sum_nonneg fun i _ => affineCorrectionTerm_nonneg k n i
end CollatzEndpointTransport.Terras
