-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.fixedTotal_firstMoment_exact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:38:23.327312+00:00
-- url     : https://prove2.me/submissions/5bf60807-5774-4890-80ca-f2d06ed862e9

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCompositionRecurrence
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalFirstMoment
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_lengthPowSum_formula
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_numeratorSum_formula

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    (N : ℕ) (hN : 0 < N) :
    2 * (∑ c : Composition N,
        (3 ^ c.length + syracuseNumerator c)) =
      (N + 7) * 4 ^ (N - 1) := by
  rw [Finset.sum_add_distrib, Nat.mul_add]
  have hlen := lengthPowSum_formula N hN
  have hnum := numeratorSum_formula N hN
  change
    2 * lengthPowSum N + 2 * numeratorSum N =
      (N + 7) * 4 ^ (N - 1)
  rw [hlen, hnum]
  ring
end CollatzEndpointTransport.FixedTotal
