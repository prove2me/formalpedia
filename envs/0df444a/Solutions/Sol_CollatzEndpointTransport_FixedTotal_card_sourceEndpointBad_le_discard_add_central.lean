-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.card_sourceEndpointBad_le_discard_add_central
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:38:05.428815+00:00
-- url     : https://prove2.me/submissions/dd6e3428-0a85-4aa2-88a4-16dfce339904

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiShell
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalNonlinearShell
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sourceEndpointBad_subset_central_union

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real Topology
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.centralPullbackSourceCodeDecidableEq
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    (S : Set ℕ) (M : ℕ) (theta eta : ℝ) :
    (sourceEndpointBad S M).card ≤
      (centralDiscardedSourceSet M theta eta).card +
        (centralSourceEndpointBad S M theta eta).card := by
  calc
    (sourceEndpointBad S M).card ≤
        (centralDiscardedSourceSet M theta eta ∪
          centralSourceEndpointBad S M theta eta).card :=
      Finset.card_le_card
        (sourceEndpointBad_subset_central_union S M theta eta)
    _ ≤ (centralDiscardedSourceSet M theta eta).card +
          (centralSourceEndpointBad S M theta eta).card :=
      Finset.card_union_le _ _
end CollatzEndpointTransport.FixedTotal
