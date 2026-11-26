-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.centralLevelRenyiFactor_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:16:00.770297+00:00
-- url     : https://prove2.me/submissions/8f0cbc4e-4b30-4605-af56-6531df6d4903

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiShell
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalNonlinearShell
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real Topology
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.centralPullbackSourceCodeDecidableEq
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    (M s : ℕ) (theta eta : ℝ) :
    ((((3 : ℝ) ^ (s + 1)) /
        (sourceOddLevel M s).card) ^ theta) *
      (∑ y ∈ centralLevelEndpointSet M s theta eta,
        (centralLevelFiberCard M s theta eta y : ℝ) ^ (1 + theta)) =
      centralLevelRenyiInformation M s theta eta := by
  unfold centralLevelRenyiInformation
  rw [Real.div_rpow (by positivity) (by positivity)]
end CollatzEndpointTransport.FixedTotal
