-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.centralLevelBadEndpointSet_subset_actual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:41:59.437363+00:00
-- url     : https://prove2.me/submissions/502678d7-20de-4c92-8930-b95f7d7e9c71

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiShell
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalNonlinearShell
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralLevelEndpointSet_subset_actual

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real Topology
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.centralPullbackSourceCodeDecidableEq
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    (S : Set ℕ) (M s : ℕ) (theta eta : ℝ) :
    centralLevelBadEndpointSet S M s theta eta ⊆
      actualLevelBadEndpointSet S M s := by
  classical
  intro y hy
  rw [centralLevelBadEndpointSet, Finset.mem_filter] at hy
  rw [actualLevelBadEndpointSet, Finset.mem_filter]
  exact ⟨centralLevelEndpointSet_subset_actual M s theta eta hy.1, hy.2⟩
end CollatzEndpointTransport.FixedTotal
