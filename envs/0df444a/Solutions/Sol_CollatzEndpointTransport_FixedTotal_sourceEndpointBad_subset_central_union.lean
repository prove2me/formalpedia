-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.sourceEndpointBad_subset_central_union
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:36:36.105652+00:00
-- url     : https://prove2.me/submissions/9b7e63cf-aa16-4ed9-9c6b-b34f7dd43791

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiShell
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalNonlinearShell
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_mem_centralDiscardedSourceSet_iff


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
    sourceEndpointBad S M ⊆
      centralDiscardedSourceSet M theta eta ∪
        centralSourceEndpointBad S M theta eta := by
  classical
  intro x hx
  rw [sourceEndpointBad, Finset.mem_filter] at hx
  by_cases hc : x ∈ centralSourceSet M theta eta
  · exact Finset.mem_union_right _ (by
      rw [centralSourceEndpointBad, Finset.mem_filter]
      exact ⟨hc, hx.2⟩)
  · exact Finset.mem_union_left _
      (mem_centralDiscardedSourceSet_iff.mpr hc)
end CollatzEndpointTransport.FixedTotal
