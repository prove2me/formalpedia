-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.sourceEndpoint_mem_centralLevelEndpointSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:36:30.217833+00:00
-- url     : https://prove2.me/submissions/5b8425ba-ffba-4111-8f17-a33d3ab70209

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiShell
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalNonlinearShell
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralLevelSourceSet_eq_pairImage
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_map_mem_mixedTargetSet


set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real Topology
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.centralPullbackSourceCodeDecidableEq
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {M s : ℕ} {theta eta : ℝ} {x : SourceCode M}
    (hx : x ∈ centralLevelSourceSet M s theta eta) :
    sourceEndpoint x ∈ centralLevelEndpointSet M s theta eta := by
  classical
  rw [centralLevelSourceSet_eq_pairImage] at hx
  rcases Finset.mem_image.mp hx with ⟨p, hp, rfl⟩
  exact map_mem_mixedTargetSet
    (Finset.univ : Finset (Fin M))
    (centralLevelCohortSet M s theta eta)
    (fun u => cohortEndpoint u)
    (Finset.mem_univ p.1) (Finset.mem_sigma.mp hp).2
end CollatzEndpointTransport.FixedTotal
