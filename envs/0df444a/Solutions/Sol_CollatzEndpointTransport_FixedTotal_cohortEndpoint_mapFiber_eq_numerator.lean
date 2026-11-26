-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.cohortEndpoint_mapFiber_eq_numerator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:35:49.488018+00:00
-- url     : https://prove2.me/submissions/00a40099-61ce-4d8e-ac72-0ba95b7b9c2b

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalEndpointBridge
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalEndpointMoment
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_cohortEndpoint_eq_iff_numeratorResidue
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumerator_prependOne
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_wordCorrectionFrom_nil
import Theorems.Thm_CollatzEndpointTransport_Terras_integerCorrection_zero
attribute [local simp] CollatzEndpointTransport.FixedTotal.encodeBlocks_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.encodeBlocks_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumerator_prependOne
attribute [local simp] CollatzEndpointTransport.FixedTotal.wordCorrectionFrom_nil
attribute [local simp] CollatzEndpointTransport.Terras.integerCorrection_zero



set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.endpointCompositionDecidableEq
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {M s : ℕ} (u : Fin M)
    {c : Composition (M - (u : ℕ))}
    (hc : c ∈ fixedSet (M - (u : ℕ)) s) :
    mapFiber (fixedSet (M - (u : ℕ)) s)
        (cohortEndpoint u) (cohortEndpoint u c) =
      mapFiber (fixedSet (M - (u : ℕ)) s)
        (cohortNumeratorResidue (s := s))
        (cohortNumeratorResidue (s := s) c) := by
  ext d
  simp only [mapFiber, Finset.mem_filter]
  constructor
  · rintro ⟨hd, hout⟩
    exact ⟨hd, (cohortEndpoint_eq_iff_numeratorResidue u hd hc).1 hout⟩
  · rintro ⟨hd, hres⟩
    exact ⟨hd, (cohortEndpoint_eq_iff_numeratorResidue u hd hc).2 hres⟩
end CollatzEndpointTransport.FixedTotal
