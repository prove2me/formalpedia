-- Prove2me | solution 1 for CollatzEndpointTransport.QuantitativeDensity.mem_pullbackWitnessSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:56:43.781202+00:00
-- url     : https://prove2.me/submissions/391c7062-1fd6-419c-91b5-c2e60076869b

import Definitions.Def_CollatzEndpointTransport_Common_AffineCorrectionDensity
import Definitions.Def_CollatzEndpointTransport_Common_TerrasInitialWindow
import Definitions.Def_CollatzEndpointTransport_Common_QuantitativePullbackDefs
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_mem_collatzPullback
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_mem_basePullback
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_card_positivePrefix
attribute [local simp] CollatzEndpointTransport.QuantitativeDensity.card_positivePrefix


attribute [local simp] CollatzEndpointTransport.QuantitativeDensity.mem_collatzPullback
attribute [local simp] CollatzEndpointTransport.QuantitativeDensity.mem_basePullback

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.QuantitativeDensity
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.QuantitativeDensity
theorem _root_.solution
    {S : Set ℕ} {eta etaPrime alpha correctionTol : ℝ} {n : ℕ} :
    n ∈ pullbackWitnessSet S eta etaPrime alpha correctionTol ↔
      baseMap alpha n ∈ coneCore 2 etaPrime S ∧
      n ∈ Terras.parityGood eta ∧
      n ∈ Terras.affineCorrectionGood correctionTol := by
  simp only [pullbackWitnessSet, basePullback, Set.mem_inter_iff,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨hbase, hparity⟩, hcorr⟩
    exact ⟨hbase, hparity, hcorr⟩
  · rintro ⟨hbase, hparity, hcorr⟩
    exact ⟨⟨hbase, hparity⟩, hcorr⟩
end CollatzEndpointTransport.QuantitativeDensity
