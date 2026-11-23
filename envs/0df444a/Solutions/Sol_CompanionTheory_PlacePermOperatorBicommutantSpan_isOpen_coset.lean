-- Prove2me | solution 1 for CompanionTheory.PlacePermOperatorBicommutantSpan.isOpen_coset
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:01:48.255622+00:00
-- url     : https://prove2.me/submissions/336e149f-c127-4a7a-9e7e-5d192d08b406

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_IsOpenCoset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Set
open scoped ENNReal ComplexConjugate
noncomputable section
open CompanionTheory CompanionTheory.PlacePermOperatorBicommutantSpan
open GlobalTheory.CompanionTheory.SW.Core
variable {V : Type} [AddCommGroup V] [TopologicalSpace V]
variable [IsTopologicalAddGroup V]
namespace CompanionTheory.PlacePermOperatorBicommutantSpan
theorem _root_.solution (a : V) {L : AddSubgroup V} (h : IsOpen (L : Set V)) : IsOpen {x | x - a ∈ L} :=
  h.preimage (continuous_id.sub continuous_const)
end CompanionTheory.PlacePermOperatorBicommutantSpan
