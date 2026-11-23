-- Prove2me | solution 1 for CompanionTheory.PlacePermOperatorBicommutantSpan.ind_of_not
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:58:55.5974+00:00
-- url     : https://prove2.me/submissions/5a5f34ca-171c-47ff-8591-8eff31190646

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
omit [TopologicalSpace V]
namespace CompanionTheory.PlacePermOperatorBicommutantSpan
theorem _root_.solution {a x : V} {L : AddSubgroup V} (h : x - a ∉ L) : ind a L x = 0 :=
  Set.indicator_of_notMem (s := {x | x - a ∈ L}) h _
end CompanionTheory.PlacePermOperatorBicommutantSpan
