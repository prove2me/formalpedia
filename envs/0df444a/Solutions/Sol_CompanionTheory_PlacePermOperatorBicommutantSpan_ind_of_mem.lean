-- Prove2me | solution 1 for CompanionTheory.PlacePermOperatorBicommutantSpan.ind_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:58:46.930344+00:00
-- url     : https://prove2.me/submissions/e47c125e-e3c1-4328-ad0a-14914514d462

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
theorem _root_.solution {a x : V} {L : AddSubgroup V} (h : x - a ∈ L) : ind a L x = 1 :=
  Set.indicator_of_mem (s := {x | x - a ∈ L}) h _
end CompanionTheory.PlacePermOperatorBicommutantSpan
