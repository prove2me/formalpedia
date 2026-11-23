-- Prove2me | solution 1 for CompanionTheory.PlacePermOperatorBicommutantSpan.ind_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:02:25.791375+00:00
-- url     : https://prove2.me/submissions/f7a512ea-95f6-4541-992a-2f28f5ee57e2

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_IsOpenCoset
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_ind_of_mem
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_ind_of_not

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
theorem _root_.solution {a b x y : V} {L L' : AddSubgroup V} (h : x - a ∈ L ↔ y - b ∈ L') : ind a L x = ind b L' y := by
  by_cases hx : x - a ∈ L
  · rw [ind_of_mem hx, ind_of_mem (h.1 hx)]
  · rw [ind_of_not hx, ind_of_not (mt h.2 hx)]
end CompanionTheory.PlacePermOperatorBicommutantSpan
