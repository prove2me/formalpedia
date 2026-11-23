-- Prove2me | solution 1 for CompanionTheory.PlacePermOperatorBicommutantSpan.ind_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:06:11.130776+00:00
-- url     : https://prove2.me/submissions/e6a15566-09d8-4a7a-a1c3-541e38d3d028

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_IsOpenCoset
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_ind_congr

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
theorem _root_.solution {a l : V} {L : AddSubgroup V} (x : V) (hl : l ∈ L) : ind a L (x + l) = ind a L x :=
  ind_congr (by rw [add_sub_right_comm, L.add_mem_cancel_right hl])
end CompanionTheory.PlacePermOperatorBicommutantSpan
