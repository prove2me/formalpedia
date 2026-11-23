-- Prove2me | solution 1 for CompanionTheory.PlacePermOperatorBicommutantSpan.chi_cont
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:33:17.912027+00:00
-- url     : https://prove2.me/submissions/c37d717f-0fd6-46ee-b9ee-09adaa2c25a6

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
variable [MeasurableSpace V] {χ : V → V → ℂ} {μ : Measure V}
variable (h : NADual V χ μ)
include h
namespace CompanionTheory.PlacePermOperatorBicommutantSpan
theorem _root_.solution : Continuous fun p : V × V => χ p.1 p.2 := h.2.2.2.2.2.2.2.2.1
end CompanionTheory.PlacePermOperatorBicommutantSpan
