-- Prove2me | solution 1 for CompanionTheory.PlacePermOperatorBicommutantSpan.co_perp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:01:36.831361+00:00
-- url     : https://prove2.me/submissions/bf7fd11f-6e8f-4326-8d21-b54b4761a302

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
theorem _root_.solution {L : AddSubgroup V} (hL : CO L) : CO (perpG h L) :=
  ⟨(h.2.2.2.2.2.2.2.2.2.2.2.2 L hL.1 hL.2).1, (h.2.2.2.2.2.2.2.2.2.2.2.2 L hL.1 hL.2).2.1⟩
end CompanionTheory.PlacePermOperatorBicommutantSpan
