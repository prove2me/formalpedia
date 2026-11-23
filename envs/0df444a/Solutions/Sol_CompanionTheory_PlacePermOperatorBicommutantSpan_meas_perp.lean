-- Prove2me | solution 1 for CompanionTheory.PlacePermOperatorBicommutantSpan.meas_perp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:35:53.736278+00:00
-- url     : https://prove2.me/submissions/5fac604a-cb9d-4bbd-96c3-e0406a26033b

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
theorem _root_.solution {L : AddSubgroup V} (hL : CO L) : (μ L).toReal * (μ (perpG h L)).toReal = 1 := by
  rw [← ENNReal.toReal_mul]
  exact (congrArg ENNReal.toReal (h.2.2.2.2.2.2.2.2.2.2.2.2 L hL.1 hL.2).2.2.2).trans ENNReal.toReal_one
end CompanionTheory.PlacePermOperatorBicommutantSpan
