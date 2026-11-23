-- Prove2me | solution 1 for CompanionTheory.PlacePermOperatorBicommutantSpan.sb_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:02:41.839921+00:00
-- url     : https://prove2.me/submissions/ee02b4ba-d0c4-46ae-84dd-23d15971a1b6

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
theorem _root_.solution {φ : V → ℂ} (hφ : SB φ) : Integrable φ μ := by
  obtain ⟨_, _, _, _, _, _, -⟩ := h
  exact hφ.1.continuous.integrable_of_hasCompactSupport hφ.2
end CompanionTheory.PlacePermOperatorBicommutantSpan
