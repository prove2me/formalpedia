-- Prove2me | solution 1 for CompanionTheory.PlacePermOperatorBicommutantSpan.chi_lc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:51:43.094636+00:00
-- url     : https://prove2.me/submissions/1dbd1ffc-16e4-441c-a764-650284ca78d2

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_IsOpenCoset
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_lc_of_inv
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_co_cpt
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_co_perp

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
theorem _root_.solution (a : V) : IsLocallyConstant fun y => χ a y := by
  have := h.1
  obtain ⟨L, hL, ha⟩ := co_cpt h (isCompact_singleton (x := a))
  exact lc_of_inv (co_perp h hL).2 fun x l hl => by rw [chi_add' h, hl a (ha rfl), mul_one]
end CompanionTheory.PlacePermOperatorBicommutantSpan
