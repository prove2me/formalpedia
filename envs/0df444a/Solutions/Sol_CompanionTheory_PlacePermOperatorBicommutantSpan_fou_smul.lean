-- Prove2me | solution 1 for CompanionTheory.PlacePermOperatorBicommutantSpan.fou_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:02:40.828825+00:00
-- url     : https://prove2.me/submissions/e4d77371-3b17-4db1-9d74-2fe2d31b6e6f

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
omit h
namespace CompanionTheory.PlacePermOperatorBicommutantSpan
theorem _root_.solution (c : ℂ) (f : V → ℂ) : fou χ μ (c • f) = c • fou χ μ f := by
  funext y
  simp only [fou, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]
end CompanionTheory.PlacePermOperatorBicommutantSpan
