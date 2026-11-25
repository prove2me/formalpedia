-- Prove2me | solution 1 for CompanionTheory.PlacePermOperatorBicommutantSpan.Tgt.c_planch
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:31:47.030916+00:00
-- url     : https://prove2.me/submissions/e9cceca7-cfee-4e94-acf0-759bc382ae3d

import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_SqPosOfNe
import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_WeilImplicationNonarchQuadratic
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_planch


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
open CompanionTheory CompanionTheory.PlacePermOperatorBicommutantSpan CompanionTheory.PlacePermOperatorBicommutantSpan.Tgt
open CompanionTheory.PlacePermOperatorBicommutantSpan
namespace CompanionTheory.PlacePermOperatorBicommutantSpan.Tgt
theorem _root_.solution : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] (χ : V → V → ℂ) (μ : Measure V), NADual V χ μ → ∀ φ : V → ℂ, SB φ → ∫ y, ‖fou χ μ φ y‖ ^ 2 ∂μ = ∫ x, ‖φ x‖ ^ 2 ∂μ :=
  fun _ _ _ _ _ _ h _ hφ => planch h hφ
end CompanionTheory.PlacePermOperatorBicommutantSpan.Tgt
