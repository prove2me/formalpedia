-- Prove2me | solution 1 for CompanionTheory.PlacePermOperatorBicommutantSpan.sb_homeo
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:01:48.463806+00:00
-- url     : https://prove2.me/submissions/84ae8c70-4943-4880-b932-0f8e85770b6a

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
omit [AddCommGroup V]
namespace CompanionTheory.PlacePermOperatorBicommutantSpan
theorem _root_.solution {f : V → ℂ} (hf : SB f) (e : V ≃ₜ V) : SB (f ∘ e) :=
  ⟨hf.1.comp_continuous e.continuous, hf.2.comp_homeomorph e⟩
end CompanionTheory.PlacePermOperatorBicommutantSpan
