-- Prove2me | solution 1 for CompanionTheory.PlacePermOperatorBicommutantSpan.sb_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:01:48.799178+00:00
-- url     : https://prove2.me/submissions/73526a2e-9dde-44c4-bf38-48b7dd9ea2f1

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
theorem _root_.solution {f g : V → ℂ} (hf : IsLocallyConstant f) (hg : SB g) : SB fun x => f x * g x :=
  ⟨hf.mul hg.1, hg.2.mul_left⟩
end CompanionTheory.PlacePermOperatorBicommutantSpan
