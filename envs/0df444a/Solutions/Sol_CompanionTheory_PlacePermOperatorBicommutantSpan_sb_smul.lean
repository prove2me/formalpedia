-- Prove2me | solution 1 for CompanionTheory.PlacePermOperatorBicommutantSpan.sb_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:05:29.888978+00:00
-- url     : https://prove2.me/submissions/a9774f19-4610-45da-a006-58bc50511494

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_IsOpenCoset
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_sb_mul

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
theorem _root_.solution (c : ℂ) {g : V → ℂ} (hg : SB g) : SB (c • g) := sb_mul (IsLocallyConstant.const c) hg
end CompanionTheory.PlacePermOperatorBicommutantSpan
