-- Prove2me | solution 1 for CompanionTheory.PlacePermOperatorBicommutantSpan.sb_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:06:03.146677+00:00
-- url     : https://prove2.me/submissions/f0a41091-5fb6-44e0-9270-3cdaf2fb1c8b

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_IsOpenCoset
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_sb_add
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_sb_zero

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
theorem _root_.solution {α : Type} (s : Finset α) {f : α → V → ℂ} (h : ∀ a ∈ s, SB (f a)) : SB (∑ a ∈ s, f a) :=
  Finset.sum_induction _ SB (fun _ _ => sb_add) sb_zero h
end CompanionTheory.PlacePermOperatorBicommutantSpan
