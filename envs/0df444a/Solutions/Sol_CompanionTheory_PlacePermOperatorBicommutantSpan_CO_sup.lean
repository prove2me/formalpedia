-- Prove2me | solution 1 for CompanionTheory.PlacePermOperatorBicommutantSpan.CO.sup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:33:07.969528+00:00
-- url     : https://prove2.me/submissions/41bc782a-8aff-47c2-a2f8-f68f0df23b8d

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
variable [IsTopologicalAddGroup V]
namespace CompanionTheory.PlacePermOperatorBicommutantSpan
namespace CO
theorem _root_.solution {L L' : AddSubgroup V} (h : CO L) (h' : CO L') : CO (L ⊔ L') :=
  ⟨by rw [AddSubgroup.add_normal]; exact h.1.add h'.1, AddSubgroup.isOpen_mono le_sup_left h.2⟩
end CO
end CompanionTheory.PlacePermOperatorBicommutantSpan
