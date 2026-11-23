-- Prove2me | solution 1 for CompanionTheory.PlacePermOperatorBicommutantSpan.CO.inf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:01:36.867705+00:00
-- url     : https://prove2.me/submissions/079c7a36-fdf3-4e2f-bde4-5179be12e727

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
theorem _root_.solution {L L' : AddSubgroup V} (h : CO L) (h' : IsOpen (L' : Set V)) : CO (L ⊓ L') :=
  ⟨h.1.inter_right (L'.isClosed_of_isOpen h'), h.2.inter h'⟩
end CO
end CompanionTheory.PlacePermOperatorBicommutantSpan
