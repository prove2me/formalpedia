-- Prove2me | solution 1 for CompanionTheory.PlacePermOperatorBicommutantSpan.bsym
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:05:35.900878+00:00
-- url     : https://prove2.me/submissions/7e511dab-e48d-4c10-964e-270b8d9d48f0

import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_IsOpenCoset
import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_SqPosOfNe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Set Matrix
open scoped ENNReal ComplexConjugate MatrixGroups
noncomputable section
open CompanionTheory CompanionTheory.PlacePermOperatorBicommutantSpan
open GlobalTheory.CompanionTheory.SW.Core
variable {R : Type} [CommRing R] {ι : Type} [Fintype ι]
namespace CompanionTheory.PlacePermOperatorBicommutantSpan
theorem _root_.solution {B : Matrix ι ι R} (hB : B.IsSymm) (x y : ι → R) : x ⬝ᵥ (B *ᵥ y) = y ⬝ᵥ (B *ᵥ x) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hB.eq, dotProduct_comm]
end CompanionTheory.PlacePermOperatorBicommutantSpan
