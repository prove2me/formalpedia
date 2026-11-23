-- Prove2me | solution 1 for CompanionTheory.PlacePermOperatorBicommutantSpan.sb_opD
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:28:28.783497+00:00
-- url     : https://prove2.me/submissions/686cb658-b868-46b2-82af-ba67160338ef

import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_IsOpenCoset
import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_SqPosOfNe
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_sb_homeo
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_sb_smul


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
variable [TopologicalSpace R] [MeasurableSpace R] {ψ : AddChar R ℂ} {h : R} {B : Matrix ι ι R} {μ : Measure (ι → R)}
variable (H : NAQuad ψ h B μ)
include H
namespace CompanionTheory.PlacePermOperatorBicommutantSpan
theorem _root_.solution (m : ℝ) (a : Rˣ) {φ : (ι → R) → ℂ} (hφ : SB φ) : SB (opD m (a : R) φ) := by
  have := H.1
  exact sb_smul (m : ℂ) (sb_homeo hφ (Homeomorph.smul a))
end CompanionTheory.PlacePermOperatorBicommutantSpan
