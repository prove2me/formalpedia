-- Prove2me | solution 1 for CompanionTheory.PlacePermOperatorBicommutantSpan.sq_pos_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:35:55.322154+00:00
-- url     : https://prove2.me/submissions/1ebacb28-78f8-40f4-adb8-47de8d356c8f

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
variable [TopologicalSpace R] [MeasurableSpace R] {ψ : AddChar R ℂ} {h : R} {B : Matrix ι ι R} {μ : Measure (ι → R)}
variable (H : NAQuad ψ h B μ)
include H
namespace CompanionTheory.PlacePermOperatorBicommutantSpan
theorem _root_.solution {φ : (ι → R) → ℂ} (hφ : SB φ) (hne : φ ≠ 0) : ∫ u, ‖φ u‖ ^ 2 ∂μ ≠ 0 := by
  have hh := H.2.2.2.2.2
  obtain ⟨_, _, _, _, _, _, -⟩ := hh
  intro h0
  have hc : Continuous fun u => ‖φ u‖ ^ 2 := hφ.1.continuous.norm.pow 2
  have h1 := (integral_eq_zero_iff_of_nonneg (fun u => sq_nonneg _) (hc.integrable_of_hasCompactSupport
    (hφ.2.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp)))).1 h0
  have h2 := (hc.ae_eq_iff_eq μ continuous_zero).1 h1
  exact hne (funext fun u => by simpa using congrFun h2 u)
end CompanionTheory.PlacePermOperatorBicommutantSpan
