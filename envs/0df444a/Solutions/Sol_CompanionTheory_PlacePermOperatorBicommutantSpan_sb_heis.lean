-- Prove2me | solution 1 for CompanionTheory.PlacePermOperatorBicommutantSpan.sb_heis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:57:44.083677+00:00
-- url     : https://prove2.me/submissions/4f266f1f-9694-49f6-882a-4569be3e7658

import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_IsOpenCoset
import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_SqPosOfNe
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_sb_chi
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
theorem _root_.solution (x y : ι → R) {φ : (ι → R) → ℂ} (hφ : SB φ) : SB (Heisenberg₂ ψ h B x y φ) := by
  have hD := H.2.2.2.2.2
  have := hD.1
  have e : Heisenberg₂ ψ h B x y φ =
      ψ (h * (x ⬝ᵥ (B *ᵥ y))) • fun u => (φ ∘ Homeomorph.addRight x) u * chiB ψ B u y := by
    funext u
    simp only [Heisenberg₂, chiB, AddChar.map_add_eq_mul, Pi.smul_apply, smul_eq_mul, Function.comp, Homeomorph.coe_addRight]
    ring
  exact e ▸ sb_smul _ (sb_chi hD (sb_homeo hφ _) y)
end CompanionTheory.PlacePermOperatorBicommutantSpan
