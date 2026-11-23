-- Prove2me | solution 1 for CompanionTheory.PlacePermOperatorBicommutantSpan.impl_fou_chiB
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:09:01.079474+00:00
-- url     : https://prove2.me/submissions/d847874c-636a-4897-83c0-47bc520e21d0

import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_IsOpenCoset
import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_SqPosOfNe
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_bsym
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_fou_add
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_fou_sb
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_fou_smul
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_planch
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_sb_homeo


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
theorem _root_.solution : Impl ψ h B μ wMat (fou (chiB ψ B) μ) := by
  have hD := H.2.2.2.2.2
  have hh := hD
  obtain ⟨_, _, _, _, _, _, -⟩ := hh
  refine ⟨fun φ hφ => (fou_sb hD hφ).1, fun φ hφ => ?_, fun φ φ' hφ hφ' => fou_add hD hφ hφ',
    fun c φ _ => fou_smul c φ, fun φ hφ => planch hD hφ, fun x y φ _ => ?_⟩
  · have h1 := sb_homeo hφ (Homeomorph.neg _)
    exact ⟨_, (fou_sb hD h1).1, funext fun u => by rw [(fou_sb hD h1).2]; simp⟩
  · funext u
    simp only [Heisenberg₂, fou, wMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, one_smul, zero_smul, add_zero, zero_add, neg_smul, ← integral_const_mul]
    conv_rhs => rw [← integral_add_right_eq_self _ y]
    refine integral_congr_ae (ae_of_all _ fun v => ?_)
    simp only [add_neg_cancel_right, chiB]
    rw [mul_left_comm, mul_right_comm, mul_comm _ (φ v), ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 2
    simp only [mulVec_add, add_dotProduct, dotProduct_add, neg_dotProduct, bsym H.2.2.2.2.1 y u, bsym H.2.2.2.2.1 y x]
    linear_combination (x ⬝ᵥ (B *ᵥ y)) * H.2.1
end CompanionTheory.PlacePermOperatorBicommutantSpan
