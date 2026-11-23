-- Prove2me | solution 1 for CompanionTheory.PlacePermOperatorBicommutantSpan.impl_U
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:56:03.003811+00:00
-- url     : https://prove2.me/submissions/429f0ac7-6cc4-420c-aa16-dc5a99509d81

import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_IsOpenCoset
import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_SqPosOfNe
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_bsym
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_sb_opU

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
theorem _root_.solution (b : R) : Impl ψ h B μ (nMat b) (opU ψ h B b) := by
  refine ⟨fun φ hφ => sb_opU H b hφ, fun φ hφ => ⟨_, sb_opU H (-b) hφ, ?_⟩, fun φ φ' _ _ => ?_, fun c φ _ => ?_,
    fun φ _ => ?_, fun x y φ _ => ?_⟩
  · funext u; simp only [opU, ← mul_assoc, ← AddChar.map_add_eq_mul]; simp
  · funext u; simp only [opU, Pi.add_apply, mul_add]
  · funext u; simp only [opU, Pi.smul_apply, smul_eq_mul]; ring
  · simp only [opU, norm_mul, H.2.2.2.1, one_mul]
  · funext u
    simp only [Heisenberg₂, opU, ← mul_assoc, ← AddChar.map_add_eq_mul, nMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, one_smul, zero_smul, add_zero]
    congr 2
    simp only [qf, mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add, dotProduct_smul, smul_eq_mul,
      bsym H.2.2.2.2.1 x u]
    linear_combination (b * (u ⬝ᵥ (B *ᵥ x))) * H.2.1
end CompanionTheory.PlacePermOperatorBicommutantSpan
