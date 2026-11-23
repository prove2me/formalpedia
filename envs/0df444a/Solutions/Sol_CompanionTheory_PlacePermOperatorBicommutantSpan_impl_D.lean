-- Prove2me | solution 1 for CompanionTheory.PlacePermOperatorBicommutantSpan.impl_D
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:32:09.695175+00:00
-- url     : https://prove2.me/submissions/47c6d8d4-2ba2-4331-a081-61ccc33a01aa

import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_IsOpenCoset
import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_SqPosOfNe
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_sb_opD

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
theorem _root_.solution (a : Rˣ) {m : ℝ} (hm : 0 < m)
    (hμ : ∀ s : Set (ι → R), MeasurableSet s → μ ((fun u => (a : R) • u) '' s) = ENNReal.ofReal (m ^ 2) * μ s) :
    Impl ψ h B μ (mMat a) (opD m (a : R)) := by
  have := H.1
  have := H.2.2.2.2.2.2.2.2.2.1
  refine ⟨fun φ hφ => sb_opD H m a hφ, fun φ hφ => ⟨_, sb_opD H m⁻¹ a⁻¹ hφ, ?_⟩, fun φ φ' _ _ => ?_, fun c φ _ => ?_,
    fun φ _ => ?_, fun x y φ _ => ?_⟩
  · funext u
    have : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    simp [opD, smul_smul, this]
  · funext u; simp only [opD, Pi.add_apply, mul_add]
  · funext u; simp only [opD, Pi.smul_apply, smul_eq_mul]; ring
  · let e : (ι → R) ≃ᵐ (ι → R) := (Homeomorph.smul a).toMeasurableEquiv
    have he : μ = ENNReal.ofReal (m ^ 2) • μ.map e := by
      ext s hs
      rw [Measure.smul_apply, e.map_apply, smul_eq_mul, ← hμ _ (e.measurable hs)]
      exact congrArg μ (e.surjective.image_preimage s).symm
    conv_rhs => rw [he]
    rw [integral_smul_measure, integral_map_equiv, ENNReal.toReal_ofReal (sq_nonneg m), smul_eq_mul,
      ← integral_const_mul]
    simp only [opD, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rfl
  · funext u
    simp only [Heisenberg₂, opD, mMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, zero_smul, add_zero, zero_add, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_add,
      smul_eq_mul, Units.mul_inv_cancel_left, Units.inv_mul_cancel_left]
    ring
end CompanionTheory.PlacePermOperatorBicommutantSpan
