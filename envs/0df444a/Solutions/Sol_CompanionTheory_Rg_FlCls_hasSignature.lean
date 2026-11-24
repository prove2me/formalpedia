-- Prove2me | solution 1 for CompanionTheory.Rg.FlCls.hasSignature
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:27:48.257031+00:00
-- url     : https://prove2.me/submissions/f33ea4f4-e118-4251-a219-fe4db7baeb1d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AdelicCMFields_SupportedAtSplit
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_NefEffectiveCones_ExistsNsmulMulVecMemHat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsAdeleRingTensorEquivInfiniteProdFinite
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_UJClassFin
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_ArchimedeanDenseStabilizers_DenseRangeOfNotIsReal
import Theorems.Thm_CompanionTheory_Rg_FlCls_denseRange_of_not_isReal
import Theorems.Thm_CompanionTheory_Rg_FlCls_hasSignature_of_posDef
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix ComplexOrder MatrixOrder
open CompanionTheory CompanionTheory.Rg CompanionTheory.Rg.FlCls
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
namespace CompanionTheory.Rg.FlCls
theorem _root_.solution (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (hG : IsHermForm c G)
    (hc : ∀ (σ : E →+* ℂ) (x : E), σ (c x) = starRingEnd ℂ (σ x)) (τ : E →+* ℂ)
    (h : ∀ x : Fin n → E, x ≠ 0 → 0 < (τ (hermE c G x x)).re) :
    PI.UJClassFin.HasSignature (Gᵀ.map τ) n 0 := by
  refine hasSignature_of_posDef (J := Gᵀ.map τ) ?_
  have hH : (Gᵀ.map τ).IsHermitian := by
    ext i k
    simp only [Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.transpose_apply]
    rw [← hG.2.2.1 i k, hc]; rfl
  have hd : DenseRange τ := by
    refine denseRange_of_not_isReal τ fun hr => hG.2.1 ?_
    ext x
    apply τ.injective
    rw [hc]
    exact RingHom.congr_fun (ComplexEmbedding.isReal_iff.1 hr) x
  have hdn : DenseRange fun (l : Fin n → E) => (fun i => τ (l i)) :=
    DenseRange.piMap (fun _ : Fin n => hd)
  have hco : ∀ l : Fin n → E, τ (hermE c G l l) =
      star (fun i => τ (l i)) ⬝ᵥ (Gᵀ.map τ).mulVec (fun i => τ (l i)) := by
    intro l
    simp only [hermE, map_sum, map_mul, hc, dotProduct, Matrix.mulVec, Matrix.map_apply,
      Matrix.transpose_apply, Pi.star_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [starRingEnd_apply]; ring
  have hpsd : (Gᵀ.map τ).PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH fun x => ?_
    rw [Complex.nonneg_iff]
    refine ⟨?_, (hH.im_star_dotProduct_mulVec_self x).symm⟩
    refine hdn.induction_on (p := fun y => 0 ≤ (star y ⬝ᵥ ((Gᵀ.map τ) *ᵥ y)).re) x ?_ ?_
    · exact isClosed_le continuous_const (by fun_prop)
    · intro l
      by_cases hl : l = 0
      · subst hl
        simp [dotProduct]
      · have := h _ hl
        rw [hco] at this
        exact this.le
  rw [hpsd.posDef_iff_isUnit, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro h0
  apply hG.2.2.2
  apply τ.injective
  rw [← Matrix.det_transpose, RingHom.map_det, map_zero]
  exact h0
end CompanionTheory.Rg.FlCls
