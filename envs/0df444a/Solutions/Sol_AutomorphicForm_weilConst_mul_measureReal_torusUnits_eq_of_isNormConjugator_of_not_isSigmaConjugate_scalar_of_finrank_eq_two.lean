-- Prove2me | solution 1 for AutomorphicForm.weilConst_mul_measureReal_torusUnits_eq_of_isNormConjugator_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/07c5f6f3-daef-5f23-881e-fd01be8951c1

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Theorems.Thm_AutomorphicForm_det_mem_range_and_isOpen_isCompact_detUnits_twistedCentralizer_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
import Theorems.Thm_AutomorphicForm_valuation_trace_le_one_of_valuation_det_eq_one_of_mem_localCentralizer_of_forall_not_diagonal
import Theorems.Thm_AutomorphicForm_weilConst_mul_measureReal_torusUnits_eq_of_detUnits_isCompact_isOpen_of_isNormConjugator
import Theorems.Thm_AutomorphicForm_exists_mem_twistedCentralizer_valuation_eq_exp_neg_one_and_det_eq_of_isNormOf_scalar_of_finrank_eq_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_weilConst_mul_measureReal_torusUnits_eq_of_isNormConjugator_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
p2m_attr_erase "instance" "ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false

open MeasureTheory NumberField
open IsDedekindDomain
open scoped TensorProduct
open scoped TensorProduct.RightActions

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K))
    (c : (v.adicCompletion K)ˣ)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ)
    (hδq : ∀ z : (L ⊗[K] v.adicCompletion K)ˣ,
      ¬ AutomorphicForm.IsSigmaConjugate K L (v.adicCompletion K) σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z))
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ')
    (u₀ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hu₀ : u₀ ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)
    (γ₀ : GL (Fin 2) (v.adicCompletion K)) (hγ₀ : AutomorphicForm.IsRegularSemisimple γ₀)
    (hγ₀e : ∀ g : GL (Fin 2) (v.adicCompletion K),
      ¬ (((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 ∧
         ((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0))
    (y₁ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hy₁ : AutomorphicForm.IsNormConjugator K L (v.adicCompletion K) σ γ₀ (u₀ * δ) y₁)
    (hS : ∀ t : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
      t ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ⊓
          AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ) ↔
        ∃ m ∈ AutomorphicForm.localCentralizer K v γ₀,
          y₁ * AutomorphicForm.toTensorGL K L (v.adicCompletion K) m * y₁⁻¹ = t)
    (τS : @Measure ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ⊓
        AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)) (borel _))
    (hτS : @Measure.IsHaarMeasure _ _ _ (borel _) τS)
    (τT : @Measure (AutomorphicForm.localCentralizer K v γ₀) (AutomorphicForm.localCentralizerBorel K v γ₀))
    (hτT : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ₀) τT)
    (hlink : (letI := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
       letI := AutomorphicForm.localCentralizerBorel K v γ₀
       letI : MeasurableSpace ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ⊓
           AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)) := borel _
       Measure.map (fun s : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ⊓
             AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)) =>
           y₁⁻¹ * (s : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * y₁) τS =
         Measure.map (fun m : ↥(AutomorphicForm.localCentralizer K v γ₀) =>
           AutomorphicForm.toTensorGL K L (v.adicCompletion K) (m : GL (Fin 2) (v.adicCompletion K))) τT)) :
      (letI := AutomorphicForm.localGLBorel K v
       letI := AutomorphicForm.localCentralizerBorel K v γ₀
       letI := AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ
       ∀ ρ : ℝ,
        (∀ w : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ) → ℝ,
          (letI := AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ
           letI : MeasurableSpace ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ⊓
               AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)) := borel _
           (∀ t, 0 ≤ w t) ∧ Measurable w ∧ HasCompactSupport w ∧
             ∀ t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ),
               ∫ s : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ⊓
                   AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)),
                 w ((⟨(s : GL (Fin 2) (L ⊗[K] v.adicCompletion K)), (Subgroup.mem_inf.mp s.2).1⟩ :
                   ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)) * t) ∂τS = 1) →
          (letI := AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ
           ∫ t, w t ∂τ' = ρ)) →
        ((∃ t : GL (Fin 2) (v.adicCompletion K), t ∈ AutomorphicForm.localCentralizer K v γ₀ ∧
          Valued.v ((t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = Multiplicative.ofAdd (-1 : ℤ)) →
          ρ * ((Measure.map Subtype.val τT) {g : GL (Fin 2) (v.adicCompletion K) | g ∈ AutomorphicForm.localCentralizer K v γ₀ ∧
            Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = 1 ∧
            Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).trace) ≤ 1}).toReal = (τ' {t | ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 ∧
            Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
              Units.map (Algebra.TensorProduct.includeRight :
                v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s}).toReal) ∧
        ((¬ (∃ t : GL (Fin 2) (v.adicCompletion K), t ∈ AutomorphicForm.localCentralizer K v γ₀ ∧
          Valued.v ((t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = Multiplicative.ofAdd (-1 : ℤ))) →
          ρ * ((Measure.map Subtype.val τT) {g : GL (Fin 2) (v.adicCompletion K) | g ∈ AutomorphicForm.localCentralizer K v γ₀ ∧
            Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = 1 ∧
            Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).trace) ≤ 1}).toReal = 2 * (τ' {t | ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 ∧
            Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
              Units.map (Algebra.TensorProduct.includeRight :
                v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s}).toReal)) := by
  obtain ⟨hdetK, hUo, hUc⟩ := AutomorphicForm.det_mem_range_and_isOpen_isCompact_detUnits_twistedCentralizer_of_not_isSigmaConjugate_scalar_of_finrank_eq_two K L h2 σ hgen v c δ hδ hδq
  exact AutomorphicForm.weilConst_mul_measureReal_torusUnits_eq_of_detUnits_isCompact_isOpen_of_isNormConjugator K L h2 σ hgen v c δ hδ hδq τ' hτ' u₀ hu₀ γ₀ hγ₀ hγ₀e y₁ hy₁ hS τS hτS τT hτT hlink
    hdetK hUo hUc
    (AutomorphicForm.exists_mem_twistedCentralizer_valuation_eq_exp_neg_one_and_det_eq_of_isNormOf_scalar_of_finrank_eq_two K L h2 σ hgen v c δ hδ)
    (fun m hm hd => AutomorphicForm.valuation_trace_le_one_of_valuation_det_eq_one_of_mem_localCentralizer_of_forall_not_diagonal K v γ₀ hγ₀ hγ₀e m hm hd)

end S_AutomorphicForm_weilConst_mul_measureReal_torusUnits_eq_of_isNormConjugator_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
end P2MW
export P2MW.S_AutomorphicForm_weilConst_mul_measureReal_torusUnits_eq_of_isNormConjugator_of_not_isSigmaConjugate_scalar_of_finrank_eq_two (solution)
