-- Prove2me | solution 1 for CuspForm.IsNewform.isIrreducibleGLRep_of_linearMap_range_eq_span_padic_smul_self
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/9a5cd714-4190-58fa-b476-0bb0ccc2a0b3

import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_LocalNewvector_PrincipalSeriesCarrier
import Definitions.Def_LocalNewvector_ReductionFunctor
import Theorems.Thm_CuspForm_IsAdelicLiftOf_ne_zero
import Theorems.Thm_CuspForm_IsNewform_hasNewvectorConductor_adelicSpan_factorization_of_isAdelicLiftOf
import Theorems.Thm_CuspForm_IsAdelicLiftOf_exists_mem_span_fixed_padicK1_of_fixedSubmodule_padicK1_ne_bot
import Theorems.Thm_AutomorphicForm_SiegelCovering_centreCutSiegelSet_coversModCentre_rat
import Theorems.Thm_CuspForm_IsNewform_exists_isGenuineCuspRealizationAt_productionPinsOf_toFun_eq_of_isAdelicLiftOf
import Theorems.Thm_AutomorphicForm_exists_isIrreducibleGLRep_injective_linearMap_adelicSpan_finsupp_of_agreesAwayFromFinite
import Theorems.Thm_LocalNewvector_exists_iSup_range_eq_top_of_injective_linearMap_finsupp_of_isIrreducibleGLRep
import Theorems.Thm_CuspForm_IsNewform_exists_smul_add_smul_eq_zero_of_mem_span_of_mem_fixedSubmodule_padicK1_of_centralGL_smul_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsNewform_isIrreducibleGLRep_of_linearMap_range_eq_span_padic_smul_self
p2m_attr_erase "instance" "FLT.SpectralSide.instCompactSpaceMatrix instCountableOfNumberField_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions RestrictedProduct.SecondCountableTopology_of_principal"
p2m_attr_erase "instance" "instCountableElemSetSetsCofinite_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2"
p2m_attr_erase "simp" "ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AutomorphicForm.IsStableLinearOn.coe_toEnd_apply AutomorphicForm.ArchRepAt.mk.sizeOf_spec AutomorphicForm.IsIsotypicCuspFormAt.toRealization_toFun AutomorphicForm.ArchTypeFamily.mk.sizeOf_spec AutomorphicForm.charRep_apply AutomorphicForm.ArchRepAt.mk.injEq AutomorphicForm.ArchTypeFamily.mk.injEq M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply AutomorphicForm.CuspidalConstituent.rightRegular_apply AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv SemialgHom.baseChange_of_algebraMap_tmul_left"
p2m_attr_erase "simp" "SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul AutomorphicForm.mem_sigmaCentralizer_iff M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply"
p2m_attr_erase "simp" "FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.iotaZsqrtdNegTwo_apply AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply"
p2m_attr_erase "simp" "Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec LanglandsTunnell.signShift_zero LanglandsTunnell.RealArchParam.twist_zero LanglandsTunnell.RealArchParam.discrete.sizeOf_spec LanglandsTunnell.RealArchParam.principal.injEq LanglandsTunnell.ComplexArchParam.dual_dual LanglandsTunnell.ComplexArchParam.mk.sizeOf_spec LanglandsTunnell.RealArchParam.dual_dual LanglandsTunnell.RealArchParam.discrete.injEq LanglandsTunnell.ComplexArchParam.twist_zero LanglandsTunnell.RealArchParam.principal.sizeOf_spec LanglandsTunnell.signShift_one LanglandsTunnell.ComplexArchParam.mk.injEq LanglandsTunnell.TateLocal.conductorExponentAt_one"
p2m_attr_erase "simp" "NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent LanglandsTunnell.signEpsilon_one LanglandsTunnell.RealArchParam.epsilonFactor_principal LanglandsTunnell.RealArchParam.epsilonFactor_discrete LanglandsTunnell.signEpsilon_zero LanglandsTunnell.LDatum.mk.sizeOf_spec LanglandsTunnell.LDatum.badFactor_zero LanglandsTunnell.LDatum.mk.injEq AutomorphicForm.rightTranslationEmbed_smul_apply FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero CuspForm.coe_traceLin_apply ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply FreyPackage.ModMCarrier.coe_levelInclusionLin FreyPackage.ModMCarrier.atkinLehnerDatumOfPrimeNotDvd_R FreyPackage.ModMCarrier.latticeRed.mk_eq_tmul CuspForm.coe_heckeULowerLin_apply"

set_option autoImplicit false

namespace NewformLocalSpanCopies

section Criterion

variable (q : ℕ) [Fact q.Prime]
  {σ : Type} [AddCommGroup σ] [Module ℂ σ] [DistribMulAction (GL (Fin 2) ℚ_[q]) σ]
  {V : Type} [AddCommGroup V] [Module ℂ V] [DistribMulAction (GL (Fin 2) ℚ_[q]) V]

private theorem smul_mem_range {e : σ →ₗ[ℂ] V} (he : ∀ (x : GL (Fin 2) ℚ_[q]) (s : σ), e (x • s) = x • e s)
    (x : GL (Fin 2) ℚ_[q]) {v : V} (hv : v ∈ LinearMap.range e) : x • v ∈ LinearMap.range e := by
  obtain ⟨s, rfl⟩ := hv
  exact ⟨x • s, he x s⟩

private theorem eq_zero_or_injective (hσ : LocalNewvector.IsIrreducibleGLRep q σ) (e : σ →ₗ[ℂ] V)
    (he : ∀ (x : GL (Fin 2) ℚ_[q]) (s : σ), e (x • s) = x • e s) : e = 0 ∨ Function.Injective e := by
  rcases hσ.2 (LinearMap.ker e) (fun x s hs => by
      rw [LinearMap.mem_ker] at hs ⊢
      rw [he, hs, smul_zero]) with h | h
  · exact Or.inr (LinearMap.ker_eq_bot.1 h)
  · exact Or.inl (LinearMap.ker_eq_top.1 h)

private theorem isIrreducibleGLRep_of_bijective (hσ : LocalNewvector.IsIrreducibleGLRep q σ) (e : σ →ₗ[ℂ] V)
    (he : ∀ (x : GL (Fin 2) ℚ_[q]) (s : σ), e (x • s) = x • e s) (hinj : Function.Injective e)
    (hsurj : Function.Surjective e) : LocalNewvector.IsIrreducibleGLRep q V := by
  obtain ⟨s₀, hs₀⟩ := hσ.1
  refine ⟨⟨e s₀, fun h => hs₀ (hinj (h.trans (map_zero e).symm))⟩, fun W hW => ?_⟩
  rcases hσ.2 (W.comap e) (fun x s hs => by
      rw [Submodule.mem_comap] at hs ⊢
      rw [he]
      exact hW x _ hs) with h | h
  · left
    rw [← Submodule.map_comap_eq_of_surjective hsurj W, h, Submodule.map_bot]
  · right
    rw [← Submodule.map_comap_eq_of_surjective hsurj W, h, Submodule.map_top, LinearMap.range_eq_top.2 hsurj]

private theorem isIrreducibleGLRep_or_exists_two [SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ σ]
    [SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ V] (hσ : LocalNewvector.IsIrreducibleGLRep q σ) (hV0 : ∃ v : V, v ≠ 0)
    (ι : Type) (L : V →ₗ[ℂ] (ι →₀ σ)) (hL : Function.Injective L)
    (hLx : ∀ (x : GL (Fin 2) ℚ_[q]) (v : V), L (x • v) = x • L v) :
    LocalNewvector.IsIrreducibleGLRep q V ∨
      ∃ e₁ e₂ : σ →ₗ[ℂ] V,
        (∀ (x : GL (Fin 2) ℚ_[q]) (s : σ), e₁ (x • s) = x • e₁ s) ∧
          (∀ (x : GL (Fin 2) ℚ_[q]) (s : σ), e₂ (x • s) = x • e₂ s) ∧
          Function.Injective e₁ ∧ Function.Injective e₂ ∧ LinearMap.range e₁ ⊓ LinearMap.range e₂ = ⊥ := by
  obtain ⟨κ, fam, hfam, hsup⟩ :=
    LocalNewvector.exists_iSup_range_eq_top_of_injective_linearMap_finsupp_of_isIrreducibleGLRep q σ V hσ ι L hL hLx
  haveI : Nontrivial V := by
    obtain ⟨v, hv⟩ := hV0
    exact nontrivial_of_ne v 0 hv

  have hex : ∃ i, fam i ≠ 0 := by
    by_contra h
    push Not at h
    have : (⨆ i : κ, LinearMap.range (fam i)) = ⊥ := by
      refine iSup_eq_bot.2 fun i => ?_
      rw [h i, LinearMap.range_zero]
    exact bot_ne_top (this.symm.trans hsup)
  obtain ⟨i₁, hi₁⟩ := hex
  have hinj₁ : Function.Injective (fam i₁) := (eq_zero_or_injective q hσ _ (hfam i₁)).resolve_left hi₁
  by_cases htop : LinearMap.range (fam i₁) = ⊤
  · exact Or.inl (isIrreducibleGLRep_of_bijective q hσ _ (hfam i₁) hinj₁ (LinearMap.range_eq_top.1 htop))
  · right

    have hex₂ : ∃ i, ¬ LinearMap.range (fam i) ≤ LinearMap.range (fam i₁) := by
      by_contra h
      push Not at h
      exact htop (top_le_iff.1 (hsup ▸ iSup_le h))
    obtain ⟨i₂, hi₂⟩ := hex₂
    have hne₂ : fam i₂ ≠ 0 := by
      rintro h
      rw [h, LinearMap.range_zero] at hi₂
      exact hi₂ bot_le
    have hinj₂ : Function.Injective (fam i₂) := (eq_zero_or_injective q hσ _ (hfam i₂)).resolve_left hne₂
    refine ⟨fam i₁, fam i₂, hfam i₁, hfam i₂, hinj₁, hinj₂, ?_⟩

    rcases hσ.2 ((LinearMap.range (fam i₁) ⊓ LinearMap.range (fam i₂)).comap (fam i₂)) (fun x s hs => by
        rw [Submodule.mem_comap, Submodule.mem_inf] at hs ⊢
        rw [hfam i₂]
        exact ⟨smul_mem_range q (hfam i₁) x hs.1, smul_mem_range q (hfam i₂) x hs.2⟩) with h | h
    · rw [eq_bot_iff]
      rintro w ⟨hw₁, hw₂⟩
      obtain ⟨s, rfl⟩ := hw₂
      have hs : s ∈ (LinearMap.range (fam i₁) ⊓ LinearMap.range (fam i₂)).comap (fam i₂) :=
        ⟨hw₁, LinearMap.mem_range_self _ s⟩
      rw [h, Submodule.mem_bot] at hs
      rw [hs, map_zero]
      exact zero_mem _
    · exact absurd (fun w ⟨s, hs⟩ => hs ▸ ((Submodule.eq_top_iff'.1 h) s).1) hi₂

end Criterion

open NumberField NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain AutomorphicForm in
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering in

private theorem exists_embedding
    {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hg : g.IsNewform)
    (q : ℕ) [Fact q.Prime]
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hΦg : g.IsAdelicLiftOf Φ) :
    ∃ (σ : Type) (_ : AddCommGroup σ) (_ : Module ℂ σ) (_ : DistribMulAction (GL (Fin 2) ℚ_[q]) σ)
      (_ : SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ σ),
      LocalNewvector.IsIrreducibleGLRep q σ ∧
      ∃ (ι : Type) (j : LocalNewvector.AdelicSpan Φ →ₗ[ℂ] (ι →₀ σ)),
        Function.Injective j ∧ ∀ (x : GL (Fin 2) ℚ_[q]) (s : LocalNewvector.AdelicSpan Φ), j (x • s) = x • j s := by

  have hc : (0 : ℝ) < 1 / 2 := by norm_num
  have hd₁ : (0 : ℝ) < 1 := by norm_num
  have hd : (1 : ℝ) < 2 := by norm_num
  have hcov₀ : CoversModCentre ℚ (centreCutSiegelSet ℚ (1 / 2) (1 / 2) 1 2) :=
    centreCutSiegelSet_coversModCentre_rat
      (by
        rw [div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)]
        exact Real.le_sqrt_of_sq_le (by norm_num))
      le_rfl (by norm_num) hd.le
  have hcov : CoversModCentre ℚ
      (⋃ x ∈ ({1} : Finset (AdelicGL2 (𝓞 ℚ) ℚ)), (· * x) '' centreCutSiegelSet ℚ (1 / 2) (1 / 2) 1 2) := by
    have hset : (⋃ x ∈ ({1} : Finset (AdelicGL2 (𝓞 ℚ) ℚ)), (· * x) '' centreCutSiegelSet ℚ (1 / 2) (1 / 2) 1 2)
        = centreCutSiegelSet ℚ (1 / 2) (1 / 2) 1 2 := by
      rw [Finset.set_biUnion_singleton]
      simp only [mul_one, Set.image_id']
    rw [hset]
    exact hcov₀

  have hI : AdelicDock.ratLevel M ≠ ⊥ := AdelicDock.ratLevel_ne_bot (NeZero.ne M)
  let S : Finset (HeightOneSpectrum (𝓞 ℚ)) := (Ideal.finite_factors hI).toFinset
  have hS : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ¬ v.asIdeal ∣ AdelicDock.ratLevel M := fun v hv hdvd =>
    hv ((Ideal.finite_factors hI).mem_toFinset.2 hdvd)

  obtain ⟨Θ, R, hR, hRΦ, -, -⟩ :=
    CuspForm.IsNewform.exists_isGenuineCuspRealizationAt_productionPinsOf_toFun_eq_of_isAdelicLiftOf (1 / 2) (1 / 2)
      1 2 {1} hc hd₁ hd hcov hg Φ hΦg S hS
  subst hRΦ

  obtain ⟨σ, i₁, i₂, i₃, i₄, hσ, ι, j₁, j₂, hj₁, -, hj₁x, -⟩ :=
    AutomorphicForm.exists_isIrreducibleGLRep_injective_linearMap_adelicSpan_finsupp_of_agreesAwayFromFinite (1 / 2)
      (1 / 2) 1 2 {1} hd hcov Θ.toRawCentral Θ.toRawCentral ⟨∅, fun v _ => ⟨rfl, rfl⟩⟩ R hR R hR q
  exact ⟨σ, i₁, i₂, i₃, i₄, hσ, ι, j₁, hj₁, hj₁x⟩

end NewformLocalSpanCopies

namespace NewformLocalSpanFixed

private theorem exists_ne_zero_mem_fixedSubmodule_padicK1_centralGL_smul_eq
    {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hg : g.IsNewform)
    (q : ℕ) [Fact q.Prime]
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hΦg : g.IsAdelicLiftOf Φ)
    (V : Type) [AddCommGroup V] [Module ℂ V] [DistribMulAction (GL (Fin 2) ℚ_[q]) V]
    [SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ V]
    [FiniteDimensional ℂ
      ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V)]
    (f : V →ₗ[ℂ] LocalNewvector.AdelicSpan Φ)
    (hf : ∀ (x : GL (Fin 2) ℚ_[q]) (v : V), f (x • v) = x • f v) (hfinj : Function.Injective f)
    (hfrange : LinearMap.range f =
      Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self Φ)) :
    ∃ v : V, v ≠ 0 ∧
      v ∈ LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 q (M.factorization q)) V ∧
      ∀ z : ℚ_[q]ˣ, LocalNewvector.centralGL q z • v = v := by
  have hΦ0 : Φ ≠ 0 := hΦg.ne_zero hg.ne_zero
  have hfixne := (hg.hasNewvectorConductor_adelicSpan_factorization_of_isAdelicLiftOf Φ hΦ0 hΦg q).1
  obtain ⟨y, hy, hy₀, hyfix, hycent⟩ :=
    hΦg.exists_mem_span_fixed_padicK1_of_fixedSubmodule_padicK1_ne_bot q (M.factorization q) hfixne
  rw [← hfrange] at hy
  obtain ⟨v, rfl⟩ := LinearMap.mem_range.1 hy
  refine ⟨v, ?_, ?_, ?_⟩
  · rintro rfl
    exact hy₀ (map_zero f)
  · intro k hk
    apply hfinj
    rw [hf, (LocalNewvector.mem_fixedSubmodule_iff.1 hyfix) k hk]
  · intro z
    apply hfinj
    rw [hf, hycent z]

end NewformLocalSpanFixed

private theorem no_two_copies
    {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hg : g.IsNewform)
    (q : ℕ) [Fact q.Prime]
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hΦg : g.IsAdelicLiftOf Φ)
    (V : Type) [AddCommGroup V] [Module ℂ V] [DistribMulAction (GL (Fin 2) ℚ_[q]) V]
    [SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ V]
    [FiniteDimensional ℂ
      ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V)]
    (f : V →ₗ[ℂ] LocalNewvector.AdelicSpan Φ)
    (hf : ∀ (x : GL (Fin 2) ℚ_[q]) (v : V), f (x • v) = x • f v) (hfinj : Function.Injective f)
    (hfrange : LinearMap.range f =
      Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self Φ))
    (σ : Type) [AddCommGroup σ] [Module ℂ σ] [DistribMulAction (GL (Fin 2) ℚ_[q]) σ]
    [SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ σ]
    (ι : Type) (L : V →ₗ[ℂ] (ι →₀ σ)) (hL : Function.Injective L)
    (hLx : ∀ (x : GL (Fin 2) ℚ_[q]) (v : V), L (x • v) = x • L v)
    (e₁ e₂ : σ →ₗ[ℂ] V)
    (he₁ : ∀ (x : GL (Fin 2) ℚ_[q]) (s : σ), e₁ (x • s) = x • e₁ s)
    (he₂ : ∀ (x : GL (Fin 2) ℚ_[q]) (s : σ), e₂ (x • s) = x • e₂ s)
    (h₁ : Function.Injective e₁) (h₂ : Function.Injective e₂)
    (hdis : LinearMap.range e₁ ⊓ LinearMap.range e₂ = ⊥) : False := by

  obtain ⟨v, hv0, hvK, hvZ⟩ :=
    NewformLocalSpanFixed.exists_ne_zero_mem_fixedSubmodule_padicK1_centralGL_smul_eq hg q Φ hΦg V f hf hfinj hfrange
  have hLv : L v ≠ 0 := fun h => hv0 (hL (h.trans (map_zero L).symm))
  obtain ⟨i, hi⟩ : ∃ i, L v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hLv (Finsupp.ext h)
  set s : σ := L v i with hs
  have hsx : ∀ x : GL (Fin 2) ℚ_[q], x • v = v → x • s = s := fun x hx => by
    rw [hs, ← Finsupp.smul_apply, ← hLx, hx]
  have hsK : ∀ k ∈ LocalNewvector.padicK1 q (M.factorization q), k • s = s := fun k hk =>
    hsx k ((LocalNewvector.mem_fixedSubmodule_iff.1 hvK) k hk)
  have hsZ : ∀ z : ℚ_[q]ˣ, LocalNewvector.centralGL q z • s = s := fun z => hsx _ (hvZ z)

  have hmem : ∀ w : V, f w ∈
      Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self Φ) := fun w => by
    rw [← hfrange]
    exact LinearMap.mem_range_self f w
  have hfix : ∀ (e : σ →ₗ[ℂ] V), (∀ (x : GL (Fin 2) ℚ_[q]) (s : σ), e (x • s) = x • e s) →
      f (e s) ∈ LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 q (M.factorization q))
        (LocalNewvector.AdelicSpan Φ) := fun e he => by
    rw [LocalNewvector.mem_fixedSubmodule_iff]
    intro k hk
    rw [← hf, ← he, hsK k hk]
  have hcent : ∀ (e : σ →ₗ[ℂ] V), (∀ (x : GL (Fin 2) ℚ_[q]) (s : σ), e (x • s) = x • e s) →
      ∀ z : ℚ_[q]ˣ, LocalNewvector.centralGL q z • f (e s) = f (e s) :=
    fun e he z => by rw [← hf, ← he, hsZ z]
  obtain ⟨a, b, hab, hlin⟩ :=
    hg.exists_smul_add_smul_eq_zero_of_mem_span_of_mem_fixedSubmodule_padicK1_of_centralGL_smul_eq q Φ hΦg
      (f (e₁ s)) (f (e₂ s)) (hmem _) (hmem _) (hfix e₁ he₁) (hfix e₂ he₂) (hcent e₁ he₁) (hcent e₂ he₂)

  have hV : a • e₁ s + b • e₂ s = 0 := hfinj (by rw [map_add, map_smul, map_smul, hlin, map_zero])
  have hmem₁ : a • e₁ s ∈ LinearMap.range e₁ ⊓ LinearMap.range e₂ := by
    refine ⟨⟨a • s, by rw [map_smul]⟩, ⟨-(b • s), ?_⟩⟩
    rw [map_neg, map_smul, eq_neg_iff_add_eq_zero.2 hV]
  rw [hdis, Submodule.mem_bot] at hmem₁
  have hs0 : s ≠ 0 := hi
  have ha : a = 0 := by
    rcases smul_eq_zero.1 hmem₁ with h | h
    · exact h
    · exact absurd (h₁ (h.trans (map_zero e₁).symm)) hs0
  have hb : b = 0 := by
    rw [ha, zero_smul, zero_add] at hV
    rcases smul_eq_zero.1 hV with h | h
    · exact h
    · exact absurd (h₂ (h.trans (map_zero e₂).symm)) hs0
  exact hab.elim (fun h => h ha) (fun h => h hb)

theorem solution
    {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hg : g.IsNewform)
    (q : ℕ) [Fact q.Prime]
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hΦg : g.IsAdelicLiftOf Φ)
    (hps : ∀ (μ₁ μ₂ : ℚ_[q]ˣ →* ℂˣ)
      (f : LocalNewvector.AdelicSpan Φ →ₗ[ℂ] LocalNewvector.PSCarrier q μ₁ μ₂),
      (∀ (x : GL (Fin 2) ℚ_[q]) (v : LocalNewvector.AdelicSpan Φ), f (x • v) = x • f v) → f = 0)
    (V : Type) [AddCommGroup V] [Module ℂ V] [DistribMulAction (GL (Fin 2) ℚ_[q]) V]
    [SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ V]
    [FiniteDimensional ℂ
      ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V)]
    (f : V →ₗ[ℂ] LocalNewvector.AdelicSpan Φ)
    (hf : ∀ (x : GL (Fin 2) ℚ_[q]) (v : V), f (x • v) = x • f v) (hfinj : Function.Injective f)
    (hfrange : LinearMap.range f =
      Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self Φ)) :
    LocalNewvector.IsIrreducibleGLRep q V := by
  have _ := hps

  have hΦ0 : Φ ≠ 0 := CuspForm.IsAdelicLiftOf.ne_zero hΦg hg.ne_zero
  have hV0 : ∃ v : V, v ≠ 0 := by
    have hmem : LocalNewvector.AdelicSpan.self Φ ∈ LinearMap.range f := by
      rw [hfrange]
      exact Submodule.subset_span ⟨1, one_smul _ _⟩
    obtain ⟨v, hv⟩ := hmem
    refine ⟨v, fun h => LocalNewvector.AdelicSpan.self_ne_zero_of_ne_zero Φ hΦ0 ?_⟩
    rw [← hv, h, map_zero]
  obtain ⟨σ, _, _, _, _, hσ, ι, j, hj, hjx⟩ := NewformLocalSpanCopies.exists_embedding hg q Φ hΦg
  rcases NewformLocalSpanCopies.isIrreducibleGLRep_or_exists_two q hσ hV0 ι (j ∘ₗ f) (hj.comp hfinj)
      (fun x v => by rw [LinearMap.comp_apply, LinearMap.comp_apply, hf, hjx]) with
    h | ⟨e₁, e₂, he₁, he₂, h₁, h₂, hdis⟩
  · exact h
  · exact (no_two_copies hg q Φ hΦg V f hf hfinj hfrange σ ι (j ∘ₗ f) (hj.comp hfinj)
      (fun x v => by rw [LinearMap.comp_apply, LinearMap.comp_apply, hf, hjx]) e₁ e₂ he₁ he₂ h₁ h₂ hdis).elim

end S_CuspForm_IsNewform_isIrreducibleGLRep_of_linearMap_range_eq_span_padic_smul_self
end P2MW
export P2MW.S_CuspForm_IsNewform_isIrreducibleGLRep_of_linearMap_range_eq_span_padic_smul_self (solution)
