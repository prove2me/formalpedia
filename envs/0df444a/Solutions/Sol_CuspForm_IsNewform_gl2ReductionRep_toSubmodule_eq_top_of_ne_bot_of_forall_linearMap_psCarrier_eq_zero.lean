-- Prove2me | solution 1 for CuspForm.IsNewform.gl2ReductionRep_toSubmodule_eq_top_of_ne_bot_of_forall_linearMap_psCarrier_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/7931c1ec-0abe-5bf7-ace3-9cd61a36cec3

import Mathlib
import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_LocalNewvector_PrincipalSeriesCarrier
import Definitions.Def_LocalNewvector_ReductionFunctor
import Definitions.Def_LocalNewvector_ConductorDatum
import Definitions.Def_CuspidalType_IsCuspidalOfType
import Theorems.Thm_CuspForm_IsNewform_gl2ReductionRep_unipotent_fixed_eq_zero_of_forall_linearMap_psCarrier_eq_zero
import Theorems.Thm_CuspidalType_exists_isCuspidalOfType_of_irreducible_of_cuspidal_of_central
import Theorems.Thm_CuspForm_IsAdelicLiftOf_gl2ReductionRep_scalarElem_eq_id_of_linearMap_range_eq_span
import Theorems.Thm_LocalNewvector_isCuspidalOfType_gl2ReductionRep_of_isIrreducibleGLRep_of_injective_of_isCuspidalOfType
import Theorems.Thm_CuspidalType_IsCuspidalOfType_toSubmodule_eq_top_of_ne_bot
import Theorems.Thm_CuspForm_IsNewform_isIrreducibleGLRep_of_linearMap_range_eq_span_padic_smul_self
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsNewform_gl2ReductionRep_toSubmodule_eq_top_of_ne_bot_of_forall_linearMap_psCarrier_eq_zero
p2m_attr_erase "instance" "FLT.SpectralSide.instCompactSpaceMatrix instCountableOfNumberField_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions RestrictedProduct.SecondCountableTopology_of_principal"
p2m_attr_erase "instance" "instCountableElemSetSetsCofinite_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2"
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv AutomorphicForm.CuspidalConstituent.rightRegular_apply AutomorphicForm.IsStableLinearOn.coe_toEnd_apply AutomorphicForm.ArchRepAt.mk.sizeOf_spec AutomorphicForm.IsIsotypicCuspFormAt.toRealization_toFun AutomorphicForm.ArchTypeFamily.mk.sizeOf_spec AutomorphicForm.charRep_apply AutomorphicForm.ArchRepAt.mk.injEq AutomorphicForm.ArchTypeFamily.mk.injEq AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.ratArchLine_apply"
p2m_attr_erase "simp" "NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul"
p2m_attr_erase "simp" "TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul AutomorphicForm.mem_sigmaCentralizer_iff M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.iotaZsqrtdNegTwo_apply AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply"
p2m_attr_erase "simp" "Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec LanglandsTunnell.signShift_zero LanglandsTunnell.RealArchParam.twist_zero LanglandsTunnell.RealArchParam.discrete.sizeOf_spec LanglandsTunnell.RealArchParam.principal.injEq LanglandsTunnell.ComplexArchParam.dual_dual"
p2m_attr_erase "simp" "LanglandsTunnell.ComplexArchParam.mk.sizeOf_spec LanglandsTunnell.RealArchParam.dual_dual LanglandsTunnell.RealArchParam.discrete.injEq LanglandsTunnell.ComplexArchParam.twist_zero LanglandsTunnell.RealArchParam.principal.sizeOf_spec LanglandsTunnell.signShift_one LanglandsTunnell.ComplexArchParam.mk.injEq LanglandsTunnell.TateLocal.conductorExponentAt_one NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent LanglandsTunnell.signEpsilon_one LanglandsTunnell.RealArchParam.epsilonFactor_principal LanglandsTunnell.RealArchParam.epsilonFactor_discrete LanglandsTunnell.signEpsilon_zero LanglandsTunnell.LDatum.mk.sizeOf_spec LanglandsTunnell.LDatum.badFactor_zero LanglandsTunnell.LDatum.mk.injEq AutomorphicForm.rightTranslationEmbed_smul_apply FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero CuspForm.coe_traceLin_apply ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply FreyPackage.ModMCarrier.coe_levelInclusionLin FreyPackage.ModMCarrier.atkinLehnerDatumOfPrimeNotDvd_R FreyPackage.ModMCarrier.latticeRed.mk_eq_tmul CuspForm.coe_heckeULowerLin_apply"

set_option autoImplicit false

namespace Ws37
namespace S3

open CuspidalType

theorem exists_irreducible_subrepresentation {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [Nontrivial V] (ρ : Representation k G V) :
    ∃ W : Subrepresentation ρ, W.toSubmodule ≠ ⊥ ∧
      ∀ W' : Subrepresentation W.toRepresentation, W'.toSubmodule ≠ ⊥ → W'.toSubmodule = ⊤ := by
  classical
  have hne : ∃ n, ∃ W : Subrepresentation ρ, W.toSubmodule ≠ ⊥ ∧ Module.finrank k W.toSubmodule = n :=
    ⟨_, ⊤, by
      have h__ := (Submodule.ne_bot_iff (⊤ : Submodule k V)).2 (by
        obtain ⟨v, hv⟩ := exists_ne (0 : V); exact ⟨v, Submodule.mem_top, hv⟩)
      first | simpa using h__ | (simp at h__; exact h__) | exact h__, rfl⟩
  obtain ⟨W, hW, hWn⟩ := Nat.find_spec hne
  refine ⟨W, hW, fun W' hW' => ?_⟩

  let W'' : Subrepresentation ρ :=
    ⟨W'.toSubmodule.map W.toSubmodule.subtype, by
      rintro g v ⟨w, hw, rfl⟩
      exact ⟨W.toRepresentation g w, W'.apply_mem_toSubmodule g hw, rfl⟩⟩
  have hW''ne : W''.toSubmodule ≠ ⊥ := by
    intro h
    apply hW'
    rw [eq_bot_iff]
    intro w hw
    have hmem : (w : V) ∈ W''.toSubmodule := ⟨w, hw, rfl⟩
    rw [h, Submodule.mem_bot, ZeroMemClass.coe_eq_zero] at hmem
    rw [Submodule.mem_bot, hmem]
  have hmin : Nat.find hne ≤ Module.finrank k W''.toSubmodule := Nat.find_min' hne ⟨W'', hW''ne, rfl⟩
  have heq : Module.finrank k W''.toSubmodule = Module.finrank k W'.toSubmodule :=
    LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ W.toSubmodule.injective_subtype _).symm
  apply Submodule.eq_top_of_finrank_eq
  have hle : Module.finrank k W'.toSubmodule ≤ Module.finrank k W.toSubmodule := Submodule.finrank_le _
  omega

theorem Subrepresentation.toRepresentation_apply_coe {k G V : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V]
    [Module k V] {ρ : Representation k G V} (W : Subrepresentation ρ) (g : G) (w : W.toSubmodule) :
    ((W.toRepresentation g w : W.toSubmodule) : V) = ρ g w := rfl

theorem cuspidal_toRepresentation {q : ℕ} [Fact q.Prime] {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k (GL2 q) V)
    (hcusp : ∀ v : V, (∀ t : ZMod q, ρ (unipotent q t) v = v) → v = 0) (W : Subrepresentation ρ) :
    ∀ w : W.toSubmodule, (∀ t : ZMod q, W.toRepresentation (unipotent q t) w = w) → w = 0 := by
  intro w hw
  apply Subtype.ext
  exact hcusp w fun t => by rw [← Subrepresentation.toRepresentation_apply_coe W, hw t]

theorem central_toRepresentation {q : ℕ} [Fact q.Prime] {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k (GL2 q) V)
    (hcent : ∀ c : (ZMod q)ˣ, ρ (scalarElem q c) = LinearMap.id) (W : Subrepresentation ρ) :
    ∀ c : (ZMod q)ˣ, W.toRepresentation (scalarElem q c) = LinearMap.id := by
  intro c
  ext w
  rw [Subrepresentation.toRepresentation_apply_coe, hcent c, LinearMap.id_apply, LinearMap.id_apply]

theorem nontrivial_of_ne_bot {k V : Type*} [Semiring k] [AddCommGroup V] [Module k V] {S : Submodule k V} (h : S ≠ ⊥) :
    Nontrivial S := Submodule.nontrivial_iff_ne_bot.2 h

theorem exists_subrepresentation_isCuspidalOfType {q : ℕ} [Fact q.Prime] {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [Nontrivial V] (ρ : Representation ℂ (GL2 q) V)
    (hcusp : ∀ v : V, (∀ t : ZMod q, ρ (unipotent q t) v = v) → v = 0)
    (hcent : ∀ c : (ZMod q)ˣ, ρ (scalarElem q c) = LinearMap.id) :
    ∃ (W : Subrepresentation ρ) (θ : (GaloisField q 2)ˣ →* ℂˣ), IsCuspidalOfType θ W.toRepresentation := by
  obtain ⟨W, hWne, hirrW⟩ := exists_irreducible_subrepresentation ρ
  haveI : Nontrivial ↥W.toSubmodule := nontrivial_of_ne_bot hWne
  obtain ⟨θ, hθ⟩ := CuspidalType.exists_isCuspidalOfType_of_irreducible_of_cuspidal_of_central
    W.toRepresentation hirrW (cuspidal_toRepresentation ρ hcusp W) (central_toRepresentation ρ hcent W)
  exact ⟨W, θ, hθ⟩

end Ws37.S3

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
    ∀ W : Subrepresentation (LocalNewvector.gl2ReductionRep q V), W.toSubmodule ≠ ⊥ → W.toSubmodule = ⊤ := by
  intro W hW
  classical
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : q.Prime).ne_zero
  have hq1 : (q : ℂ) - 1 ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast (Fact.out : q.Prime).one_lt.ne'

  have hcusp : ∀ v : ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V),
      (∀ t : ZMod q, LocalNewvector.gl2ReductionRep q V (CuspidalType.unipotent q t) v = v) → v = 0 := fun v hv =>
    CuspForm.IsNewform.gl2ReductionRep_unipotent_fixed_eq_zero_of_forall_linearMap_psCarrier_eq_zero
      g hg q Φ hΦg hps V f hf hfinj hfrange v hv
  have hcent : ∀ c : (ZMod q)ˣ, LocalNewvector.gl2ReductionRep q V (CuspidalType.scalarElem q c) = LinearMap.id :=
    fun c => CuspForm.IsAdelicLiftOf.gl2ReductionRep_scalarElem_eq_id_of_linearMap_range_eq_span g q Φ hΦg
      V f hf hfinj hfrange c

  haveI : Nontrivial ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V) := by
    obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).1 hW
    exact ⟨⟨w, 0, fun h => hw0 h⟩⟩

  obtain ⟨W₁, θ, hθ⟩ := Ws37.S3.exists_subrepresentation_isCuspidalOfType (LocalNewvector.gl2ReductionRep q V) hcusp hcent

  have hV : LocalNewvector.IsIrreducibleGLRep q V :=
    CuspForm.IsNewform.isIrreducibleGLRep_of_linearMap_range_eq_span_padic_smul_self hg q Φ hΦg hps V f hf hfinj hfrange
  have hall : CuspidalType.IsCuspidalOfType θ (LocalNewvector.gl2ReductionRep q V) :=
    LocalNewvector.isCuspidalOfType_gl2ReductionRep_of_isIrreducibleGLRep_of_injective_of_isCuspidalOfType q V hV θ hθ
      W₁.toSubmodule.subtype (fun _ _ => rfl) W₁.toSubmodule.injective_subtype

  exact hall.toSubmodule_eq_top_of_ne_bot hq0 hq1 W hW

end S_CuspForm_IsNewform_gl2ReductionRep_toSubmodule_eq_top_of_ne_bot_of_forall_linearMap_psCarrier_eq_zero
end P2MW
export P2MW.S_CuspForm_IsNewform_gl2ReductionRep_toSubmodule_eq_top_of_ne_bot_of_forall_linearMap_psCarrier_eq_zero (solution)
