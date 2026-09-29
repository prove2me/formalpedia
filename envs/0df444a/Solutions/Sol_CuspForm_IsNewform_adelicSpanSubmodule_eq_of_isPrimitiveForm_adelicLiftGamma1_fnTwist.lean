-- Prove2me | solution 1 for CuspForm.IsNewform.adelicSpanSubmodule_eq_of_isPrimitiveForm_adelicLiftGamma1_fnTwist
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/b7e42d97-2e28-50f9-b992-feeebf0ff487

import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_CuspForm_AdelicLiftGamma1
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_AutomorphicForm_FnTwist
import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_AutomorphicForm_SiegelCovering
import Theorems.Thm_CuspForm_IsEigenformWith_isIsotypicCuspFormAt_of_isAdelicLiftOfGamma1
import Theorems.Thm_CuspForm_IsNormalizedEigenform_isIsotypicCuspFormAt_one_of_isAdelicLiftOf
import Theorems.Thm_CuspForm_HasNebentypus_exists_isFiniteOrderHeckeChar_centralScalar_mul_of_isAdelicLiftOfGamma1
import Theorems.Thm_CuspForm_IsAdelicLiftOfGamma1_hasArchType0_archWeightCharFamily_two
import Theorems.Thm_CuspForm_IsAdelicLiftOf_hasArchType0_archWeightCharFamily_two
import Theorems.Thm_AutomorphicForm_hasArchType0_fnTwist
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_cuspConstituentMeets_span_image_fnTwist_of_isIsotypicCuspFormAt_of_isBoundedGenuineFn_of_forall_not_dvd
import Theorems.Thm_AutomorphicForm_IsIsotypicCuspFormAt_of_le_of_subset
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_mem_span_rightTranslate_finiteAdelic_of_isCuspConstituent_of_finiteDimensional_of_mem_levelInvariantSubmodule_of_mem_archCutSubmodule_ofChar_of_pos
import Theorems.Thm_CuspForm_IsAdelicLiftOf_isBoundedGenuineFn_productionPinsGeneral_stdAddChar
import Theorems.Thm_AutomorphicForm_eq_of_isCuspConstituent_of_cuspConstituentMeets_of_coversModCentre
import Theorems.Thm_AutomorphicForm_isotypicCuspSubmodule_inf_archCutSubmodule_le_iSup_isCuspConstituent
import Theorems.Thm_AutomorphicForm_SiegelCovering_centreCutSiegelSet_coversModCentre_rat
import Theorems.Thm_HeckeCharacter_eq_of_forall_apply_localUnit_uniformizerUnit_eq
import Theorems.Thm_CuspForm_IsAdelicLiftOf_ne_zero
import Theorems.Thm_AutomorphicForm_finiteDimensional_inf_levelInvariantSubmodule_inf_archCutSubmodule_of_isCuspConstituent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsNewform_adelicSpanSubmodule_eq_of_isPrimitiveForm_adelicLiftGamma1_fnTwist
p2m_attr_erase "instance" "instCountableOfNumberField_definitions AutomorphicForm.GaussTwist.instFiniteLocalGaussFactorValHeightOneSpectrumRingOfIntegersMemFinsetModulusPrimes AutomorphicForm.GaussTwist.instFintypeGaussIndex AutomorphicForm.GaussTwist.instCommGroupGaussIndex RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar"
p2m_attr_erase "instance" "AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply"
p2m_attr_erase "simp" "Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply"
p2m_attr_erase "simp" "IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.mem_sigmaCentralizer_iff M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec"
p2m_attr_erase "simp" "FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec LanglandsTunnell.signShift_zero LanglandsTunnell.RealArchParam.twist_zero LanglandsTunnell.RealArchParam.discrete.sizeOf_spec LanglandsTunnell.RealArchParam.principal.injEq LanglandsTunnell.ComplexArchParam.dual_dual LanglandsTunnell.ComplexArchParam.mk.sizeOf_spec LanglandsTunnell.RealArchParam.dual_dual LanglandsTunnell.RealArchParam.discrete.injEq LanglandsTunnell.ComplexArchParam.twist_zero LanglandsTunnell.RealArchParam.principal.sizeOf_spec LanglandsTunnell.signShift_one LanglandsTunnell.ComplexArchParam.mk.injEq AutomorphicForm.iotaZsqrtdNegTwo_apply"

set_option autoImplicit false
open MeasureTheory NumberField IsDedekindDomain
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent

noncomputable section

namespace B4Reduce

abbrev P : CarrierPins ℚ := productionPinsGeneral ℚ

abbrev tys₂ : ArchTypeFamily ℚ := ArchTypeFamily.ofChar ℚ (archWeightCharFamily ℚ 2)

theorem hcov : CoversModCentre ℚ (⋃ x ∈ classRepTranslates ℚ, (· * x) '' centreCutSiegelSet ℚ (1/2 : ℝ) 1 (1/2) 2) := by
  refine CoversModCentre.mono ?_ (AutomorphicForm.SiegelCovering.centreCutSiegelSet_coversModCentre_rat (c := (1/2 : ℝ)) (u := 1) (d₁ := (1/2 : ℝ)) (d₂ := 2)
    (by
      have h3 : (1 : ℝ) ≤ Real.sqrt 3 := by
        have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 3 by norm_num)
        rwa [Real.sqrt_one] at h
      linarith)
    (by norm_num) (by norm_num) (by norm_num))
  intro g hg
  refine Set.mem_iUnion₂.2 ⟨1, one_mem_classRepTranslates ℚ, ?_⟩
  exact ⟨g, hg, mul_one g⟩

section ArchG1
open NumberField IsDedekindDomain AutomorphicForm NumberField.AdelicLevel Matrix
open scoped MatrixGroups ModularForm UpperHalfPlane

section Arch

open NumberField IsDedekindDomain AutomorphicForm NumberField.AdelicLevel Matrix
open scoped MatrixGroups ModularForm UpperHalfPlane

private theorem isReal_rat_infinitePlace (v : InfinitePlace ℚ) : v.IsReal := IsTotallyReal.isReal v

private def ratArchHom : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) →* GL (Fin 2) ℝ :=
  (GeneralLinearGroup.map
    (InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace default)).toRingHom).comp
    ((archComponent ℚ default).comp (glArch (𝓞 ℚ) ℚ))

private theorem ratArchHom_apply (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    ratArchHom g = LanglandsTunnell.ratArchGL2 g := rfl

private theorem ratArch_mul (g g' : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    LanglandsTunnell.ratArchGL2 (g * g') = LanglandsTunnell.ratArchGL2 g * LanglandsTunnell.ratArchGL2 g' := by
  rw [← ratArchHom_apply, ← ratArchHom_apply, ← ratArchHom_apply, map_mul]

private theorem ratArch_eq_one_of_glArch_eq_one {u : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)} (hu : glArch (𝓞 ℚ) ℚ u = 1) :
    LanglandsTunnell.ratArchGL2 u = 1 := by
  unfold LanglandsTunnell.ratArchGL2
  rw [hu, map_one, map_one]

private theorem ratArch_finEmbed (u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    LanglandsTunnell.ratArchGL2 (AdelicDock.finEmbed (𝓞 ℚ) ℚ u) = 1 :=
  ratArch_eq_one_of_glArch_eq_one (AdelicDock.glArch_finEmbed (𝓞 ℚ) ℚ u)

private theorem ratArch_globalPoints (γ : GL (Fin 2) ℚ) :
    LanglandsTunnell.ratArchGL2 (globalPoints (𝓞 ℚ) ℚ γ) = GeneralLinearGroup.map (Rat.castHom ℝ) γ := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change ((InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace default)).toRingHom.comp
      ((archEval ℚ default).comp ((adeleArch (𝓞 ℚ) ℚ).comp (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)))))
      ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j) = (Rat.castHom ℝ) ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j)
  rw [eq_ratCast, eq_ratCast]

private theorem dense_ratPoints :
    Dense (((↑) : ℍ → ℂ) ⁻¹' {w : ℂ | w.re ∈ Set.range ((↑) : ℚ → ℝ) ∧ w.im ∈ Set.range ((↑) : ℚ → ℝ)}) := by
  have h1 : Dense (Set.range ((↑) : ℚ → ℝ) ×ˢ Set.range ((↑) : ℚ → ℝ)) :=
    Rat.denseRange_cast.prod Rat.denseRange_cast
  have h2 : {w : ℂ | w.re ∈ Set.range ((↑) : ℚ → ℝ) ∧ w.im ∈ Set.range ((↑) : ℚ → ℝ)} =
      Complex.equivRealProdCLM ⁻¹' (Set.range ((↑) : ℚ → ℝ) ×ˢ Set.range ((↑) : ℚ → ℝ)) := by
    ext w; simp [Set.mem_prod]
  have hS : Dense {w : ℂ | w.re ∈ Set.range ((↑) : ℚ → ℝ) ∧ w.im ∈ Set.range ((↑) : ℚ → ℝ)} := by
    rw [h2]; exact h1.preimage Complex.equivRealProdCLM.toHomeomorph.isOpenMap
  exact hS.preimage UpperHalfPlane.isOpenEmbedding_coe.isOpenMap

theorem liftGamma1_ne_zero {M : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma1 M) 2} (hg0 : g ≠ 0)
    {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hφg : CuspForm.IsAdelicLiftOfGamma1 g φ) : φ ≠ 0 := by
  intro hφ
  apply hg0
  have hcont : Continuous (⇑g : ℍ → ℂ) := (CuspFormClass.holo g).continuous
  have hEq : Set.EqOn (⇑g : ℍ → ℂ) (fun _ => (0 : ℂ))
      (((↑) : ℍ → ℂ) ⁻¹' {w : ℂ | w.re ∈ Set.range ((↑) : ℚ → ℝ) ∧ w.im ∈ Set.range ((↑) : ℚ → ℝ)}) := by
    rintro z ⟨⟨x, hx⟩, ⟨y, hy⟩⟩

    have hy0 : (0 : ℝ) < y := by rw [hy]; exact z.im_pos
    have hyq : (0 : ℚ) < y := by exact_mod_cast hy0

    let A : Matrix (Fin 2) (Fin 2) ℚ := !![y, x; 0, 1]
    have hdetA : A.det = y := by simp [A, Matrix.det_fin_two_of]
    let γ : GL (Fin 2) ℚ := GeneralLinearGroup.mkOfDetNeZero A (by rw [hdetA]; exact hyq.ne')
    let h : AdelicGL2 (𝓞 ℚ) ℚ :=
      globalPoints (𝓞 ℚ) ℚ γ * AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ))⁻¹
    have hfin : glFin (𝓞 ℚ) ℚ h = 1 := by
      simp only [h, map_mul, AdelicDock.glFin_finEmbed, mul_inv_cancel]
    have hP : LanglandsTunnell.ratArchGL2 h = GeneralLinearGroup.map (Rat.castHom ℝ) γ := by
      simp only [h, ratArch_mul, ratArch_finEmbed, mul_one, ratArch_globalPoints]
    have hPmat : ((LanglandsTunnell.ratArchGL2 h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        !![(y : ℝ), (x : ℝ); 0, 1] := by
      rw [hP]
      ext i j
      change (Rat.castHom ℝ) (A i j) = _
      fin_cases i <;> fin_cases j <;> simp [A]
    have hdetP : ((LanglandsTunnell.ratArchGL2 h).det.val : ℝ) = y := by
      rw [Matrix.GeneralLinearGroup.val_det_apply, hPmat, Matrix.det_fin_two_of]; ring
    have hdetpos : (0 : ℝ) < (LanglandsTunnell.ratArchGL2 h).det.val := by rw [hdetP]; exact hy0
    have hpos : LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ := by
      rw [Matrix.mem_glpos]; exact hdetpos

    have h3 := hφg.apply_eq h hfin hpos
    rw [hφ, Pi.zero_apply, ModularForm.slash_apply] at h3
    have hne1 : |((LanglandsTunnell.ratArchGL2 h).det.val : ℝ)| ^ ((2 : ℤ) - 1) ≠ 0 :=
      zpow_ne_zero _ (abs_ne_zero.mpr hdetpos.ne')
    have hne2 : UpperHalfPlane.denom (LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I ^ (-(2 : ℤ)) ≠ 0 :=
      zpow_ne_zero _ (UpperHalfPlane.denom_ne_zero _ _)
    have hg1 : (⇑g : ℍ → ℂ) ((LanglandsTunnell.ratArchGL2 h) • UpperHalfPlane.I) = 0 := by
      have := h3.symm
      rw [mul_eq_zero, mul_eq_zero] at this
      rcases this with (h0 | h0) | h0
      · rw [← UpperHalfPlane.σ_sq (LanglandsTunnell.ratArchGL2 h) ((⇑g : ℍ → ℂ) _), h0, map_zero]
      · exact absurd (by exact_mod_cast h0) hne1
      · exact absurd h0 hne2

    have hpt : (LanglandsTunnell.ratArchGL2 h) • UpperHalfPlane.I = z := by
      rw [UpperHalfPlane.coe_re] at hx
      rw [UpperHalfPlane.coe_im] at hy
      apply UpperHalfPlane.ext
      rw [UpperHalfPlane.coe_smul_of_det_pos hdetpos]
      simp only [UpperHalfPlane.num, UpperHalfPlane.denom, hPmat, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, UpperHalfPlane.coe_I,
        Complex.ofReal_zero, zero_mul, zero_add, Complex.ofReal_one, div_one]
      apply Complex.ext <;> simp [← hx, ← hy]
    rw [hpt] at hg1
    exact hg1
  have hfun : (⇑g : ℍ → ℂ) = fun _ => 0 := Continuous.ext_on dense_ratPoints hcont continuous_const hEq
  ext z
  exact congrFun hfun z

end Arch

end ArchG1

end B4Reduce

open B4Reduce in

theorem solution
    {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hg : g.IsNewform)
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hΦg : g.IsAdelicLiftOf Φ)
    (q : ℕ) [Fact q.Prime]
    (η : (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ →* ℂˣ)
    (hη : HeckeCharacter.IsFiniteOrderHeckeChar ℚ η)
    (b : ℕ) (hηb : HeckeCharacter.AdmitsModulus ℚ η (AdelicDock.ratLevel (q ^ b)))
    {M' : ℕ} [NeZero M'] {ε : DirichletCharacter ℂ M'} {h : CuspForm (CongruenceSubgroup.Gamma1 M') 2}
    (hh : CuspForm.IsPrimitiveForm ε h)
    (Φh : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hΦh : CuspForm.IsAdelicLiftOfGamma1 h Φh)
    (ha : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ M → ¬ ℓ ∣ M' → ℓ ≠ q →
      ModularFormClass.qCoeff h ℓ =
        (η (AutomorphicForm.uniformizerIdele ℚ (@AdelicDock.padicPlace ℓ ⟨hℓ⟩)) : ℂ) * ModularFormClass.qCoeff g ℓ)
    (hε : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ M → ¬ ℓ ∣ M' → ℓ ≠ q →
      ε (ℓ : ZMod M') = (η (AutomorphicForm.uniformizerIdele ℚ (@AdelicDock.padicPlace ℓ ⟨hℓ⟩)) : ℂ) ^ 2) :
    LocalNewvector.AdelicSpanSubmodule Φh = LocalNewvector.AdelicSpanSubmodule (AutomorphicForm.fnTwist ℚ η Φ) := by
  classical

  have hPdef : productionPinsGeneral ℚ = (productionPinsOf ℚ (⋃ x ∈ classRepTranslates ℚ, (· * x) '' centreCutSiegelSet ℚ (1/2 : ℝ) 1 (1/2) 2)
      (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) := rfl
  set Φ' : AdelicGL2 (𝓞 ℚ) ℚ → ℂ := fnTwist ℚ η Φ with hΦ'def
  have hM0 : (M : ℕ) ≠ 0 := NeZero.ne M
  have hM'0 : (M' : ℕ) ≠ 0 := NeZero.ne M'
  have hq0 : q ≠ 0 := (Fact.out : q.Prime).ne_zero

  have hbad : AdelicDock.ratLevel (M * M' * q) ≠ ⊥ :=
    AdelicDock.ratLevel_ne_bot (mul_ne_zero (mul_ne_zero hM0 hM'0) hq0)
  set S₀ : Finset (HeightOneSpectrum (𝓞 ℚ)) := (Ideal.finite_factors hbad).toFinset with hS₀def
  have hS₀mem : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.asIdeal ∣ AdelicDock.ratLevel (M * M' * q) → v ∈ S₀ := by
    intro v hv
    rw [hS₀def, Set.Finite.mem_toFinset]
    exact hv
  have hfac : AdelicDock.ratLevel (M * M' * q) =
      AdelicDock.ratLevel M * AdelicDock.ratLevel M' * AdelicDock.ratLevel q := by
    simp only [AdelicDock.ratLevel, Nat.cast_mul, Ideal.span_singleton_mul_span_singleton]
  have hS₀M : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S₀ → ¬ v.asIdeal ∣ AdelicDock.ratLevel M := by
    intro v hv hdvd
    refine hv (hS₀mem v ?_)
    rw [hfac]
    exact (hdvd.mul_right _).mul_right _
  have hS₀M' : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S₀ → ¬ v.asIdeal ∣ AdelicDock.ratLevel M' := by
    intro v hv hdvd
    refine hv (hS₀mem v ?_)
    rw [hfac]
    exact (hdvd.trans (dvd_mul_left _ _)).mul_right _
  have hS₀q : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S₀ → ¬ v.asIdeal ∣ AdelicDock.ratLevel q := by
    intro v hv hdvd
    refine hv (hS₀mem v ?_)
    rw [hfac]
    exact hdvd.trans (dvd_mul_left _ _)

  obtain ⟨ω, hωfin, hωmod, hωval, hωact⟩ :=
    CuspForm.HasNebentypus.exists_isFiniteOrderHeckeChar_centralScalar_mul_of_isAdelicLiftOfGamma1
      hh.isEigenformWith.hasNebentypus Φh hΦh
  set ξh : (productionPinsGeneral ℚ).Z →* ℂˣ := ω.comp (productionPinsGeneral ℚ).Z.subtype with hξhdef
  have hξh : ∀ (z : ↥((productionPinsGeneral ℚ).Z)) (x : AdelicGL2 (𝓞 ℚ) ℚ),
      Φh (centralScalar (𝓞 ℚ) ℚ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) * x) = ((ξh z : ℂˣ) : ℂ) * Φh x :=
    fun z x => hωact z x
  have hM'bot : AdelicDock.ratLevel M' ≠ ⊥ := AdelicDock.ratLevel_ne_bot hM'0
  let Ψh : HeckeEigensystem ℚ ℂ :=
    { level := AdelicDock.ratLevel M', level_ne_bot := hM'bot,
      a := fun v => ModularFormClass.qCoeff h (Ideal.absNorm v.asIdeal),
      b := fun v => (Ideal.absNorm v.asIdeal : ℂ) * ε ((Ideal.absNorm v.asIdeal : ℕ) : ZMod M') }
  have H1 : IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξh (AdelicDock.ratLevel M') S₀ Ψh Φh :=
    CuspForm.IsEigenformWith.isIsotypicCuspFormAt_of_isAdelicLiftOfGamma1 hh.isEigenformWith Φh hΦh ξh hξh S₀ hS₀M'
      Ψh (fun _ _ => rfl) (fun _ _ => rfl)
  have H1arch : Φh ∈ archCutSubmodule ℚ (ArchTypeFamily.ofChar ℚ (archWeightCharFamily ℚ 2)) :=
    (mem_archCutSubmodule_ofChar_iff ℚ (archWeightCharFamily ℚ 2) Φh).2
      (CuspForm.IsAdelicLiftOfGamma1.hasArchType0_archWeightCharFamily_two Φh hΦh)

  have hMbot : AdelicDock.ratLevel M ≠ ⊥ := AdelicDock.ratLevel_ne_bot hM0
  let Ψg : HeckeEigensystem ℚ ℂ :=
    { level := AdelicDock.ratLevel M, level_ne_bot := hMbot,
      a := fun v => ModularFormClass.qCoeff g (Ideal.absNorm v.asIdeal),
      b := fun v => (Ideal.absNorm v.asIdeal : ℂ) }
  have G1 : IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) 1 (AdelicDock.ratLevel M) S₀ Ψg Φ :=
    CuspForm.IsNormalizedEigenform.isIsotypicCuspFormAt_one_of_isAdelicLiftOf hg.isNormalizedEigenform Φ hΦg S₀ hS₀M
      Ψg (fun _ _ => rfl) (fun _ _ => rfl)
  have G1arch : Φ ∈ archCutSubmodule ℚ (ArchTypeFamily.ofChar ℚ (archWeightCharFamily ℚ 2)) :=
    (mem_archCutSubmodule_ofChar_iff ℚ (archWeightCharFamily ℚ 2) Φ).2
      (CuspForm.IsAdelicLiftOf.hasArchType0_archWeightCharFamily_two Φ hΦg)

  have key : ∀ (p : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ) → Prop) (x : AdelicGL2 (𝓞 ℚ) ℚ → ℂ),
      x ≠ 0 → (∀ V W, p V → p W → V = W) → x ∈ (⨆ (V : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)) (_ : p V), V) →
      ∃ V, p V ∧ x ∈ V := by
    intro p x hx huniq hmem
    by_cases hex : ∃ V, p V
    · obtain ⟨V₀, hV₀⟩ := hex
      refine ⟨V₀, hV₀, ?_⟩
      have hle : (⨆ (V : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)) (_ : p V), V) ≤ V₀ :=
        iSup₂_le fun V hV => (huniq V V₀ hV hV₀).le
      exact hle hmem
    · exfalso
      apply hx
      have hbot : (⨆ (V : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)) (_ : p V), V) = ⊥ := by
        refine le_antisymm (iSup₂_le fun V hV => (hex ⟨V, hV⟩).elim) bot_le
      rw [hbot, Submodule.mem_bot] at hmem
      exact hmem
  have hh0 : h ≠ 0 := by
    intro h0
    have h1 := hh.isEigenformWith.qCoeff_one
    have hz : ModularFormClass.qCoeff (h : UpperHalfPlane → ℂ) 1 = 0 := by
      have hcoe : ((h : CuspForm (CongruenceSubgroup.Gamma1 M') 2) : UpperHalfPlane → ℂ) = (0 : UpperHalfPlane → ℂ) := by
        rw [h0]; rfl
      rw [ModularFormClass.qCoeff, hcoe, UpperHalfPlane.qExpansion_zero]
      simp
    exact one_ne_zero (h1.symm.trans hz)
  have hΦh0 : Φh ≠ 0 := B4Reduce.liftGamma1_ne_zero hh0 hΦh
  have hΦ0 : Φ ≠ 0 := CuspForm.IsAdelicLiftOf.ne_zero hΦg hg.ne_zero
  obtain ⟨Vh, ⟨hVh, hVhMeets, -⟩, hΦhVh⟩ := key _ Φh hΦh0
    (fun V W hV hW => AutomorphicForm.eq_of_isCuspConstituent_of_cuspConstituentMeets_of_coversModCentre ℚ
        (1/2 : ℝ) 1 (1/2) 2 (classRepTranslates ℚ) (by norm_num) hcov ξh (AdelicDock.ratLevel M') S₀ Ψh V W
        hV.1 hW.1 hV.2.1 hW.2.1)
    (AutomorphicForm.isotypicCuspSubmodule_inf_archCutSubmodule_le_iSup_isCuspConstituent ℚ
        (1/2 : ℝ) 1 (1/2) 2 (classRepTranslates ℚ) (by norm_num) hcov ξh (AdelicDock.ratLevel M') S₀
        (ArchTypeFamily.ofChar ℚ (archWeightCharFamily ℚ 2)) Ψh ⟨H1.mem_isotypicCuspSubmodule, H1arch⟩)
  obtain ⟨Vg, ⟨hVg, hVgMeets, -⟩, hΦVg⟩ := key _ Φ hΦ0
    (fun V W hV hW => AutomorphicForm.eq_of_isCuspConstituent_of_cuspConstituentMeets_of_coversModCentre ℚ
        (1/2 : ℝ) 1 (1/2) 2 (classRepTranslates ℚ) (by norm_num) hcov 1 (AdelicDock.ratLevel M) S₀ Ψg V W
        hV.1 hW.1 hV.2.1 hW.2.1)
    (AutomorphicForm.isotypicCuspSubmodule_inf_archCutSubmodule_le_iSup_isCuspConstituent ℚ
        (1/2 : ℝ) 1 (1/2) 2 (classRepTranslates ℚ) (by norm_num) hcov 1 (AdelicDock.ratLevel M) S₀
        (ArchTypeFamily.ofChar ℚ (archWeightCharFamily ℚ 2)) Ψg ⟨G1.mem_isotypicCuspSubmodule, G1arch⟩)

  have hbg : IsBoundedGenuineFn ℚ (productionPinsGeneral ℚ) (NumberField.StandardAddChar.stdAddChar ℚ) Φ :=
    CuspForm.IsAdelicLiftOf.isBoundedGenuineFn_productionPinsGeneral_stdAddChar Φ hΦg
  obtain ⟨hV'cons, 𝔣₀, h𝔣₀, hmod₀, Ψ', hΨ'level, hΨ'ab, hmeets'⟩ :=
    AutomorphicForm.CuspidalConstituent.exists_cuspConstituentMeets_span_image_fnTwist_of_isIsotypicCuspFormAt_of_isBoundedGenuineFn_of_forall_not_dvd
      ℚ (1/2 : ℝ) 1 (1/2) 2 (classRepTranslates ℚ) (by norm_num) (by norm_num) 1 (AdelicDock.ratLevel M) hMbot S₀ hS₀M Ψg
      Vg hVg Φ hΦVg hΦ0 G1 hbg η hη (AdelicDock.ratLevel (q ^ b)) hηb
  set V' : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ) :=
    Submodule.span ℂ ((fun φ => fnTwist ℚ η φ) '' (Vg : Set (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))) with hV'def
  have hΦ'V' : Φ' ∈ V' := Submodule.subset_span ⟨Φ, hΦVg, rfl⟩

  have hη2icc : AutomorphicForm.IsIdeleClassChar (𝓞 ℚ) ℚ (η ^ 2) := fun u => by
    rw [MonoidHom.pow_apply, hη.isIdeleClassChar u, one_pow]
  have hη2cont : Continuous (η ^ 2 : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) := by
    have hfun : (⇑(η ^ 2 : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)) = fun x => η x ^ 2 := by
      funext x; exact MonoidHom.pow_apply η 2 x
    rw [hfun]
    exact hη.continuous.pow 2
  have hη2mod : HeckeCharacter.AdmitsModulus ℚ (η ^ 2) (AdelicDock.ratLevel (q ^ b)) := fun u hu1 hu2 => by
    rw [MonoidHom.pow_apply, hηb u hu1 hu2, one_pow]

  have hplace : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S₀ →
      ∃ (ℓ : ℕ) (hℓ : ℓ.Prime), v = @AdelicDock.padicPlace ℓ ⟨hℓ⟩ ∧ ¬ ℓ ∣ M ∧ ¬ ℓ ∣ M' ∧ ℓ ≠ q := by
    intro v hv

    have hdvd : ∀ n : ℕ, Rat.HeightOneSpectrum.natGenerator v ∣ n → v.asIdeal ∣ AdelicDock.ratLevel n := by
      intro n hn
      rw [AdelicDock.ratLevel, Ideal.dvd_span_singleton]
      rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff] at hn
      rwa [← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) n, Ideal.apply_mem_of_equiv_iff] at hn
    refine ⟨Rat.HeightOneSpectrum.natGenerator v, Rat.HeightOneSpectrum.prime_natGenerator v, ?_, ?_, ?_, ?_⟩
    · show v = (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨_, _⟩
      exact ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm_apply_apply v).symm
    · exact fun h => hS₀M v hv (hdvd M h)
    · exact fun h => hS₀M' v hv (hdvd M' h)
    · intro h
      exact hS₀q v hv (hdvd q (h ▸ dvd_rfl))
  have hωη : ω = η ^ 2 := by
    refine HeckeCharacter.eq_of_forall_apply_localUnit_uniformizerUnit_eq ℚ ω (η ^ 2) hωfin.isIdeleClassChar hη2icc
      hωfin.continuous hη2cont (AdelicDock.ratLevel M') (AdelicDock.ratLevel (q ^ b)) hωmod hη2mod S₀ ?_
    intro v hv
    obtain ⟨ℓ, hℓ, rfl, hℓM, hℓM', hℓq⟩ := hplace v hv
    have h1 := hωval ℓ hℓ hℓM'
    have h2 := hε ℓ hℓ hℓM hℓM' hℓq

    apply Units.ext
    show ((ω (uniformizerIdele ℚ (@AdelicDock.padicPlace ℓ ⟨hℓ⟩)) : ℂˣ) : ℂ) =
      (((η ^ 2) (uniformizerIdele ℚ (@AdelicDock.padicPlace ℓ ⟨hℓ⟩)) : ℂˣ) : ℂ)
    rw [h1, h2, MonoidHom.pow_apply, Units.val_pow_eq_pow_val]
  have hξ : twistedCentralChar ℚ ((productionPinsGeneral ℚ).Z) (1 : (productionPinsGeneral ℚ).Z →* ℂˣ) η = ξh := by
    refine MonoidHom.ext fun z => ?_
    simp only [twistedCentralChar, MonoidHom.mul_apply, MonoidHom.one_apply, one_mul, MonoidHom.pow_apply,
      MonoidHom.comp_apply, hξhdef, hωη]

  have hNtot : AdelicDock.ratLevel M' * (AdelicDock.ratLevel M * 𝔣₀ ^ 2) ≠ ⊥ :=
    mul_ne_zero hM'bot (mul_ne_zero hMbot (pow_ne_zero 2 h𝔣₀))
  set Sstar : Finset (HeightOneSpectrum (𝓞 ℚ)) := S₀ ∪ (Ideal.finite_factors hNtot).toFinset with hSstardef
  have hSstar : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ Sstar → ¬ v.asIdeal ∣ AdelicDock.ratLevel M' * (AdelicDock.ratLevel M * 𝔣₀ ^ 2) := by
    intro v hv hdvd
    apply hv
    rw [hSstardef, Finset.mem_union]
    exact Or.inr ((Ideal.finite_factors hNtot).mem_toFinset.2 hdvd)
  have hMeetsH : CuspConstituentMeets ℚ (productionPinsGeneral ℚ) ξh
      (AdelicDock.ratLevel M' * (AdelicDock.ratLevel M * 𝔣₀ ^ 2)) Sstar Ψh Vh :=
    ⟨Φh, hΦhVh, hΦh0, AutomorphicForm.IsIsotypicCuspFormAt.of_le_of_subset ℚ _ ξh Ideal.mul_le_left hNtot
      Finset.subset_union_left hSstar Ψh H1⟩
  have hMeets' : CuspConstituentMeets ℚ (productionPinsGeneral ℚ) ξh
      (AdelicDock.ratLevel M' * (AdelicDock.ratLevel M * 𝔣₀ ^ 2)) Sstar Ψh V' := by
    have hSstar𝔣 : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ Sstar → ¬ v.asIdeal ∣ 𝔣₀ := by
      intro v hv hdvd
      refine hSstar v hv (hdvd.trans ?_)
      exact (dvd_pow_self 𝔣₀ two_ne_zero).trans ((dvd_mul_left _ _).trans (dvd_mul_left _ _))
    obtain ⟨φ₁, hφ₁V', hφ₁0, hφ₁⟩ := hmeets' Sstar Finset.subset_union_left hSstar𝔣
    refine ⟨φ₁, hφ₁V', hφ₁0, ?_⟩

    have hdetgen : ∀ v : HeightOneSpectrum (𝓞 ℚ),
        Matrix.GeneralLinearGroup.det (heckeGen (𝓞 ℚ) ℚ v) = uniformizerIdele ℚ v := by
      intro v
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
      simp [heckeGen, heckeGenAt, diagOne_coe_apply, uniformizerIdele, Matrix.diagonal]

    have hab : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ Sstar → Ψ'.a v = Ψh.a v ∧ Ψ'.b v = Ψh.b v := by
      intro v hv
      have hv0 : v ∉ S₀ := fun h0 => hv (Finset.mem_union_left _ h0)
      obtain ⟨ℓ, hℓ, rfl, hℓM, hℓM', hℓq⟩ := hplace v hv0
      obtain ⟨ha', hb'⟩ := hΨ'ab (@AdelicDock.padicPlace ℓ ⟨hℓ⟩)
      have hnorm : Ideal.absNorm (@AdelicDock.padicPlace ℓ ⟨hℓ⟩).asIdeal = ℓ := by
        have hgen : Rat.HeightOneSpectrum.natGenerator (@AdelicDock.padicPlace ℓ ⟨hℓ⟩) = ℓ := by
          have := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply ⟨ℓ, hℓ⟩
          exact congrArg Subtype.val this
        set e : 𝓞 ℚ ≃+* ℤ := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) with he
        have hmap : (@AdelicDock.padicPlace ℓ ⟨hℓ⟩).asIdeal.map e = Ideal.span {(ℓ : ℤ)} := by
          rw [he, ← Rat.HeightOneSpectrum.span_natGenerator, hgen]
        have hI : (@AdelicDock.padicPlace ℓ ⟨hℓ⟩).asIdeal = Ideal.span {(ℓ : 𝓞 ℚ)} := by
          have h1 : (@AdelicDock.padicPlace ℓ ⟨hℓ⟩).asIdeal = ((@AdelicDock.padicPlace ℓ ⟨hℓ⟩).asIdeal.map e).comap e :=
            (Ideal.comap_map_of_bijective (e : 𝓞 ℚ →+* ℤ) e.bijective).symm
          rw [h1, hmap, ← Ideal.map_symm, Ideal.map_span, Set.image_singleton]
          congr 2
          exact map_natCast e.symm.toRingHom ℓ
        rw [hI, Ideal.absNorm_span_singleton]
        have h2 : (ℓ : 𝓞 ℚ) = algebraMap ℤ (𝓞 ℚ) (ℓ : ℤ) := by simp
        rw [h2, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, Module.finrank_self, pow_one]
        simp
      refine ⟨?_, ?_⟩
      · rw [ha', hdetgen]
        show _ * ModularFormClass.qCoeff (g : UpperHalfPlane → ℂ) (Ideal.absNorm _) =
          ModularFormClass.qCoeff (h : UpperHalfPlane → ℂ) (Ideal.absNorm _)
        rw [hnorm, ha ℓ hℓ hℓM hℓM' hℓq]
      · rw [hb', hdetgen]
        show _ * ((Ideal.absNorm _ : ℕ) : ℂ) = ((Ideal.absNorm _ : ℕ) : ℂ) * ε ((Ideal.absNorm _ : ℕ) : ZMod M')
        rw [hnorm, hε ℓ hℓ hℓM hℓM' hℓq, mul_comm]

    have hξ' : twistedCentralChar ℚ ((productionPinsOf ℚ (⋃ x ∈ classRepTranslates ℚ, (· * x) '' centreCutSiegelSet ℚ (1/2 : ℝ) 1 (1/2) 2)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)).Z)
        (1 : _ →* ℂˣ) η = ξh := hξ
    rw [hξ'] at hφ₁
    have hφ₁' : IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξh (AdelicDock.ratLevel M * 𝔣₀ ^ 2) Sstar Ψh φ₁ := by
      refine ⟨hφ₁.smoothCusp, hφ₁.continuous, hφ₁.level_invariant, fun v hv => ?_, fun v hv x => ?_⟩
      · have h1 := hφ₁.hecke_eigen v hv
        rwa [(hab v hv).1] at h1
      · have h1 := hφ₁.central_eigen v hv x
        rw [AutomorphicForm.HeckeEigensystem.toRawCentral_b] at h1 ⊢
        rwa [(hab v hv).2] at h1
    exact AutomorphicForm.IsIsotypicCuspFormAt.of_le_of_subset ℚ _ ξh Ideal.mul_le_right hNtot (Finset.Subset.refl _)
      hSstar Ψh hφ₁'

  have hV'cons' : IsCuspConstituent ℚ (productionPinsGeneral ℚ) ξh V' := by
    rw [← hξ]; exact hV'cons
  have hEq : V' = Vh :=
    AutomorphicForm.eq_of_isCuspConstituent_of_cuspConstituentMeets_of_coversModCentre ℚ
      (1/2 : ℝ) 1 (1/2) 2 (classRepTranslates ℚ) (by norm_num) hcov ξh _ Sstar Ψh V' Vh hV'cons' hVh hMeets' hMeetsH

  have hΦ'Vh : Φ' ∈ Vh := hEq ▸ hΦ'V'
  have hΦ'arch : Φ' ∈ archCutSubmodule ℚ (ArchTypeFamily.ofChar ℚ (archWeightCharFamily ℚ 2)) :=
    (mem_archCutSubmodule_ofChar_iff ℚ (archWeightCharFamily ℚ 2) Φ').2
      (AutomorphicForm.hasArchType0_fnTwist ℚ η (archWeightCharFamily ℚ 2)
        (CuspForm.IsAdelicLiftOf.hasArchType0_archWeightCharFamily_two Φ hΦg))
  have hΦ'0 : Φ' ≠ 0 := by
    intro h0
    apply hΦ0
    funext x
    have hx := congrFun h0 x
    rw [hΦ'def, fnTwist_apply, Pi.zero_apply, mul_eq_zero] at hx
    rcases hx with hx | hx
    · exact absurd hx (by simp [chiDet])
    · simpa using hx

  have A : Φ' ∈ Submodule.span ℂ ((fun x => rightTranslate ℚ x Φh) '' (finiteAdelicGL2Subgroup ℚ : Set (AdelicGL2 (𝓞 ℚ) ℚ))) :=
    AutomorphicForm.CuspidalConstituent.mem_span_rightTranslate_finiteAdelic_of_isCuspConstituent_of_finiteDimensional_of_mem_levelInvariantSubmodule_of_mem_archCutSubmodule_ofChar_of_pos
      ℚ (1/2 : ℝ) 1 (1/2) 2 (classRepTranslates ℚ) (by norm_num) (by norm_num) (by norm_num) hcov ξh Vh hVh
      (fun N tys hN => AutomorphicForm.finiteDimensional_inf_levelInvariantSubmodule_inf_archCutSubmodule_of_isCuspConstituent ℚ
        (1/2 : ℝ) 1 (1/2) 2 (classRepTranslates ℚ) (by norm_num) hcov ξh N hN tys Vh hVh)
      (fun w => IsTotallyReal.isReal w) (archWeightCharFamily ℚ 2)
      Φh Φ' hΦhVh hΦ'Vh H1arch hΦ'arch (AdelicDock.ratLevel M') hM'bot H1.level_invariant hΦh0

  have hΦhV' : Φh ∈ V' := by rw [hEq]; exact hΦhVh
  obtain ⟨Θ, hΘVg, hΘ⟩ : ∃ Θ ∈ Vg, fnTwist ℚ η Θ = Φh := by
    refine Submodule.span_induction (p := fun φ _ => ∃ Θ ∈ Vg, fnTwist ℚ η Θ = φ) ?_ ?_ ?_ ?_ hΦhV'
    · rintro _ ⟨Θ, hΘ, rfl⟩; exact ⟨Θ, hΘ, rfl⟩
    · exact ⟨0, Vg.zero_mem, by funext x; simp [fnTwist_apply]⟩
    · rintro a b - - ⟨Θa, ha, rfl⟩ ⟨Θb, hb, rfl⟩
      exact ⟨Θa + Θb, Vg.add_mem ha hb, by funext x; simp [fnTwist_apply, mul_add]⟩
    · rintro r a - ⟨Θa, ha, rfl⟩
      exact ⟨r • Θa, Vg.smul_mem r ha, by funext x; simp [fnTwist_apply]; ring⟩
  have hΘeq : Θ = fnTwist ℚ η⁻¹ Φh := by
    have hinv : η⁻¹ * η = 1 := inv_mul_cancel η
    rw [← hΘ, fnTwist_fnTwist, hinv, fnTwist_one]
  have hΘarch : Θ ∈ archCutSubmodule ℚ (ArchTypeFamily.ofChar ℚ (archWeightCharFamily ℚ 2)) := by
    rw [hΘeq]
    exact (mem_archCutSubmodule_ofChar_iff ℚ (archWeightCharFamily ℚ 2) _).2
      (AutomorphicForm.hasArchType0_fnTwist ℚ η⁻¹ (archWeightCharFamily ℚ 2)
        ((mem_archCutSubmodule_ofChar_iff ℚ (archWeightCharFamily ℚ 2) Φh).1 H1arch))
  have B0 : Θ ∈ Submodule.span ℂ ((fun x => rightTranslate ℚ x Φ) '' (finiteAdelicGL2Subgroup ℚ : Set (AdelicGL2 (𝓞 ℚ) ℚ))) :=
    AutomorphicForm.CuspidalConstituent.mem_span_rightTranslate_finiteAdelic_of_isCuspConstituent_of_finiteDimensional_of_mem_levelInvariantSubmodule_of_mem_archCutSubmodule_ofChar_of_pos
      ℚ (1/2 : ℝ) 1 (1/2) 2 (classRepTranslates ℚ) (by norm_num) (by norm_num) (by norm_num) hcov 1 Vg hVg
      (fun N tys hN => AutomorphicForm.finiteDimensional_inf_levelInvariantSubmodule_inf_archCutSubmodule_of_isCuspConstituent ℚ
        (1/2 : ℝ) 1 (1/2) 2 (classRepTranslates ℚ) (by norm_num) hcov 1 N hN tys Vg hVg)
      (fun w => IsTotallyReal.isReal w) (archWeightCharFamily ℚ 2)
      Φ Θ hΦVg hΘVg G1arch hΘarch (AdelicDock.ratLevel M) hMbot G1.level_invariant hΦ0

  have B : Φh ∈ Submodule.span ℂ ((fun x => rightTranslate ℚ x Φ') '' (finiteAdelicGL2Subgroup ℚ : Set (AdelicGL2 (𝓞 ℚ) ℚ))) := by
    rw [← hΘ]
    refine Submodule.span_induction
      (p := fun θ _ => fnTwist ℚ η θ ∈
        Submodule.span ℂ ((fun x => rightTranslate ℚ x Φ') '' (finiteAdelicGL2Subgroup ℚ : Set (AdelicGL2 (𝓞 ℚ) ℚ))))
      ?_ ?_ ?_ ?_ B0
    · rintro _ ⟨x, hx, rfl⟩
      show fnTwist ℚ η (rightTranslate ℚ x Φ) ∈ _
      have hc : chiDet (𝓞 ℚ) ℚ η x ≠ 0 := by unfold chiDet; exact Units.ne_zero _
      have hrel : rightTranslate ℚ x Φ' = chiDet (𝓞 ℚ) ℚ η x • fnTwist ℚ η (rightTranslate ℚ x Φ) := by
        funext y
        simp only [hΦ'def, rightTranslate_apply, fnTwist_apply, Pi.smul_apply, smul_eq_mul, chiDet, map_mul,
          Units.val_mul]
        ring
      have hrel' : fnTwist ℚ η (rightTranslate ℚ x Φ) = (chiDet (𝓞 ℚ) ℚ η x)⁻¹ • rightTranslate ℚ x Φ' := by
        rw [hrel, smul_smul, inv_mul_cancel₀ hc, one_smul]
      rw [hrel']
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, hx, rfl⟩)
    · have h0 : fnTwist ℚ η (0 : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) = 0 := by funext x; simp [fnTwist_apply]
      show fnTwist ℚ η 0 ∈ _
      rw [h0]; exact Submodule.zero_mem _
    · intro a c _ _ ha hc
      have hadd : fnTwist ℚ η (a + c) = fnTwist ℚ η a + fnTwist ℚ η c := by
        funext x; simp [fnTwist_apply, mul_add]
      show fnTwist ℚ η (a + c) ∈ _
      rw [hadd]; exact Submodule.add_mem _ ha hc
    · intro r a _ ha
      have hsm : fnTwist ℚ η (r • a) = r • fnTwist ℚ η a := by
        funext x; simp [fnTwist_apply]; ring
      show fnTwist ℚ η (r • a) ∈ _
      rw [hsm]; exact Submodule.smul_mem _ r ha

  have absorb : ∀ (ψ θ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ),
      ψ ∈ Submodule.span ℂ ((fun x => rightTranslate ℚ x θ) '' (finiteAdelicGL2Subgroup ℚ : Set (AdelicGL2 (𝓞 ℚ) ℚ))) →
      LocalNewvector.AdelicSpanSubmodule ψ ≤ LocalNewvector.AdelicSpanSubmodule θ := by
    intro ψ θ hψ

    have hmk : ∀ x : AdelicGL2 (𝓞 ℚ) ℚ, LocalNewvector.AdelicFnCarrier.mk (rightTranslate ℚ x θ)
        = x • LocalNewvector.AdelicFnCarrier.mk θ := fun x => rfl

    have hgen : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, g • LocalNewvector.AdelicFnCarrier.mk ψ ∈ LocalNewvector.AdelicSpanSubmodule θ := by
      intro g
      refine Submodule.span_induction (p := fun ψ _ => g • LocalNewvector.AdelicFnCarrier.mk ψ ∈
        LocalNewvector.AdelicSpanSubmodule θ) ?_ ?_ ?_ ?_ hψ
      · rintro _ ⟨x, -, rfl⟩
        rw [hmk, ← mul_smul]
        exact Submodule.subset_span ⟨g * x, rfl⟩
      · show g • LocalNewvector.AdelicFnCarrier.mk 0 ∈ _
        have : LocalNewvector.AdelicFnCarrier.mk (F := ℚ) 0 = 0 := rfl
        rw [this, smul_zero]
        exact Submodule.zero_mem _
      · intro a c _ _ ha hc
        have : LocalNewvector.AdelicFnCarrier.mk (a + c) =
            LocalNewvector.AdelicFnCarrier.mk a + LocalNewvector.AdelicFnCarrier.mk c := rfl
        rw [this, smul_add]
        exact Submodule.add_mem _ ha hc
      · intro r a _ ha
        have : LocalNewvector.AdelicFnCarrier.mk (r • a) = r • LocalNewvector.AdelicFnCarrier.mk a := rfl
        rw [this, smul_comm]
        exact Submodule.smul_mem _ r ha
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, rfl⟩
    exact hgen g
  exact le_antisymm (absorb Φh Φ' B) (absorb Φ' Φh A)

end
end S_CuspForm_IsNewform_adelicSpanSubmodule_eq_of_isPrimitiveForm_adelicLiftGamma1_fnTwist
end P2MW
export P2MW.S_CuspForm_IsNewform_adelicSpanSubmodule_eq_of_isPrimitiveForm_adelicLiftGamma1_fnTwist (solution)
