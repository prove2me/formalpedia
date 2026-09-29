-- Prove2me | solution 1 for DeligneSerre.eulerFactor_eq_and_tameLevel_of_weightOne_newform_qCoeff_eq_trace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/649b2173-a2d3-52ab-b8a8-9475a0d71609

import Mathlib
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_GaloisRep_ComplexConjugation
import Definitions.Def_Deformations_MatrixRepresentation
import Definitions.Def_ArtinL_Conductor
import Definitions.Def_GaloisRep_GlobalUnramifiedAt
import Definitions.Def_FormalHecke_Eigensystem
import Theorems.Thm_ArtinL_eulerFactorAt_eq_eulerFactor
import Theorems.Thm_ArtinL_conductorExponent_add_finrank_inertiaInvariants_eq
import Theorems.Thm_ArtinL_exists_completedLSeries_functionalEquation_of_odd
import Theorems.Thm_DeligneSerre_eq_of_eulerProduct_completedLSeries_functionalEquation
import Theorems.Thm_CuspForm_exists_weightOne_completedLSeries_functionalEquation_of_fricke
import Theorems.Thm_FormalHecke_IsEigensystem_isRecursive
import Theorems.Thm_GlobalGaloisRep_exists_finset_forall_isUnramifiedAt_of_isOpen_ker
import Theorems.Thm_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime
import Theorems.Thm_ValuationSubring_exists_liesOverPrime_isFrobeniusAt_ratAlgClosure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DeligneSerre_eulerFactor_eq_and_tameLevel_of_weightOne_newform_qCoeff_eq_trace
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem"
p2m_attr_erase "instance" "RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion M4aHerbrand.Bridge.instT2SpaceAdeleRing LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO"
p2m_attr_erase "instance" "ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm JacobiSumStickelberger.instModuleZModModP instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal FixedPoints.isLocalRing_subring FixedPoints.isLocalHom_subring_subtype"
p2m_attr_erase "simp" "ArtinL.Abelian.coeff_zero LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal"
p2m_attr_erase "simp" "Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply"
p2m_attr_erase "simp" "IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply IsLocalRing.upperRamificationGroup_zero IsLocalRing.upperRamificationIndex_zero IsLocalRing.herbrandPhi_zero ValuationSubring.herbrandPhi_zero IsLocalRing.mem_upperRamificationGroup"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent IsLocalRing.principalUnits_zero ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot Stickelberger.mem_exponentSet galRestrictionDatum_apply Ideal.coe_mapNonZero"
p2m_attr_erase "simp" "algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.SUnits.val_zsmul NumberField.SUnits.val_add IsLocalRing.lowerRamificationGroup_subgroupOf IsLocalRing.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_subgroupOf NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.CarrierPins.mk.injEq AutomorphicForm.CarrierPins.mk.sizeOf_spec AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open CongruenceSubgroup Polynomial
open scoped MatrixGroups

namespace DeligneSerreDS46c

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
local notation "ℚbar" => AlgebraicClosure ℚ

section PartA

def eulerPoly (c₁ c₂ : ℂ) : ℂ[X] := 1 - C c₁ * X + C c₂ * X ^ 2

@[scoped simp] theorem coeff_eulerPoly_zero (c₁ c₂ : ℂ) : (eulerPoly c₁ c₂).coeff 0 = 1 := by
  simp [eulerPoly, coeff_one, coeff_X, coeff_C]

@[scoped simp] theorem coeff_eulerPoly_one (c₁ c₂ : ℂ) : (eulerPoly c₁ c₂).coeff 1 = -c₁ := by
  simp [eulerPoly, coeff_one, coeff_C, coeff_X_pow]

@[scoped simp] theorem coeff_eulerPoly_two (c₁ c₂ : ℂ) : (eulerPoly c₁ c₂).coeff 2 = c₂ := by
  simp [eulerPoly, coeff_one, coeff_X_pow]

theorem natDegree_eulerPoly_le (c₁ c₂ : ℂ) : (eulerPoly c₁ c₂).natDegree ≤ 2 := by
  unfold eulerPoly
  have h1 : (1 - C c₁ * X : ℂ[X]).natDegree ≤ 2 := by
    refine (natDegree_sub_le _ _).trans (max_le (by simp) ?_)
    exact (natDegree_C_mul_le _ _).trans (by simp)
  refine (natDegree_add_le _ _).trans (max_le h1 ?_)
  exact (natDegree_C_mul_le _ _).trans (by simp)

theorem natDegree_eulerPoly_of_ne_zero (c₁ : ℂ) {c₂ : ℂ} (h : c₂ ≠ 0) :
    (eulerPoly c₁ c₂).natDegree = 2 := by
  refine le_antisymm (natDegree_eulerPoly_le c₁ c₂) ?_
  exact le_natDegree_of_ne_zero (by rwa [coeff_eulerPoly_two])

theorem natDegree_eulerPoly_zero_le (c₁ : ℂ) : (eulerPoly c₁ 0).natDegree ≤ 1 := by
  unfold eulerPoly
  simp only [map_zero, zero_mul, add_zero]
  refine (natDegree_sub_le _ _).trans (max_le (by simp) ?_)
  exact (natDegree_C_mul_le _ _).trans (by simp)

theorem eulerPoly_mul_mk_eq_one {e a : ℕ → ℂ} (h : FormalHecke.IsRecursive e a) {p : ℕ}
    (hp : p.Prime) :
    ((eulerPoly (a p) (e p) : ℂ[X]) : PowerSeries ℂ) * PowerSeries.mk (fun k => a (p ^ k)) = 1 := by
  obtain ⟨h1, -, hrec⟩ := h
  set F : PowerSeries ℂ := PowerSeries.mk (fun k => a (p ^ k)) with hF
  have hcoe : ((eulerPoly (a p) (e p) : ℂ[X]) : PowerSeries ℂ) =
      1 - PowerSeries.C (a p) * PowerSeries.X + PowerSeries.C (e p) * PowerSeries.X ^ 2 := by
    simp [eulerPoly, Polynomial.coe_sub, Polynomial.coe_add, Polynomial.coe_mul,
      Polynomial.coe_one, Polynomial.coe_C, Polynomial.coe_X, Polynomial.coe_pow]
  rw [hcoe]
  ext k
  have expand : (1 - PowerSeries.C (a p) * PowerSeries.X + PowerSeries.C (e p) * PowerSeries.X ^ 2) * F
      = F - PowerSeries.C (a p) * (PowerSeries.X * F)
          + PowerSeries.C (e p) * (PowerSeries.X ^ 2 * F) := by ring
  rw [expand, map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_one]
  rcases k with _ | k
  · simp [hF, h1]
  rcases k with _ | k
  · rw [PowerSeries.coeff_succ_X_mul]
    simp [hF, h1]
  · rw [PowerSeries.coeff_succ_X_mul, if_pos (by omega)]
    simp only [hF, PowerSeries.coeff_mk, show k + 1 + 1 - 2 = k by omega]
    rw [if_neg (by omega), hrec p k hp]
    ring

end PartA

section ArtinSide

variable {n : ℕ}

theorem constantCoeff_eulerFactor (ρ : Γℚ →* GL (Fin n) ℂ) (p : ℕ) :
    PowerSeries.constantCoeff ((ArtinL.eulerFactor ρ p : ℂ[X]) : PowerSeries ℂ) = 1 := by
  rw [Polynomial.constantCoeff_coe]
  exact ArtinL.coeff_eulerFactor_zero ρ p

theorem coeffPrimePow_zero (ρ : Γℚ →* GL (Fin n) ℂ) (p : ℕ) : ArtinL.coeffPrimePow ρ p 0 = 1 := by
  rw [ArtinL.coeffPrimePow, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.constantCoeff_inv, constantCoeff_eulerFactor, inv_one]

theorem mk_coeff_pow_eq_inv (ρ : Γℚ →* GL (Fin n) ℂ) {p : ℕ} (hp : p.Prime) :
    PowerSeries.mk (fun k => ArtinL.coeff ρ (p ^ k)) =
      ((ArtinL.eulerFactor ρ p : ℂ[X]) : PowerSeries ℂ)⁻¹ := by
  ext k
  rw [PowerSeries.coeff_mk]
  have hpk : p ^ k ≠ 0 := pow_ne_zero k hp.ne_zero
  rw [ArtinL.coeff, if_neg hpk, Nat.Prime.factorization_pow hp,
    Finsupp.prod_single_index (coeffPrimePow_zero ρ p)]
  rfl

theorem eulerFactor_mul_mk_eq_one (ρ : Γℚ →* GL (Fin n) ℂ) {p : ℕ} (hp : p.Prime) :
    ((ArtinL.eulerFactor ρ p : ℂ[X]) : PowerSeries ℂ) *
        PowerSeries.mk (fun k => ArtinL.coeff ρ (p ^ k)) = 1 := by
  rw [mk_coeff_pow_eq_inv ρ hp]
  exact PowerSeries.mul_inv_cancel _ (by rw [constantCoeff_eulerFactor]; exact one_ne_zero)

theorem coeff_mul_of_coprime (ρ : Γℚ →* GL (Fin n) ℂ) {m k : ℕ} (hmk : m.Coprime k) :
    ArtinL.coeff ρ (m * k) = ArtinL.coeff ρ m * ArtinL.coeff ρ k := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [(Nat.coprime_zero_left _).mp hmk]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [(Nat.coprime_zero_right _).mp hmk]
  have hm0 : m ≠ 0 := hm.ne'
  have hk0 : k ≠ 0 := hk.ne'
  rw [ArtinL.coeff, ArtinL.coeff, ArtinL.coeff, if_neg (mul_ne_zero hm0 hk0), if_neg hm0, if_neg hk0,
    Nat.factorization_mul hm0 hk0]
  rw [Finsupp.prod_add_index_of_disjoint]
  rw [Nat.support_factorization, Nat.support_factorization]
  exact hmk.disjoint_primeFactors

end ArtinSide

section Toolkit

variable {n : ℕ}

theorem mem_inertiaInvariants_iff (ρ : Γℚ →* GL (Fin n) ℂ) (A : ValuationSubring ℚbar)
    (v : Fin n → ℂ) :
    v ∈ ArtinL.inertiaInvariants ρ A ↔
      ∀ τ ∈ A.inertiaSubgroupIn ℚ, Deformation.matrixRepresentation ρ τ v = v := by
  change v ∈ Representation.invariants _ ↔ _
  rw [Representation.mem_invariants]
  constructor
  · intro h τ hτ
    exact h ⟨τ, hτ⟩
  · rintro h ⟨τ, hτ⟩
    exact h τ hτ

theorem inertiaInvariants_eq_top_of_le_ker (ρ : Γℚ →* GL (Fin n) ℂ) (A : ValuationSubring ℚbar)
    (h : A.inertiaSubgroupIn ℚ ≤ ρ.ker) : ArtinL.inertiaInvariants ρ A = ⊤ := by
  refine eq_top_iff.mpr fun v _ => (mem_inertiaInvariants_iff ρ A v).mpr fun τ hτ => ?_
  have h1 : ρ τ = 1 := h hτ
  simp [Deformation.matrixRepresentation_apply, h1]

theorem apply_eq_one_of_inertiaInvariants_eq_top (ρ : Γℚ →* GL (Fin n) ℂ)
    (A : ValuationSubring ℚbar) (h : ArtinL.inertiaInvariants ρ A = ⊤) {τ : Γℚ}
    (hτ : τ ∈ A.inertiaSubgroupIn ℚ) : ρ τ = 1 := by
  have hv : ∀ v : Fin n → ℂ, Deformation.matrixRepresentation ρ τ v = v := fun v =>
    (mem_inertiaInvariants_iff ρ A v).mp (h ▸ Submodule.mem_top) τ hτ
  have hmat : ((ρ τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = 1 := by
    refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.one_mulVec]
    simpa [Deformation.matrixRepresentation_apply] using hv v
  exact Units.ext hmat

theorem charpolyRev_restrict_of_eq_top {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V) {W : Submodule ℂ V} (hW : W = ⊤)
    (h : ∀ v ∈ W, T v ∈ W) : ArtinL.charpolyRev (T.restrict h) = ArtinL.charpolyRev T := by
  subst hW
  let e : (⊤ : Submodule ℂ V) ≃ₗ[ℂ] V := LinearEquiv.ofTop ⊤ rfl
  have hconj : e.conj (T.restrict h) = T := by
    ext v
    simp [e, LinearEquiv.conj_apply, LinearMap.restrict_apply]
  rw [← ArtinL.charpolyRev_conj e, hconj]

theorem eulerFactorAt_eq_of_top (ρ : Γℚ →* GL (Fin n) ℂ) (A : ValuationSubring ℚbar)
    (h : ArtinL.inertiaInvariants ρ A = ⊤) (σ : Γℚ) :
    ArtinL.eulerFactorAt ρ A σ = ((ρ σ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).charpolyRev := by
  have hst : ∀ v ∈ ArtinL.inertiaInvariants ρ A,
      Deformation.matrixRepresentation ρ σ v ∈ ArtinL.inertiaInvariants ρ A := fun v _ => by
    rw [h]; exact Submodule.mem_top
  rw [ArtinL.eulerFactorAt, dif_pos hst, charpolyRev_restrict_of_eq_top _ h,
    Deformation.matrixRepresentation_apply, ArtinL.charpolyRev_mulVecLin]

theorem eulerFactorAt_of_stable (ρ : Γℚ →* GL (Fin n) ℂ) (A : ValuationSubring ℚbar) (σ : Γℚ)
    (h : ∀ v ∈ ArtinL.inertiaInvariants ρ A,
      Deformation.matrixRepresentation ρ σ v ∈ ArtinL.inertiaInvariants ρ A) :
    ArtinL.eulerFactorAt ρ A σ =
        ArtinL.charpolyRev ((Deformation.matrixRepresentation ρ σ).restrict h) ∧
      (ArtinL.eulerFactorAt ρ A σ).natDegree ≤
        Module.finrank ℂ (ArtinL.inertiaInvariants ρ A) ∧
      (ArtinL.eulerFactorAt ρ A σ).coeff 1 =
        -LinearMap.trace ℂ _ ((Deformation.matrixRepresentation ρ σ).restrict h) := by
  have heq : ArtinL.eulerFactorAt ρ A σ =
      ArtinL.charpolyRev ((Deformation.matrixRepresentation ρ σ).restrict h) := by
    rw [ArtinL.eulerFactorAt, dif_pos h]
  refine ⟨heq, ?_, ?_⟩
  · rw [heq]; exact ArtinL.natDegree_charpolyRev_le _
  · rw [heq, ArtinL.coeff_charpolyRev_one]

theorem exists_pow_fixes (L : IntermediateField ℚ ℚbar) [FiniteDimensional ℚ L]
    (σ : Γℚ) : ∃ d : ℕ, 0 < d ∧ ∀ x ∈ L, (σ ^ d) x = x := by
  classical
  let F : ℕ → (L →ₐ[ℚ] ℚbar) := fun k => (σ ^ k).toAlgHom.comp L.val
  obtain ⟨i, j, hij, hF⟩ := Finite.exists_ne_map_eq_of_infinite F
  wlog hlt : i < j generalizing i j
  · exact this j i hij.symm hF.symm (lt_of_le_of_ne (not_lt.mp hlt) hij.symm)
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hlt
  refine ⟨d + 1, Nat.succ_pos d, fun x hx => ?_⟩
  have h := congrArg (fun φ : L →ₐ[ℚ] ℚbar => φ ⟨x, hx⟩) hF
  simp only [F, AlgHom.coe_comp, Function.comp_apply] at h
  rw [show i + d + 1 = i + (d + 1) by ring, pow_add] at h
  change (σ ^ i) x = (σ ^ i * σ ^ (d + 1)) x at h
  rw [AlgEquiv.mul_apply] at h
  exact ((σ ^ i).injective h).symm

theorem exists_pow_eq_one {ρ : Γℚ →* GL (Fin n) ℂ} (hρ : GaloisFactorsThroughFiniteLevel ρ)
    (σ : Γℚ) : ∃ d : ℕ, 0 < d ∧ ρ σ ^ d = 1 := by
  obtain ⟨L, hL, hker⟩ := hρ
  haveI := hL
  obtain ⟨d, hd, hfix⟩ := exists_pow_fixes L σ
  exact ⟨d, hd, by rw [← map_pow]; exact hker _ hfix⟩

theorem isOpen_ker {ρ : Γℚ →* GL (Fin n) ℂ} (hρ : GaloisFactorsThroughFiniteLevel ρ) :
    IsOpen ((ρ.ker : Subgroup Γℚ) : Set Γℚ) := by
  obtain ⟨L, hL, hker⟩ := hρ
  haveI := hL
  refine Subgroup.isOpen_mono (H₁ := L.fixingSubgroup) ?_ (IntermediateField.fixingSubgroup_isOpen L)
  intro σ hσ
  rw [IntermediateField.mem_fixingSubgroup_iff] at hσ
  exact hker σ hσ

theorem norm_eq_one_of_isRoot_charpolyRev {W : Type*} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (T : W →ₗ[ℂ] W) {d : ℕ} (hd : 0 < d) (hT : T ^ d = 1) {z : ℂ}
    (hz : (ArtinL.charpolyRev T).IsRoot z) : ‖z‖ = 1 := by
  classical
  rcases (Module.finrank ℂ W).eq_zero_or_pos with h0 | hpos
  ·
    exfalso
    have hdeg : (ArtinL.charpolyRev T).natDegree ≤ 0 :=
      (ArtinL.natDegree_charpolyRev_le T).trans h0.le
    have hC := Polynomial.eq_C_of_natDegree_le_zero hdeg
    rw [ArtinL.coeff_charpolyRev_zero] at hC
    have h1 := hz
    rw [hC, IsRoot.def, eval_C] at h1
    exact one_ne_zero h1
  haveI : Nonempty (Fin (Module.finrank ℂ W)) := ⟨⟨0, hpos⟩⟩
  set B := LinearMap.toMatrix (Module.finBasis ℂ W) (Module.finBasis ℂ W) T with hB
  have hBd : B ^ d = 1 := by
    rw [hB, LinearMap.toMatrix_pow, hT, LinearMap.toMatrix_one]
  have hz0 : z ≠ 0 := by
    rintro rfl
    have h0 := hz
    rw [IsRoot.def, ← coeff_zero_eq_eval_zero, ArtinL.coeff_charpolyRev_zero] at h0
    exact one_ne_zero h0

  have hrev : (ArtinL.charpolyRev T) = B.charpoly.reverse := by
    rw [ArtinL.charpolyRev, Matrix.reverse_charpoly]
  haveI : Invertible z⁻¹ := invertibleOfNonzero (inv_ne_zero hz0)
  have hroot : IsRoot B.charpoly z⁻¹ := by
    have h1 : eval₂ (RingHom.id ℂ) (⅟ (z⁻¹)) B.charpoly.reverse = 0 := by
      rw [invOf_eq_inv, inv_inv, ← hrev]
      exact hz
    rw [Polynomial.eval₂_reverse_eq_zero_iff] at h1
    exact h1
  have hmem : z⁻¹ ∈ spectrum ℂ B := Matrix.mem_spectrum_of_isRoot_charpoly hroot
  have hpow : (z⁻¹) ^ d ∈ spectrum ℂ (B ^ d) := spectrum.pow_mem_pow B d hmem
  rw [hBd, spectrum.one_eq, Set.mem_singleton_iff] at hpow
  have hn : ‖z⁻¹‖ ^ d = 1 := by rw [← norm_pow, hpow, norm_one]
  have hn1 : ‖z⁻¹‖ = 1 := (pow_eq_one_iff_of_nonneg (norm_nonneg _) hd.ne').mp hn
  rwa [norm_inv, inv_eq_one] at hn1

end Toolkit

section PartC

theorem norm_dirichlet_prime_eq_one {M : ℕ} (ε : DirichletCharacter ℂ M) {p : ℕ} (hp : p.Prime)
    (hpM : ¬ p ∣ M) : ‖ε (p : ZMod M)‖ = 1 := by
  have hu : IsUnit (p : ZMod M) := by
    rw [ZMod.isUnit_prime_iff_not_dvd hp]
    exact hpM
  obtain ⟨u, hu⟩ := hu
  rw [← hu]
  exact ε.unit_norm_eq_one u

theorem sqrt_div_two_pi_cpow (N : ℕ) (s : ℂ) :
    ((Real.sqrt N / (2 * Real.pi) : ℝ) : ℂ) ^ s =
      ((Real.sqrt N : ℝ) : ℂ) ^ s * (((2 * Real.pi)⁻¹ : ℝ) : ℂ) ^ s := by
  rw [div_eq_mul_inv, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (Real.sqrt_nonneg _) (inv_nonneg.mpr (by positivity))]

theorem roots_large_of_norm_le_one {b : ℂ} (hb : ‖b‖ ≤ 1) {p : ℕ} (hp : p.Prime) {z : ℂ}
    (hz : (eulerPoly b 0).IsRoot z) : 1 < ‖z‖ ^ 2 * p := by
  have h : 1 - b * z = 0 := by
    have := hz
    simp only [eulerPoly, map_zero, zero_mul, add_zero, IsRoot.def, eval_sub, eval_one, eval_mul,
      eval_C, eval_X] at this
    exact this
  have hbz : b * z = 1 := by linear_combination -h
  have hn : ‖b‖ * ‖z‖ = 1 := by rw [← norm_mul, hbz, norm_one]
  have hz1 : 1 ≤ ‖z‖ := by
    by_contra hlt
    push Not at hlt
    have : ‖b‖ * ‖z‖ < 1 := by
      calc ‖b‖ * ‖z‖ ≤ 1 * ‖z‖ := by gcongr
        _ = ‖z‖ := one_mul _
        _ < 1 := hlt
    linarith
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hz2 : 1 ≤ ‖z‖ ^ 2 := by nlinarith
  nlinarith

end PartC

end DeligneSerreDS46c
p2m_reactivate "P2MW.S_DeligneSerre_eulerFactor_eq_and_tameLevel_of_weightOne_newform_qCoeff_eq_trace.DeligneSerreDS46c"

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

open DeligneSerreDS46c in
theorem solution
    (ρ : Γℚ →* GL (Fin 2) ℂ) (hρ : GaloisFactorsThroughFiniteLevel ρ)
    (hodd : ((ρ complexConjugation : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det = -1)
    (M : ℕ) [NeZero M] (ε : DirichletCharacter ℂ M) (g g' : CuspForm (Gamma1 M) 1) (c : ℂ)
    (hg₁ : ModularFormClass.qCoeff g 1 = 1)
    (hT : ∀ p : ℕ, p.Prime → ¬ p ∣ M → ∀ n : ℕ,
        ModularFormClass.qCoeff g (p * n) +
            ε (p : ZMod M) * (if p ∣ n then ModularFormClass.qCoeff g (n / p) else 0) =
          ModularFormClass.qCoeff g p * ModularFormClass.qCoeff g n)
    (hU : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ M → ∀ n : ℕ,
        ModularFormClass.qCoeff g (ℓ * n) =
          ModularFormClass.qCoeff g ℓ * ModularFormClass.qCoeff g n)
    (hε : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 M → ∀ τ : UpperHalfPlane,
        g (γ • τ) =
          ε ((γ 1 1 : ℤ) : ZMod M) * ((((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) * g τ))
    (hg' : ∀ n : ℕ, ModularFormClass.qCoeff g' n = starRingEnd ℂ (ModularFormClass.qCoeff g n))
    (hc : c ≠ 0)
    (hW : ∀ τ τ' : UpperHalfPlane, (τ' : ℂ) * ((M : ℂ) * (τ : ℂ)) = -1 →
        g τ' = c * (τ : ℂ) * g' τ)
    (hLi : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ M → ‖ModularFormClass.qCoeff g ℓ‖ ≤ 1)
    (N₀ : ℕ) (hN₀ : N₀ ≠ 0)
    (hρg : ∀ p : ℕ, p.Prime → ¬ p ∣ N₀ →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
          ∀ σ : Γℚ, A.IsFrobeniusAt σ p →
            ModularFormClass.qCoeff g p =
                ((ρ σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).trace ∧
            ε (p : ZMod M) = ((ρ σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det) :
    (∀ p : ℕ, p.Prime → ¬ p ∣ M →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
        (∀ σ ∈ A.inertiaSubgroupIn ℚ, ρ σ = 1) ∧
        ∀ σ : Γℚ, A.IsFrobeniusAt σ p →
          ModularFormClass.qCoeff g p =
              ((ρ σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).trace ∧
          ε (p : ZMod M) = ((ρ σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det) ∧
    (∀ ℓ : ℕ, ℓ.Prime →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        (Nat.card ((A.inertiaSubgroupIn ℚ).map ρ)).Coprime ℓ →
          M.factorization ℓ +
              Module.finrank ℂ (Representation.invariants
                ((Deformation.matrixRepresentation ρ).comp
                  (A.inertiaSubgroupIn ℚ).subtype)) = 2 ∧
          ∀ σ : Γℚ, A.IsFrobeniusAt σ ℓ →
            ∃ hσ : ∀ v ∈ Representation.invariants
                  ((Deformation.matrixRepresentation ρ).comp (A.inertiaSubgroupIn ℚ).subtype),
                Deformation.matrixRepresentation ρ σ v ∈ Representation.invariants
                  ((Deformation.matrixRepresentation ρ).comp (A.inertiaSubgroupIn ℚ).subtype),
              ModularFormClass.qCoeff g ℓ =
                LinearMap.trace ℂ _ ((Deformation.matrixRepresentation ρ σ).restrict hσ)) ∧
    (∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ M →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        Module.finrank ℂ (Representation.invariants
            ((Deformation.matrixRepresentation ρ).comp (A.inertiaSubgroupIn ℚ).subtype)) < 2 ∧
        ∀ σ : Γℚ, A.IsFrobeniusAt σ ℓ →
          ∃ hσ : ∀ v ∈ Representation.invariants
                ((Deformation.matrixRepresentation ρ).comp (A.inertiaSubgroupIn ℚ).subtype),
              Deformation.matrixRepresentation ρ σ v ∈ Representation.invariants
                ((Deformation.matrixRepresentation ρ).comp (A.inertiaSubgroupIn ℚ).subtype),
            ModularFormClass.qCoeff g ℓ =
              LinearMap.trace ℂ _ ((Deformation.matrixRepresentation ρ σ).restrict hσ)) := by
  classical

  set b : ℕ → ℂ := fun n => ModularFormClass.qCoeff g n with hb
  set e : ℕ → ℂ := fun p => if p ∣ M then 0 else ε (p : ZMod M) with he
  have hM0 : M ≠ 0 := NeZero.ne M

  have heig : FormalHecke.IsEigensystem e b := by
    refine ⟨hg₁, fun ℓ hℓ n => ?_⟩
    by_cases hℓM : ℓ ∣ M
    · simp only [he, hb, if_pos hℓM, zero_mul, add_zero]
      exact hU ℓ hℓ hℓM n
    · simp only [he, hb, if_neg hℓM]
      exact hT ℓ hℓ hℓM n
  have hrec : FormalHecke.IsRecursive e b := FormalHecke.IsEigensystem.isRecursive heig
  have hb₁ : b 1 = 1 := hrec.1
  have hbmul : ∀ m n : ℕ, m.Coprime n → b (m * n) = b m * b n := hrec.2.1
  set Q : ℕ → ℂ[X] := fun p => eulerPoly (b p) (e p) with hQdef
  have hQ : ∀ p : ℕ, p.Prime → (Q p : PowerSeries ℂ) * PowerSeries.mk (fun k => b (p ^ k)) = 1 :=
    fun p hp => eulerPoly_mul_mk_eq_one hrec hp
  set a : ℕ → ℂ := ArtinL.coeff ρ with ha
  set P : ℕ → ℂ[X] := ArtinL.eulerFactor ρ with hPdef
  have hP : ∀ p : ℕ, p.Prime → (P p : PowerSeries ℂ) * PowerSeries.mk (fun k => a (p ^ k)) = 1 :=
    fun p hp => eulerFactor_mul_mk_eq_one ρ hp

  obtain ⟨Sram, hSram⟩ :=
    GlobalGaloisRep.exists_finset_forall_isUnramifiedAt_of_isOpen_ker ρ (isOpen_ker hρ)
  have hcond0 : ArtinL.conductor ρ ≠ 0 := by
    rw [ArtinL.conductor]
    refine finprod_induction (fun x : ℕ => x ≠ 0) one_ne_zero (fun _ _ => mul_ne_zero) fun p => ?_
    by_cases hp : p = 0
    · subst hp
      have : ArtinL.conductorExponent ρ 0 = 0 := by
        rw [ArtinL.conductorExponent, dif_neg]
        exact fun h => Nat.not_prime_zero h.1
      rw [this, pow_zero]; exact one_ne_zero
    · exact pow_ne_zero _ hp
  set S : Finset ℕ := (M * N₀ * ArtinL.conductor ρ).primeFactors ∪ Sram.filter Nat.Prime with hSdef
  have hS : ∀ p ∈ S, p.Prime := by
    intro p hp
    rcases Finset.mem_union.mp hp with h | h
    · exact Nat.prime_of_mem_primeFactors h
    · exact (Finset.mem_filter.mp h).2

  have hMN0 : M * N₀ * ArtinL.conductor ρ ≠ 0 := mul_ne_zero (mul_ne_zero hM0 hN₀) hcond0
  have hnotS : ∀ p : ℕ, p.Prime → p ∉ S →
      ¬ p ∣ M ∧ ¬ p ∣ N₀ ∧ GlobalGaloisRep.IsUnramifiedAt ρ p := by
    intro p hp hpS
    have h1 : ¬ p ∣ M * N₀ * ArtinL.conductor ρ := fun h =>
      hpS (Finset.mem_union_left _ (Nat.mem_primeFactors.mpr ⟨hp, h, hMN0⟩))
    refine ⟨fun h => h1 (h.trans ((dvd_mul_right M N₀).trans (dvd_mul_right _ _))),
      fun h => h1 (h.trans ((dvd_mul_left N₀ M).trans (dvd_mul_right _ _))), ?_⟩
    exact hSram p hp fun h => hpS (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨h, hp⟩))

  have hPunr : ∀ p : ℕ, p.Prime → GlobalGaloisRep.IsUnramifiedAt ρ p →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
        ∀ σ : Γℚ, A.IsFrobeniusAt σ p →
          P p = 1 - C ((ρ σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).trace * X +
            C ((ρ σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det * X ^ 2 := by
    intro p hp hunr A hA σ hσ
    have htop : ArtinL.inertiaInvariants ρ A = ⊤ :=
      inertiaInvariants_eq_top_of_le_ker ρ A (hunr A hA)
    rw [hPdef, ← (ArtinL.eulerFactorAt_eq_eulerFactor ρ hp A hA σ hσ).2,
      eulerFactorAt_eq_of_top ρ A htop σ, Matrix.charpolyRev_fin_two]
  have hPQ : ∀ p : ℕ, p.Prime → p ∉ S → P p = Q p := by
    intro p hp hpS
    obtain ⟨hpM, hpN₀, hunr⟩ := hnotS p hp hpS
    obtain ⟨A, σ, hA, hσ⟩ := ValuationSubring.exists_liesOverPrime_isFrobeniusAt_ratAlgClosure ⟨p, hp⟩
    obtain ⟨htr, hdet⟩ := hρg p hp hpN₀ A hA σ hσ
    rw [hPunr p hp hunr A hA σ hσ, hQdef]
    simp only [eulerPoly, he, hb, if_neg hpM, htr, hdet]

  obtain ⟨Λg, Λg', σ₀, hΛg, hΛg', hMellin, hFEg⟩ :=
    CuspForm.exists_weightOne_completedLSeries_functionalEquation_of_fricke M g g' c hc hW

  obtain ⟨W, Λ₁, Λ₂, Λ₁', Λ₂', hW0, hΛ₁, hΛ₂, hΛ₁', hΛ₂', hArtin, hFE₁, hFE₂⟩ :=
    ArtinL.exists_completedLSeries_functionalEquation_of_odd ρ hρ hodd
  set G : ℂ → ℂ := fun s => (((2 * Real.pi)⁻¹ : ℝ) : ℂ) ^ s * Complex.Gamma s with hGdef
  set σ₁ : ℝ := max σ₀ 2 with hσ₁
  have hσ₁σ₀ : σ₀ ≤ σ₁ := le_max_left _ _
  have hσ₁2 : (2 : ℝ) ≤ σ₁ := le_max_right _ _
  have hG : ∀ s : ℝ, σ₁ < s → G s ≠ 0 := by
    intro s hs
    have hs0 : (0 : ℝ) < s := by linarith
    refine mul_ne_zero ?_ (Complex.Gamma_ne_zero_of_re_pos (by simpa using hs0))
    rw [Complex.cpow_ne_zero_iff]
    left
    exact_mod_cast (inv_pos.mpr (by positivity : (0 : ℝ) < 2 * Real.pi)).ne'
  have hre : ∀ s : ℝ, σ₁ < s → σ₀ < (s : ℂ).re ∧ 1 < (s : ℂ).re := fun s hs =>
    ⟨by rw [Complex.ofReal_re]; linarith, by rw [Complex.ofReal_re]; linarith⟩
  have hsum : ∀ s : ℝ, σ₁ < s → LSeriesSummable a s ∧ LSeriesSummable b s := fun s hs =>
    ⟨(hArtin s (hre s hs).2).1, (hMellin s (hre s hs).1).1⟩
  set wb : ℂ := c * Complex.I / (Real.sqrt M : ℂ) with hwbdef
  have hsqrtM : (Real.sqrt M : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt M := Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero hM0)
    exact_mod_cast this.ne'
  have hwb : wb ≠ 0 := div_ne_zero (mul_ne_zero hc Complex.I_ne_zero) hsqrtM
  have hg'b : (fun n => ModularFormClass.qCoeff g' n) = fun n => starRingEnd ℂ (b n) :=
    funext fun n => hg' n
  have hΛa : ∀ s : ℝ, σ₁ < s →
      Λ₂ s ≠ 0 ∧ Λ₂' s ≠ 0 ∧
      Λ₁ s = Λ₂ s * (((Real.sqrt (ArtinL.conductor ρ) : ℝ) : ℂ) ^ (s : ℂ) * G s * LSeries a s) ∧
      Λ₁' s = Λ₂' s * (((Real.sqrt (ArtinL.conductor ρ) : ℝ) : ℂ) ^ (s : ℂ) * G s *
        LSeries (fun m => starRingEnd ℂ (a m)) s) := by
    intro s hs
    obtain ⟨-, h2, h2', h1, h1'⟩ := hArtin s (hre s hs).2
    refine ⟨h2, h2', ?_, ?_⟩
    · rw [h1, sqrt_div_two_pi_cpow]; ring
    · rw [h1', sqrt_div_two_pi_cpow]; ring
  have hΛb : ∀ s : ℝ, σ₁ < s →
      (fun _ : ℂ => (1 : ℂ)) s ≠ 0 ∧ (fun _ : ℂ => (1 : ℂ)) s ≠ 0 ∧
      Λg s = (fun _ : ℂ => (1 : ℂ)) s * (((Real.sqrt M : ℝ) : ℂ) ^ (s : ℂ) * G s * LSeries b s) ∧
      Λg' s = (fun _ : ℂ => (1 : ℂ)) s * (((Real.sqrt M : ℝ) : ℂ) ^ (s : ℂ) * G s *
        LSeries (fun m => starRingEnd ℂ (b m)) s) := by
    intro s hs
    obtain ⟨-, -, h1, h1'⟩ := hMellin s (hre s hs).1
    refine ⟨one_ne_zero, one_ne_zero, ?_, ?_⟩
    · rw [h1, sqrt_div_two_pi_cpow]; simp only [one_mul]; ring
    · rw [h1', hg'b, sqrt_div_two_pi_cpow]; simp only [one_mul]; ring
  have hFEb : ∀ s : ℂ, Λg (1 - s) = wb * Λg' s := by
    intro s
    rw [hFEg (1 - s), sub_sub_cancel]

  have hProots : ∀ p ∈ S, ∀ z : ℂ, (P p).IsRoot z → ‖z‖ = 1 := by
    intro p hpS z hz
    have hp := hS p hpS
    obtain ⟨A, σ, hA, hσ⟩ := ValuationSubring.exists_liesOverPrime_isFrobeniusAt_ratAlgClosure ⟨p, hp⟩
    obtain ⟨hst, hfac⟩ := ArtinL.eulerFactorAt_eq_eulerFactor ρ hp A hA σ hσ
    obtain ⟨d, hd, hσd⟩ := exists_pow_eq_one hρ σ
    have hTd : (Deformation.matrixRepresentation ρ σ) ^ d = 1 := by
      have h1 : ρ (σ ^ d) = 1 := by rw [map_pow, hσd]
      rw [← map_pow, Deformation.matrixRepresentation_apply, h1]
      simp only [Units.val_one, Matrix.mulVecLin_one]
      rfl
    have hRd : ((Deformation.matrixRepresentation ρ σ).restrict hst) ^ d = 1 := by
      rw [Module.End.pow_restrict d hst]
      refine LinearMap.ext fun v => Subtype.ext ?_
      rw [LinearMap.coe_restrict_apply, hTd]
      rfl
    have hz' : (ArtinL.charpolyRev ((Deformation.matrixRepresentation ρ σ).restrict hst)).IsRoot z := by
      have : P p = ArtinL.charpolyRev ((Deformation.matrixRepresentation ρ σ).restrict hst) := by
        rw [hPdef, ← hfac, ArtinL.eulerFactorAt, dif_pos hst]
      rwa [this] at hz
    exact norm_eq_one_of_isRoot_charpolyRev _ hd hRd hz'

  have hQroots : ∀ p ∈ S,
      (∀ z : ℂ, (Q p).IsRoot z → 1 < ‖z‖ ^ 2 * p) ∨
        ((Q p).natDegree ≤ 2 ∧ ‖(Q p).coeff 2‖ = 1) := by
    intro p hpS
    have hp := hS p hpS
    by_cases hpM : p ∣ M
    · left
      intro z hz
      have hQp : Q p = eulerPoly (b p) 0 := by simp only [hQdef, he, if_pos hpM]
      rw [hQp] at hz
      exact roots_large_of_norm_le_one (hLi p hp hpM) hp hz
    · right
      refine ⟨natDegree_eulerPoly_le _ _, ?_⟩
      rw [hQdef]
      simp only [coeff_eulerPoly_two, he, if_neg hpM]
      exact norm_dirichlet_prime_eq_one ε hp hpM
  have hMS : ∀ p : ℕ, p.Prime → p ∣ ArtinL.conductor ρ * M → p ∈ S := by
    intro p hp hdvd
    refine Finset.mem_union_left _ (Nat.mem_primeFactors.mpr ⟨hp, ?_, hMN0⟩)
    exact hdvd.trans ⟨N₀, by ring⟩

  obtain ⟨hcondM, hSeq⟩ :=
    DeligneSerre.eq_of_eulerProduct_completedLSeries_functionalEquation S hS a b
      (ArtinL.coeff_one ρ) hb₁ (fun m n h => coeff_mul_of_coprime ρ h) hbmul P Q hP hQ hPQ
      hProots hQroots (ArtinL.conductor ρ) M hcond0 hM0 hMS G σ₁ hG hsum W wb hW0 hwb
      Λ₁ Λ₂ Λ₁' Λ₂' Λg (fun _ => 1) Λg' (fun _ => 1) hΛ₁ hΛ₂ hΛ₁' hΛ₂' hΛg
      (differentiable_const _) hΛg' (differentiable_const _) hΛa hΛb hFE₁ hFE₂ hFEb
      (fun _ => rfl)
  have hall : ∀ p : ℕ, p.Prime → P p = Q p := fun p hp => by
    by_cases hpS : p ∈ S
    · exact hSeq p hpS
    · exact hPQ p hp hpS

  have hAt : ∀ p : ℕ, p.Prime → ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
      ∀ σ : Γℚ, A.IsFrobeniusAt σ p →
        ∃ hσ : ∀ v ∈ ArtinL.inertiaInvariants ρ A,
            Deformation.matrixRepresentation ρ σ v ∈ ArtinL.inertiaInvariants ρ A,
          (Q p).natDegree ≤ Module.finrank ℂ (ArtinL.inertiaInvariants ρ A) ∧
          b p = LinearMap.trace ℂ _ ((Deformation.matrixRepresentation ρ σ).restrict hσ) := by
    intro p hp A hA σ hσ
    obtain ⟨hst, hfac⟩ := ArtinL.eulerFactorAt_eq_eulerFactor ρ hp A hA σ hσ
    obtain ⟨_, hdeg, hc1⟩ := eulerFactorAt_of_stable ρ A σ hst
    have hQeq : Q p = ArtinL.eulerFactorAt ρ A σ := by rw [hfac, ← hall p hp]
    refine ⟨hst, hQeq ▸ hdeg, ?_⟩
    have h1 : (Q p).coeff 1 = -b p := by rw [hQdef]; exact coeff_eulerPoly_one _ _
    rw [hQeq, hc1, neg_inj] at h1
    exact h1.symm
  have hfin2 : Module.finrank ℂ (Fin 2 → ℂ) = 2 := Module.finrank_fin_fun ℂ
  have hle2 : ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      Module.finrank ℂ (ArtinL.inertiaInvariants ρ A) ≤ 2 := fun A =>
    (Submodule.finrank_le _).trans hfin2.le

  have hC1 : ∀ p : ℕ, p.Prime → ¬ p ∣ M →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
        (∀ σ ∈ A.inertiaSubgroupIn ℚ, ρ σ = 1) ∧
        ∀ σ : Γℚ, A.IsFrobeniusAt σ p →
          ModularFormClass.qCoeff g p =
              ((ρ σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).trace ∧
          ε (p : ZMod M) = ((ρ σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det := by
    intro p hp hpM A hA
    have hεp : ε (p : ZMod M) ≠ 0 := by
      intro h0
      have := norm_dirichlet_prime_eq_one ε hp hpM
      rw [h0, norm_zero] at this
      exact zero_ne_one this
    have hQp : Q p = eulerPoly (b p) (ε (p : ZMod M)) := by simp only [hQdef, he, if_neg hpM]
    have hdegQ : (Q p).natDegree = 2 := by rw [hQp]; exact natDegree_eulerPoly_of_ne_zero _ hεp

    obtain ⟨σ₀', hσ₀'⟩ := ValuationSubring.exists_isFrobeniusAt_of_liesOverPrime hp A hA
    obtain ⟨hst₀, hdeg₀, -⟩ := hAt p hp A hA σ₀' hσ₀'
    have htop : ArtinL.inertiaInvariants ρ A = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [hfin2]
      exact le_antisymm (hle2 A) (hdegQ.ge.trans hdeg₀)
    refine ⟨fun σ hσ => apply_eq_one_of_inertiaInvariants_eq_top ρ A htop hσ, fun σ hσ => ?_⟩
    have hfac := (ArtinL.eulerFactorAt_eq_eulerFactor ρ hp A hA σ hσ).2
    have hQσ : Q p = 1 - C ((ρ σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).trace * X +
        C ((ρ σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det * X ^ 2 := by
      rw [← hall p hp, hPdef, ← hfac, eulerFactorAt_eq_of_top ρ A htop σ, Matrix.charpolyRev_fin_two]
    have h1 := congrArg (fun q : ℂ[X] => q.coeff 1) hQσ
    have h2 := congrArg (fun q : ℂ[X] => q.coeff 2) hQσ
    simp only [hQp, coeff_eulerPoly_one, coeff_eulerPoly_two] at h1 h2
    rw [show (1 - C ((ρ σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).trace * X +
        C ((ρ σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det * X ^ 2 : ℂ[X]) =
        eulerPoly ((ρ σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).trace
          ((ρ σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det from rfl,
      coeff_eulerPoly_one] at h1
    rw [show (1 - C ((ρ σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).trace * X +
        C ((ρ σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det * X ^ 2 : ℂ[X]) =
        eulerPoly ((ρ σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).trace
          ((ρ σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det from rfl,
      coeff_eulerPoly_two] at h2
    exact ⟨neg_injective h1, h2⟩

  have hexp0 : ∀ p : ℕ, p.Prime → p ∉ S → ArtinL.conductorExponent ρ p = 0 := by
    intro p hp hpS
    obtain ⟨-, -, hunr⟩ := hnotS p hp hpS
    obtain ⟨A, -, hA, -⟩ := ValuationSubring.exists_liesOverPrime_isFrobeniusAt_ratAlgClosure ⟨p, hp⟩
    have htop : ArtinL.inertiaInvariants ρ A = ⊤ := inertiaInvariants_eq_top_of_le_ker ρ A (hunr A hA)
    have hbot : (A.inertiaSubgroupIn ℚ).map ρ = ⊥ := by
      rw [Subgroup.map_eq_bot_iff]
      exact hunr A hA
    have htame : (Nat.card ((A.inertiaSubgroupIn ℚ).map ρ)).Coprime p := by
      rw [hbot, Subgroup.card_bot]
      exact Nat.coprime_one_left p
    have h := ArtinL.conductorExponent_add_finrank_inertiaInvariants_eq ρ hρ hp A hA htame
    rw [htop, finrank_top, hfin2] at h
    omega
  have hfact : ∀ ℓ : ℕ, ℓ.Prime → (ArtinL.conductor ρ).factorization ℓ = ArtinL.conductorExponent ρ ℓ := by
    intro ℓ hℓ
    have hsupp : (Function.mulSupport fun p : ℕ => p ^ ArtinL.conductorExponent ρ p) ⊆ (S : Set ℕ) := by
      intro p hp
      rw [Function.mem_mulSupport] at hp
      by_contra hpS
      apply hp
      by_cases hpr : p.Prime
      · rw [hexp0 p hpr hpS, pow_zero]
      · have : ArtinL.conductorExponent ρ p = 0 := by
          rw [ArtinL.conductorExponent, dif_neg]
          exact fun h => hpr h.1
        rw [this, pow_zero]
    have hprod : ArtinL.conductor ρ = ∏ p ∈ S, p ^ ArtinL.conductorExponent ρ p := by
      rw [ArtinL.conductor]
      exact finprod_eq_prod_of_mulSupport_subset _ hsupp
    rw [hprod, Nat.factorization_prod fun p hp => pow_ne_zero _ (hS p hp).ne_zero]
    simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Nat.factorization_pow]
    have hterm : ∀ p ∈ S, (ArtinL.conductorExponent ρ p • p.factorization) ℓ =
        if p = ℓ then ArtinL.conductorExponent ρ ℓ else 0 := by
      intro p hp
      rw [Finsupp.smul_apply, (hS p hp).factorization, Finsupp.single_apply, smul_eq_mul]
      by_cases hpl : p = ℓ
      · subst hpl; simp
      · simp [hpl]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' S ℓ]
    by_cases hℓS : ℓ ∈ S
    · rw [if_pos hℓS]
    · rw [if_neg hℓS, hexp0 ℓ hℓ hℓS]
  refine ⟨hC1, ?_, ?_⟩
  ·
    intro ℓ hℓ A hA htame
    have hex := ArtinL.conductorExponent_add_finrank_inertiaInvariants_eq ρ hρ hℓ A hA htame
    refine ⟨?_, fun σ hσ => ?_⟩
    · rw [← hcondM, hfact ℓ hℓ]
      exact hex
    · obtain ⟨hst, -, htr⟩ := hAt ℓ hℓ A hA σ hσ
      exact ⟨hst, htr⟩
  ·
    intro ℓ hℓ hℓM A hA
    have hQℓ : Q ℓ = eulerPoly (b ℓ) 0 := by simp only [hQdef, he, if_pos hℓM]
    have hdegQ : (Q ℓ).natDegree ≤ 1 := by rw [hQℓ]; exact natDegree_eulerPoly_zero_le _
    obtain ⟨σ₀', hσ₀'⟩ := ValuationSubring.exists_isFrobeniusAt_of_liesOverPrime hℓ A hA
    refine ⟨?_, fun σ hσ => ?_⟩
    · by_contra hge
      have h2 : Module.finrank ℂ (ArtinL.inertiaInvariants ρ A) = 2 :=
        le_antisymm (hle2 A) (not_lt.mp hge)
      have htop : ArtinL.inertiaInvariants ρ A = ⊤ := by
        apply Submodule.eq_top_of_finrank_eq
        rw [hfin2]; exact h2
      have hfac := (ArtinL.eulerFactorAt_eq_eulerFactor ρ hℓ A hA σ₀' hσ₀').2
      have hQσ : Q ℓ = eulerPoly ((ρ σ₀' : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).trace
          ((ρ σ₀' : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det := by
        rw [← hall ℓ hℓ, hPdef, ← hfac, eulerFactorAt_eq_of_top ρ A htop σ₀', Matrix.charpolyRev_fin_two]
        rfl
      have hdet : ((ρ σ₀' : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det ≠ 0 :=
        ((ρ σ₀' : GL (Fin 2) ℂ).isUnit.map Matrix.detMonoidHom).ne_zero
      have : (Q ℓ).natDegree = 2 := by rw [hQσ]; exact natDegree_eulerPoly_of_ne_zero _ hdet
      omega
    · obtain ⟨hst, -, htr⟩ := hAt ℓ hℓ A hA σ hσ
      exact ⟨hst, htr⟩

end
p2m_reactivate "P2MW.S_DeligneSerre_eulerFactor_eq_and_tameLevel_of_weightOne_newform_qCoeff_eq_trace.DeligneSerreDS46c"

end S_DeligneSerre_eulerFactor_eq_and_tameLevel_of_weightOne_newform_qCoeff_eq_trace
end P2MW
export P2MW.S_DeligneSerre_eulerFactor_eq_and_tameLevel_of_weightOne_newform_qCoeff_eq_trace (solution)
