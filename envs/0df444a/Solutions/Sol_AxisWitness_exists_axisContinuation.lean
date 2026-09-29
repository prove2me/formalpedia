-- Prove2me | solution 1 for AxisWitness.exists_axisContinuation
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/5fca332b-be01-5d1a-ab7e-58cb4621f346

import Mathlib
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_ConstantTerm
import Theorems.Thm_AutomorphicForm_exists_analyticOnNhd_axis_continuation_bruhatEisenstein_weylIntertwiningIntegral_of_isArchKFinite_family
import Theorems.Thm_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half
import Theorems.Thm_AutomorphicForm_constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AxisWitness_exists_axisContinuation
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra"
p2m_attr_erase "instance" "HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions"
p2m_attr_erase "simp" "AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply"
p2m_attr_erase "simp" "AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add LocalGL2.swapUnit_val"
p2m_attr_erase "simp" "M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq"
p2m_attr_erase "simp" "AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one AutomorphicForm.rightTranslationEmbed_smul_apply LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply"
p2m_attr_erase "simp" "RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22LocalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_right ContinuousAddEquiv.preimage_mulLeft_smul"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar NumberField.AdelicBox IsDedekindDomain
p2m_open "AutomorphicForm~continuous_unipotentGL2 Matrix Filter Topology"
open scoped ComplexConjugate NNReal ENNReal Pointwise

namespace AxisContAssemblyA

section Unipotent

variable {A : Type*} [CommRing A]

theorem unipotentGL2_inv (x : A) : (unipotentGL2 x)⁻¹ = unipotentGL2 (-x) :=
  inv_eq_of_mul_eq_one_right (by rw [← unipotentGL2_add, add_neg_cancel, unipotentGL2_zero])

theorem borel_entry (b : GL (Fin 2) A) (hb : b ∈ borelSubgroup A) :
    (b : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := hb

end Unipotent

section Bruhat

variable {K : Type*} [Field K]

theorem borel_fst_ne_zero (b : GL (Fin 2) K) (hb : b ∈ borelSubgroup K) :
    (b : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 := by
  have hb' : (b : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := hb
  intro h0
  have hdet : (b : Matrix (Fin 2) (Fin 2) K).det = 0 := by
    rw [Matrix.det_fin_two, hb', h0]; ring
  apply (Matrix.GeneralLinearGroup.det b).ne_zero
  rw [Matrix.GeneralLinearGroup.val_det_apply, hdet]

theorem weyl_unipotent_borel_mem (b : GL (Fin 2) K) (hb : b ∈ borelSubgroup K) (ξ : K) :
    gl2Weyl * unipotentGL2 ξ * b
      * unipotentGL2 (-(((b : Matrix (Fin 2) (Fin 2) K) 0 0)⁻¹
          * ((b : Matrix (Fin 2) (Fin 2) K) 0 1 + ξ * (b : Matrix (Fin 2) (Fin 2) K) 1 1)))
      * gl2Weyl ∈ borelSubgroup K := by
  have hb' : (b : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := hb
  have ha : (b : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 := borel_fst_ne_zero b hb
  show ((_ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
  simp only [Matrix.GeneralLinearGroup.coe_mul, gl2Weyl_val, unipotentGL2_coe]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    hb']
  field_simp
  ring

theorem bigCell_borel_mem (γ : GL (Fin 2) K) (hc : (γ : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0) :
    γ * unipotentGL2 (-(((γ : Matrix (Fin 2) (Fin 2) K) 1 0)⁻¹ * (γ : Matrix (Fin 2) (Fin 2) K) 1 1))
      * gl2Weyl ∈ borelSubgroup K := by
  show ((_ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
  simp only [Matrix.GeneralLinearGroup.coe_mul, gl2Weyl_val, unipotentGL2_coe]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  field_simp
  ring

theorem weyl_unipotent_weyl_mem (ξ : K) (hξ : ξ ≠ 0) :
    gl2Weyl * unipotentGL2 ξ * gl2Weyl * unipotentGL2 (-ξ⁻¹) * gl2Weyl ∈ borelSubgroup K := by
  show ((_ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
  simp only [Matrix.GeneralLinearGroup.coe_mul, gl2Weyl_val, unipotentGL2_coe]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  field_simp
  ring

theorem gl2Weyl_mul_gl2Weyl : (gl2Weyl : GL (Fin 2) K) * gl2Weyl = 1 := by
  conv_lhs => rw [← gl2Weyl_inv (K := K)]
  exact inv_mul_cancel _

end Bruhat

end AxisContAssemblyA

namespace AxisContAssemblyA

section Eisenstein

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

theorem borel_snd_ne_zero (b : GL (Fin 2) K) (hb : b ∈ borelSubgroup K) :
    (b : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 0 := by
  have hb' : (b : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := hb
  intro h0
  have hdet : (b : Matrix (Fin 2) (Fin 2) K).det = 0 := by
    rw [Matrix.det_fin_two, hb', h0]; ring
  apply (Matrix.GeneralLinearGroup.det b).ne_zero
  rw [Matrix.GeneralLinearGroup.val_det_apply, hdet]

theorem globalPoints_unipotentGL2 (ξ : K) :
    globalPoints R K (unipotentGL2 ξ) = unipotentGL2 (algebraMap K (AdeleRing R K) ξ) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [globalPoints_apply, unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

theorem globalPoints_gl2Weyl : globalPoints R K gl2Weyl = adelicWeyl R K := rfl

noncomputable def eis (φ : AdelicGL2 R K → ℂ) (g : AdelicGL2 R K) : ℂ :=
  φ g + ∑' ξ : K, φ (adelicWeyl R K * unipotentGL2 (algebraMap K (AdeleRing R K) ξ) * g)

variable (φ : AdelicGL2 R K → ℂ)
  (hB : ∀ b ∈ borelSubgroup K, ∀ g : AdelicGL2 R K, φ (globalPoints R K b * g) = φ g)

include hB

theorem eis_borel_mul (b : GL (Fin 2) K) (hb : b ∈ borelSubgroup K) (g : AdelicGL2 R K) :
    eis φ (globalPoints R K b * g) = eis φ g := by
  unfold eis
  congr 1
  · exact hB b hb g
  · set a := (b : Matrix (Fin 2) (Fin 2) K) 0 0 with ha_def
    set e := (b : Matrix (Fin 2) (Fin 2) K) 0 1 with he_def
    set d := (b : Matrix (Fin 2) (Fin 2) K) 1 1 with hd_def
    have ha : a ≠ 0 := borel_fst_ne_zero b hb
    have hd : d ≠ 0 := borel_snd_ne_zero b hb
    have had : a⁻¹ * d ≠ 0 := mul_ne_zero (inv_ne_zero ha) hd

    let σ : K ≃ K := (Equiv.mulRight₀ (a⁻¹ * d) had).trans (Equiv.addRight (a⁻¹ * e))
    have hσ : ∀ ξ : K, σ ξ = a⁻¹ * (e + ξ * d) := by
      intro ξ
      show ξ * (a⁻¹ * d) + a⁻¹ * e = a⁻¹ * (e + ξ * d)
      ring
    have hterm : ∀ ξ : K,
        φ (adelicWeyl R K * unipotentGL2 (algebraMap K (AdeleRing R K) ξ) * (globalPoints R K b * g))
          = φ (adelicWeyl R K * unipotentGL2 (algebraMap K (AdeleRing R K) (σ ξ)) * g) := by
      intro ξ
      have hmem := weyl_unipotent_borel_mem b hb ξ
      set T := gl2Weyl * unipotentGL2 ξ * b * unipotentGL2 (-(a⁻¹ * (e + ξ * d))) * gl2Weyl
        with hT
      have hprod : gl2Weyl * unipotentGL2 ξ * b = T * gl2Weyl * unipotentGL2 (a⁻¹ * (e + ξ * d)) := by
        rw [hT]
        simp only [mul_assoc]
        rw [← mul_assoc gl2Weyl gl2Weyl _, gl2Weyl_mul_gl2Weyl, one_mul, ← unipotentGL2_add,
          neg_add_cancel, unipotentGL2_zero, mul_one]
      have hA : adelicWeyl R K * unipotentGL2 (algebraMap K (AdeleRing R K) ξ) * (globalPoints R K b * g)
          = globalPoints R K T * (adelicWeyl R K
              * unipotentGL2 (algebraMap K (AdeleRing R K) (σ ξ)) * g) := by
        rw [hσ ξ, ← globalPoints_unipotentGL2, ← globalPoints_unipotentGL2, ← globalPoints_gl2Weyl,
          ← map_mul, ← mul_assoc, ← map_mul, hprod, map_mul, map_mul]
        simp only [mul_assoc]
      rw [hA, hB T hmem]
    simp_rw [hterm]
    exact σ.tsum_eq (fun ξ => φ (adelicWeyl R K * unipotentGL2 (algebraMap K (AdeleRing R K) ξ) * g))

variable (hS : ∀ g : AdelicGL2 R K,
    Summable (fun ξ : K => φ (adelicWeyl R K * unipotentGL2 (algebraMap K (AdeleRing R K) ξ) * g)))

include hS

open scoped Classical in

theorem eis_weyl_mul (g : AdelicGL2 R K) : eis φ (adelicWeyl R K * g) = eis φ g := by
  unfold eis
  set W := adelicWeyl R K with hW
  let fa : K → ℂ := fun ξ => φ (W * unipotentGL2 (algebraMap K (AdeleRing R K) ξ) * (W * g))
  let fb : K → ℂ := fun ξ => φ (W * unipotentGL2 (algebraMap K (AdeleRing R K) ξ) * g)
  have hWW : W * W = 1 := by
    rw [hW, ← globalPoints_gl2Weyl, ← map_mul, gl2Weyl_mul_gl2Weyl, map_one]
  have ha0 : fa 0 = φ g := by
    show φ (W * unipotentGL2 (algebraMap K (AdeleRing R K) 0) * (W * g)) = φ g
    rw [map_zero, unipotentGL2_zero, mul_one, ← mul_assoc, hWW, one_mul]
  have hb0 : fb 0 = φ (W * g) := by
    show φ (W * unipotentGL2 (algebraMap K (AdeleRing R K) 0) * g) = φ (W * g)
    rw [map_zero, unipotentGL2_zero, mul_one]
  have hab : ∀ ξ : K, ξ ≠ 0 → fa ξ = fb ξ⁻¹ := by
    intro ξ hξ
    have hmem := weyl_unipotent_weyl_mem ξ hξ
    set T := gl2Weyl * unipotentGL2 ξ * gl2Weyl * unipotentGL2 (-ξ⁻¹) * gl2Weyl with hT
    have hprod : gl2Weyl * unipotentGL2 ξ * gl2Weyl = T * gl2Weyl * unipotentGL2 ξ⁻¹ := by
      rw [hT]
      simp only [mul_assoc]
      rw [← mul_assoc gl2Weyl gl2Weyl _, gl2Weyl_mul_gl2Weyl, one_mul, ← unipotentGL2_add,
        neg_add_cancel, unipotentGL2_zero, mul_one]
    show φ (W * unipotentGL2 (algebraMap K (AdeleRing R K) ξ) * (W * g))
      = φ (W * unipotentGL2 (algebraMap K (AdeleRing R K) ξ⁻¹) * g)
    have hA : W * unipotentGL2 (algebraMap K (AdeleRing R K) ξ) * (W * g)
        = globalPoints R K T * (W * unipotentGL2 (algebraMap K (AdeleRing R K) ξ⁻¹) * g) := by
      rw [hW, ← globalPoints_unipotentGL2, ← globalPoints_unipotentGL2, ← globalPoints_gl2Weyl,
        ← map_mul, ← mul_assoc, ← map_mul, hprod, map_mul, map_mul]
      simp only [mul_assoc]
    rw [hA, hB T hmem]
  have hSa : Summable fa := hS (W * g)
  have hSb : Summable fb := hS g
  change φ (W * g) + ∑' ξ, fa ξ = φ g + ∑' ξ, fb ξ
  rw [hSa.tsum_eq_add_tsum_ite 0, hSb.tsum_eq_add_tsum_ite 0, ha0, hb0]
  have hre : ∑' ξ : K, (if ξ = 0 then 0 else fa ξ) = ∑' ξ : K, (if ξ = 0 then 0 else fb ξ) := by
    have h1 : (fun ξ : K => if ξ = 0 then 0 else fa ξ)
        = fun ξ : K => (fun η : K => if η = 0 then 0 else fb η) (Equiv.inv K ξ) := by
      funext ξ
      by_cases hξ : ξ = 0
      · simp [hξ]
      · simp only [Equiv.inv_apply, inv_eq_zero, hξ, if_false]
        exact hab ξ hξ
    rw [h1]
    exact (Equiv.inv K).tsum_eq (fun η : K => if η = 0 then 0 else fb η)
  rw [hre]
  ring

theorem eis_globalPoints_mul (γ : GL (Fin 2) K) (g : AdelicGL2 R K) :
    eis φ (globalPoints R K γ * g) = eis φ g := by
  by_cases hc : (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
  · exact eis_borel_mul φ hB γ hc g
  · have hmem := bigCell_borel_mem γ hc
    set β : K := ((γ : Matrix (Fin 2) (Fin 2) K) 1 0)⁻¹ * (γ : Matrix (Fin 2) (Fin 2) K) 1 1 with hβ
    set bγ := γ * unipotentGL2 (-β) * gl2Weyl with hbγ
    have hγ : γ = bγ * gl2Weyl * unipotentGL2 β := by
      rw [hbγ]
      simp only [mul_assoc]
      rw [← mul_assoc gl2Weyl gl2Weyl _, gl2Weyl_mul_gl2Weyl, one_mul, ← unipotentGL2_add,
        neg_add_cancel, unipotentGL2_zero, mul_one]
    rw [hγ, map_mul, map_mul, mul_assoc, mul_assoc, eis_borel_mul φ hB bγ hmem,
      globalPoints_gl2Weyl, eis_weyl_mul φ hB hS,
      eis_borel_mul φ hB _ (unipotentGL2_mem_borelSubgroup β)]

end Eisenstein

end AxisContAssemblyA

namespace AxisContAssemblyB

section HaarSubst

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [LocallyCompactSpace A]
  [MeasurableSpace A] [BorelSpace A]

theorem integral_comp_units_smul (μ : Measure A) [μ.IsAddHaarMeasure] [μ.Regular]
    (u : Aˣ) (F : A → ℂ) :
    ∫ x, F (u • x) ∂μ = ((distribHaarChar A u : ℝ≥0) : ℝ)⁻¹ • ∫ x, F x ∂μ := by
  have hmap : μ.map (fun x : A => u • x) = (distribHaarChar A u⁻¹) • μ := by
    ext s hs
    rw [Measure.map_apply (measurable_const_smul (u : Aˣ)) hs, Set.preimage_smul,
      Measure.smul_apply, ← distribHaarChar_mul μ u⁻¹ s]
    rfl
  have h1 : ∫ x, F (u • x) ∂μ = ∫ y, F y ∂(μ.map (fun x : A => u • x)) :=
    ((MeasurableEquiv.smul (u : Aˣ)).measurableEmbedding.integral_map F).symm
  rw [h1, hmap, integral_smul_nnreal_measure, map_inv, NNReal.smul_def, NNReal.coe_inv]

theorem integral_comp_add_units_smul (μ : Measure A) [μ.IsAddHaarMeasure] [μ.Regular]
    (u : Aˣ) (c : A) (F : A → ℂ) :
    ∫ x, F (c + u • x) ∂μ = ((distribHaarChar A u : ℝ≥0) : ℝ)⁻¹ • ∫ x, F x ∂μ := by
  have h : (fun x : A => F (c + u • x)) = fun x => (fun y => F (c + y)) (u • x) := rfl
  rw [h, integral_comp_units_smul μ u (fun y => F (c + y))]
  congr 1
  simp_rw [add_comm c]
  exact integral_add_right_eq_self F c

end HaarSubst

section Adelic

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [Module.Free ℤ R] [Module.Finite ℤ R] [NumberField K]

theorem regular_adelicAddHaar :
    @Measure.Regular (AdeleRing R K) (adeleBorel R K) _ (adelicAddHaar R K) := by
  letI := adeleBorel R K
  haveI := borelSpace_adeleBorel R K
  show (Measure.addHaarMeasure _).Regular
  infer_instance

end Adelic

section Intertwining

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

theorem unipotentGL2_inv {A : Type*} [CommRing A] (x : A) :
    (unipotentGL2 x)⁻¹ = unipotentGL2 (-x) :=
  inv_eq_of_mul_eq_one_right (by rw [← unipotentGL2_add, add_neg_cancel, unipotentGL2_zero])

theorem gl2Weyl_mul_gl2Weyl {A : Type*} [Field A] : (gl2Weyl : GL (Fin 2) A) * gl2Weyl = 1 := by
  conv_lhs => rw [← gl2Weyl_inv (K := A)]
  exact inv_mul_cancel _

theorem adelicWeyl_mul_adelicWeyl : adelicWeyl R K * adelicWeyl R K = 1 := by
  unfold adelicWeyl
  rw [← map_mul, gl2Weyl_mul_gl2Weyl, map_one]

theorem adelicWeyl_inv : (adelicWeyl R K)⁻¹ = adelicWeyl R K :=
  inv_eq_of_mul_eq_one_right (adelicWeyl_mul_adelicWeyl)

theorem adelicWeyl_coe :
    ((adelicWeyl R K : AdelicGL2 R K) : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) = !![0, 1; 1, 0] := by
  ext i j
  unfold adelicWeyl
  rw [globalPoints_apply, gl2Weyl_val]
  fin_cases i <;> fin_cases j <;> simp

theorem weylInv_unipotent_borel (b : AdelicGL2 R K) (hb : b ∈ adelicBorel R K) (x : AdeleRing R K) :
    ∃ (T : AdelicGL2 R K) (hT : T ∈ adelicBorel R K),
      (adelicWeyl R K)⁻¹ * unipotentGL2 x * b
        = T * (adelicWeyl R K)⁻¹
          * unipotentGL2 ((((borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel R K)))⁻¹ : (AdeleRing R K)ˣ) : AdeleRing R K)
            * ((b : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) 0 1
              + x * (b : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) 1 1)) ∧
      borelDiagFst (⟨T, hT⟩ : ↥(adelicBorel R K)) = borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel R K)) ∧
      borelDiagSnd (⟨T, hT⟩ : ↥(adelicBorel R K)) = borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel R K)) := by
  have hb' : (b : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) 1 0 = 0 := hb
  have hainv : (((borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel R K)))⁻¹ : (AdeleRing R K)ˣ) : AdeleRing R K)
      * (b : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) 0 0 = 1 :=
    Units.inv_mul _
  let y : AdeleRing R K := (((borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel R K)))⁻¹ : (AdeleRing R K)ˣ) : AdeleRing R K)
    * ((b : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) 0 1 + x * (b : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) 1 1)
  let T : AdelicGL2 R K := (adelicWeyl R K)⁻¹ * unipotentGL2 x * b * unipotentGL2 (-y) * adelicWeyl R K

  have hT : (T : Matrix (Fin 2) (Fin 2) (AdeleRing R K))
      = !![(b : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) 1 1, 0;
           0, (b : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) 0 0] := by
    show (((adelicWeyl R K)⁻¹ * unipotentGL2 x * b * unipotentGL2 (-y) * adelicWeyl R K : AdelicGL2 R K) :
        Matrix (Fin 2) (Fin 2) (AdeleRing R K)) = _
    rw [adelicWeyl_inv]
    simp only [Matrix.GeneralLinearGroup.coe_mul, adelicWeyl_coe, unipotentGL2_coe, y]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
        hb', Fin.zero_eta, Fin.mk_one, Fin.isValue] <;>
      first
      | ring1
      | (have h2 := hainv
         try simp only [Fin.isValue] at h2 ⊢
         linear_combination (-((b : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) 0 1
           + x * (b : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) 1 1)) * h2)
  have hmem : T ∈ adelicBorel R K := by
    show (T : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) 1 0 = 0
    rw [hT]; simp
  refine ⟨T, hmem, ?_, ?_, ?_⟩
  · show (adelicWeyl R K)⁻¹ * unipotentGL2 x * b
      = (adelicWeyl R K)⁻¹ * unipotentGL2 x * b * unipotentGL2 (-y) * adelicWeyl R K
        * (adelicWeyl R K)⁻¹ * unipotentGL2 y
    simp only [mul_assoc]
    rw [mul_inv_cancel_left, ← unipotentGL2_add, neg_add_cancel, unipotentGL2_zero, mul_one]
  · apply Units.ext
    show (T : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) 0 0 = (b : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) 1 1
    rw [hT]; simp
  · apply Units.ext
    show (T : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) 1 1 = (b : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) 0 0
    rw [hT]; simp

theorem weylIntertwiningIntegral_borel_mul [Module.Free ℤ R] [Module.Finite ℤ R] [NumberField K]
    (χ₁ χ₂ : (AdeleRing R K)ˣ →* ℂˣ) (φ : AdelicGL2 R K → ℂ) (hφ : IsInducedSection R K χ₁ χ₂ φ)
    (b : AdelicGL2 R K) (hb : b ∈ adelicBorel R K) (g : AdelicGL2 R K) :
    @weylIntertwiningIntegral R K _ _ _ _ _ (adeleBorel R K) (adelicAddHaar R K) φ (b * g)
      = ((χ₁ (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel R K))) : ℂˣ) : ℂ)
        * ((χ₂ (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel R K))) : ℂˣ) : ℂ)
        * ((((distribHaarChar (AdeleRing R K) (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel R K))) : ℝ≥0) : ℝ)
            * (((distribHaarChar (AdeleRing R K) (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel R K))) : ℝ≥0)
              : ℝ))⁻¹ : ℝ) : ℂ)
        * @weylIntertwiningIntegral R K _ _ _ _ _ (adeleBorel R K) (adelicAddHaar R K) φ g := by
  letI := adeleBorel R K
  haveI := borelSpace_adeleBorel R K
  haveI := isAddHaarMeasure_adelicAddHaar R K
  haveI := regular_adelicAddHaar R K
  set a : (AdeleRing R K)ˣ := borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel R K)) with ha_def
  set d : (AdeleRing R K)ˣ := borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel R K)) with hd_def
  have hdval : (d : AdeleRing R K) = (b : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) 1 1 := rfl
  set e : AdeleRing R K := (b : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) 0 1 with he_def
  set u : (AdeleRing R K)ˣ := a⁻¹ * d with hu_def
  set c : AdeleRing R K := (↑a⁻¹ : AdeleRing R K) * e with hc_def
  let F : AdeleRing R K → ℂ := fun y => φ ((adelicWeyl R K)⁻¹ * unipotentGL2 y * g)
  have hpt : ∀ x : AdeleRing R K,
      φ ((adelicWeyl R K)⁻¹ * unipotentGL2 x * (b * g))
        = ((χ₁ d : ℂˣ) : ℂ) * ((χ₂ a : ℂˣ) : ℂ) * F (c + u • x) := by
    intro x
    obtain ⟨T, hT, hprod, hT1, hT2⟩ := weylInv_unipotent_borel b hb x
    have hyc : (((borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel R K)))⁻¹ : (AdeleRing R K)ˣ) : AdeleRing R K)
        * ((b : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) 0 1
          + x * (b : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) 1 1) = c + u • x := by
      rw [hc_def, hu_def, Units.smul_def, smul_eq_mul, Units.val_mul, ← hdval, ← ha_def, ← he_def]
      ring
    have hprod' : (adelicWeyl R K)⁻¹ * unipotentGL2 x * (b * g)
        = T * ((adelicWeyl R K)⁻¹ * unipotentGL2 (c + u • x) * g) := by
      rw [← mul_assoc, hprod, hyc]
      simp only [mul_assoc]
    rw [hprod', hφ T hT, hT1, hT2]
  unfold weylIntertwiningIntegral
  simp_rw [hpt]
  rw [integral_const_mul, integral_comp_add_units_smul (adelicAddHaar R K) u c F]
  have hδ : (((distribHaarChar (AdeleRing R K) u : ℝ≥0) : ℝ))⁻¹
      = ((distribHaarChar (AdeleRing R K) a : ℝ≥0) : ℝ)
        * (((distribHaarChar (AdeleRing R K) d : ℝ≥0) : ℝ))⁻¹ := by
    rw [hu_def, map_mul, map_inv, NNReal.coe_mul, NNReal.coe_inv, mul_inv, inv_inv]
  rw [hδ, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_inv]
  ring

end Intertwining

end AxisContAssemblyB

namespace AxisContAssemblyC

theorem isOpen_halfPlane : IsOpen {s : ℂ | 1 / 2 < s.re} :=
  isOpen_lt continuous_const Complex.continuous_re

theorem one_mem_halfPlane : (1 : ℂ) ∈ {s : ℂ | 1 / 2 < s.re} := by
  show (1 / 2 : ℝ) < (1 : ℂ).re
  norm_num

theorem transport {O : Set ℂ} (hO : IsPreconnected O) (hhp : {s : ℂ | 1 / 2 < s.re} ⊆ O)
    {D : ℂ → ℂ} (hD : AnalyticOnNhd ℂ D O) (hz : ∀ s : ℂ, 1 / 2 < s.re → D s = 0) :
    ∀ s ∈ O, D s = 0 := by
  have hev : D =ᶠ[𝓝 (1 : ℂ)] 0 := by
    filter_upwards [isOpen_halfPlane.mem_nhds one_mem_halfPlane] with s hs
    exact hz s hs
  intro s hs
  exact hD.eqOn_zero_of_preconnected_of_eventuallyEq_zero hO (hhp one_mem_halfPlane) hev hs

theorem transport_eq {O : Set ℂ} (hO : IsPreconnected O) (hhp : {s : ℂ | 1 / 2 < s.re} ⊆ O)
    {D₁ D₂ : ℂ → ℂ} (h₁ : AnalyticOnNhd ℂ D₁ O) (h₂ : AnalyticOnNhd ℂ D₂ O)
    (hz : ∀ s : ℂ, 1 / 2 < s.re → D₁ s = D₂ s) :
    ∀ s ∈ O, D₁ s = D₂ s := by
  intro s hs
  have := transport hO hhp (h₁.sub h₂) (fun s hs => by simp [hz s hs]) s hs
  simpa [sub_eq_zero] using this

section Unipotent

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

omit [TopologicalSpace A] [IsTopologicalRing A] in
theorem unipotentGL2_inv' (x : A) : (unipotentGL2 x)⁻¹ = unipotentGL2 (-x) :=
  inv_eq_of_mul_eq_one_right (by rw [← unipotentGL2_add, add_neg_cancel, unipotentGL2_zero])

omit [IsTopologicalRing A] in
theorem continuous_unipotent_matrix : Continuous (fun x : A => (!![1, x; 0, 1] : Matrix (Fin 2) (Fin 2) A)) := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem continuous_unipotentGL2 : Continuous (fun x : A => (unipotentGL2 x : GL (Fin 2) A)) := by
  rw [Units.continuous_iff]
  constructor
  · show Continuous (fun x : A => ((unipotentGL2 x : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A))
    simp_rw [unipotentGL2_coe]
    exact continuous_unipotent_matrix
  · simp_rw [unipotentGL2_inv', unipotentGL2_coe]
    exact continuous_unipotent_matrix.comp continuous_neg

end Unipotent

section Parametric

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

theorem analyticOnNhd_integral {O : Set ℂ} (hO : IsOpen O) (f : ℂ → X → ℂ)
    (hf : ContinuousOn (fun p : ℂ × X => f p.1 p.2) (O ×ˢ Set.univ))
    (ha : ∀ x, AnalyticOnNhd ℂ (fun s => f s x) O)
    (μ : Measure X) [IsFiniteMeasure μ] {C : Set X} (hC : IsCompact C) (hμC : ∀ᵐ x ∂μ, x ∈ C) :
    AnalyticOnNhd ℂ (fun s => ∫ x, f s x ∂μ) O := by
  apply DifferentiableOn.analyticOnNhd _ hO
  intro s₀ hs₀

  obtain ⟨ε, hε, hεO⟩ := Metric.isOpen_iff.mp hO s₀ hs₀
  set r : ℝ := ε / 3 with hr_def
  have hr : 0 < r := by positivity
  have hcb : Metric.closedBall s₀ (2 * r) ⊆ O := by
    intro z hz
    apply hεO
    rw [Metric.mem_ball]
    have := Metric.mem_closedBall.mp hz
    linarith

  have hslice : ∀ s ∈ O, Continuous (fun x => f s x) := by
    intro s hs
    have h1 : ContinuousOn (fun x : X => ((s, x) : ℂ × X)) Set.univ :=
      (Continuous.prodMk_right s).continuousOn
    have h2 := hf.comp h1 (fun x _ => ⟨hs, Set.mem_univ x⟩)
    exact continuousOn_univ.mp h2
  have hmeas : ∀ s ∈ O, AEStronglyMeasurable (fun x => f s x) μ :=
    fun s hs => (hslice s hs).aestronglyMeasurable

  have hK : IsCompact (Metric.closedBall s₀ (2 * r) ×ˢ C) := (isCompact_closedBall _ _).prod hC
  have hfK : ContinuousOn (fun p : ℂ × X => f p.1 p.2) (Metric.closedBall s₀ (2 * r) ×ˢ C) :=
    hf.mono (Set.prod_mono hcb (Set.subset_univ _))
  obtain ⟨M₀, hM₀⟩ := hK.exists_bound_of_continuousOn hfK
  set M : ℝ := max M₀ 0 with hM_def
  have hM0 : 0 ≤ M := le_max_right _ _
  have hM : ∀ s ∈ Metric.closedBall s₀ (2 * r), ∀ x ∈ C, ‖f s x‖ ≤ M :=
    fun s hs x hx => (hM₀ (s, x) ⟨hs, hx⟩).trans (le_max_left _ _)

  let F' : ℂ → X → ℂ := fun s x => deriv (fun s => f s x) s
  have hball : ∀ s ∈ Metric.ball s₀ r, Metric.closedBall s r ⊆ Metric.closedBall s₀ (2 * r) := by
    intro s hs z hz
    rw [Metric.mem_closedBall] at hz ⊢
    rw [Metric.mem_ball] at hs
    calc dist z s₀ ≤ dist z s + dist s s₀ := dist_triangle _ _ _
      _ ≤ r + r := add_le_add hz hs.le
      _ = 2 * r := by ring
  have hderiv_bound : ∀ x ∈ C, ∀ s ∈ Metric.ball s₀ r, ‖F' s x‖ ≤ M / r := by
    intro x hx s hs
    have hsub : Metric.closedBall s r ⊆ O := (hball s hs).trans hcb
    have hd : DiffContOnCl ℂ (fun s => f s x) (Metric.ball s r) := by
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball s hr.ne']
      exact (ha x).differentiableOn.mono hsub
    refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hd (fun z hz => ?_)
    exact hM z (hball s hs (Metric.sphere_subset_closedBall hz)) x hx
  have hderiv : ∀ x, ∀ s ∈ Metric.ball s₀ r, HasDerivAt (fun s => f s x) (F' s x) s := by
    intro x s hs
    have hsO : s ∈ O := hcb (hball s hs (Metric.mem_closedBall_self hr.le))
    exact ((ha x) s hsO).differentiableAt.hasDerivAt

  have hF'meas : AEStronglyMeasurable (F' s₀) μ := by
    let t : ℕ → ℂ := fun n : ℕ => ((r / 2 / ((n : ℝ) + 1) : ℝ) : ℂ)
    have ht_pos : ∀ n : ℕ, 0 < r / 2 / ((n : ℝ) + 1) := fun n => div_pos (half_pos hr) (Nat.cast_add_one_pos n)
    have ht_ne : ∀ n, t n ≠ 0 := fun n => by
      simp only [t, ne_eq, Complex.ofReal_eq_zero]
      exact (ht_pos n).ne'
    have ht_mem : ∀ n, s₀ + t n ∈ O := by
      intro n
      apply hcb
      rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left]
      simp only [t, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (ht_pos n)]
      have h1 : r / 2 / ((n : ℝ) + 1) ≤ r / 2 := by
        apply div_le_self (by positivity)
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith
      linarith
    have ht_lim : Tendsto t atTop (𝓝[≠] 0) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, Eventually.of_forall ht_ne⟩
      have h0 : Tendsto (fun n : ℕ => r / 2 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
        have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (r / 2)
        simp only [mul_zero] at this
        refine this.congr (fun n => ?_)
        ring
      have := (Complex.continuous_ofReal.tendsto 0).comp h0
      rw [Complex.ofReal_zero] at this
      exact this
    let q : ℕ → X → ℂ := fun n x => (t n)⁻¹ • (f (s₀ + t n) x - f s₀ x)
    have hq_meas : ∀ n, AEStronglyMeasurable (q n) μ := by
      intro n
      exact (((hslice _ (ht_mem n)).sub (hslice _ hs₀)).const_smul (t n)⁻¹).aestronglyMeasurable
    refine aestronglyMeasurable_of_tendsto_ae atTop hq_meas (Eventually.of_forall (fun x => ?_))
    have h := (hderiv x s₀ (Metric.mem_ball_self hr)).tendsto_slope_zero
    exact h.comp ht_lim

  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := f) (F' := F') (x₀ := s₀) (bound := fun _ => M / r)
    (Metric.ball_mem_nhds s₀ hr)
    (by
      filter_upwards [hO.mem_nhds hs₀] with s hs
      exact hmeas s hs)
    (by
      refine Integrable.mono' (integrable_const M) (hmeas s₀ hs₀) ?_
      filter_upwards [hμC] with x hx
      exact hM s₀ (Metric.mem_closedBall_self (by positivity)) x hx)
    hF'meas
    (by
      filter_upwards [hμC] with x hx
      intro s hs
      exact hderiv_bound x hx s hs)
    (integrable_const _)
    (Eventually.of_forall (fun x s hs => hderiv x s hs))
  exact hmain.2.differentiableAt.differentiableWithinAt

end Parametric

end AxisContAssemblyC

namespace AxisContAssemblyD

attribute [local instance] NumberField.AdelicHaar.glBorel
attribute [local instance] NumberField.AdelicHaar.adeleBorel

section Eta

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

theorem eta_reflect (μ ν : (AdeleRing R K)ˣ →* ℂˣ) (α : (AdeleRing R K)ˣ →* ℝˣ)
    (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (s : ℂ) (a d : (AdeleRing R K)ˣ) :
    ((etaFst μ α hα s d : ℂˣ) : ℂ) * ((etaSnd ν α hα s a : ℂˣ) : ℂ)
        * (((((α a : ℝˣ) : ℝ) * (((α d : ℝˣ) : ℝ))⁻¹ : ℝ)) : ℂ)
      = ((etaFst ν α hα (-s) a : ℂˣ) : ℂ) * ((etaSnd μ α hα (-s) d : ℂˣ) : ℂ) := by
  simp only [etaFst_apply, etaSnd_apply, Units.val_mul, cpowChar_apply_val, Complex.ofReal_mul,
    Complex.ofReal_inv]
  have ha : (((α a : ℝˣ) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hα a).ne'
  have hd : (((α d : ℝˣ) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hα d).ne'
  have hA : (((α a : ℝˣ) : ℝ) : ℂ) ^ (-(s + 1 / 2)) * (((α a : ℝˣ) : ℝ) : ℂ)
      = (((α a : ℝˣ) : ℝ) : ℂ) ^ (-s + 1 / 2) := by
    rw [show (((α a : ℝˣ) : ℝ) : ℂ) ^ (-(s + 1 / 2)) * (((α a : ℝˣ) : ℝ) : ℂ)
        = (((α a : ℝˣ) : ℝ) : ℂ) ^ (-(s + 1 / 2)) * (((α a : ℝˣ) : ℝ) : ℂ) ^ (1 : ℂ) by
          rw [Complex.cpow_one], ← Complex.cpow_add _ _ ha]
    congr 1
    ring
  have hD : (((α d : ℝˣ) : ℝ) : ℂ) ^ (s + 1 / 2) * ((((α d : ℝˣ) : ℝ) : ℂ))⁻¹
      = (((α d : ℝˣ) : ℝ) : ℂ) ^ (-(-s + 1 / 2)) := by
    rw [← Complex.cpow_neg_one, ← Complex.cpow_add _ _ hd]
    congr 1
    ring
  calc ((μ d : ℂˣ) : ℂ) * (((α d : ℝˣ) : ℝ) : ℂ) ^ (s + 1 / 2)
        * (((ν a : ℂˣ) : ℂ) * (((α a : ℝˣ) : ℝ) : ℂ) ^ (-(s + 1 / 2)))
        * ((((α a : ℝˣ) : ℝ) : ℂ) * ((((α d : ℝˣ) : ℝ) : ℂ))⁻¹)
      = ((ν a : ℂˣ) : ℂ) * ((((α a : ℝˣ) : ℝ) : ℂ) ^ (-(s + 1 / 2)) * (((α a : ℝˣ) : ℝ) : ℂ))
        * (((μ d : ℂˣ) : ℂ) * ((((α d : ℝˣ) : ℝ) : ℂ) ^ (s + 1 / 2)
          * ((((α d : ℝˣ) : ℝ) : ℂ))⁻¹)) := by ring
    _ = ((ν a : ℂˣ) : ℂ) * (((α a : ℝˣ) : ℝ) : ℂ) ^ (-s + 1 / 2)
        * (((μ d : ℂˣ) : ℂ) * (((α d : ℝˣ) : ℝ) : ℂ) ^ (-(-s + 1 / 2))) := by rw [hA, hD]

theorem differentiable_etaFst_val (ν : (AdeleRing R K)ˣ →* ℂˣ) (α : (AdeleRing R K)ˣ →* ℝˣ)
    (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (a : (AdeleRing R K)ˣ) :
    Differentiable ℂ (fun s : ℂ => ((etaFst ν α hα (-s) a : ℂˣ) : ℂ)) := by
  simp only [etaFst_apply, Units.val_mul, cpowChar_apply_val]
  have ha : (((α a : ℝˣ) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hα a).ne'
  exact (differentiable_const _).mul
    ((differentiable_id.neg.add_const _).const_cpow (Or.inl ha))

theorem differentiable_etaSnd_val (μ : (AdeleRing R K)ˣ →* ℂˣ) (α : (AdeleRing R K)ˣ →* ℝˣ)
    (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (d : (AdeleRing R K)ˣ) :
    Differentiable ℂ (fun s : ℂ => ((etaSnd μ α hα (-s) d : ℂˣ) : ℂ)) := by
  simp only [etaSnd_apply, Units.val_mul, cpowChar_apply_val]
  have hd : (((α d : ℝˣ) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hα d).ne'
  exact (differentiable_const _).mul
    ((differentiable_id.neg.add_const _).neg.const_cpow (Or.inl hd))

theorem centralScalar_mul_comm (z : (AdeleRing R K)ˣ) (h : AdelicGL2 R K) :
    centralScalar R K z * h = h * centralScalar R K z := by
  apply Units.ext
  have hval : ((centralScalar R K z : AdelicGL2 R K) : Matrix (Fin 2) (Fin 2) (AdeleRing R K))
      = Matrix.scalar (Fin 2) (z : AdeleRing R K) := rfl
  rw [Units.val_mul, Units.val_mul, hval]
  exact (Matrix.scalar_commute (z : AdeleRing R K) (fun r' => Commute.all _ _) _).eq

end Eta

end AxisContAssemblyD

open AxisContAssemblyA AxisContAssemblyB AxisContAssemblyC AxisContAssemblyD

attribute [local instance] NumberField.AdelicHaar.glBorel
attribute [local instance] NumberField.AdelicHaar.adeleBorel

theorem solution (L : Type) [Field L] [NumberField L]
    (αn : (AdeleRing (𝓞 L) L)ˣ →* ℝˣ) (hαn : ∀ x, 0 < ((αn x : ℝˣ) : ℝ))
    (hαeq : αn = ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp (distribHaarChar (AdeleRing (𝓞 L) L))).toHomUnits)
    (μ ν : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) (hμ : IsUnitaryChar (𝓞 L) L μ) (hν : IsUnitaryChar (𝓞 L) L ν)
    (hμc : IsIdeleClassChar (𝓞 L) L μ) (hνc : IsIdeleClassChar (𝓞 L) L ν)
    (hμk : Continuous fun x : (AdeleRing (𝓞 L) L)ˣ => ((μ x : ℂˣ) : ℂ))
    (hνk : Continuous fun x : (AdeleRing (𝓞 L) L)ˣ => ((ν x : ℂˣ) : ℂ))
    (Ef : ℂ → AdelicGL2 (𝓞 L) L → ℂ)
    (hEf : ∀ s, IsInducedSection (𝓞 L) L (etaFst μ αn hαn s) (etaSnd ν αn hαn s) (Ef s))
    (hK : ∀ s, IsArchKFinite L (Ef s)) (hf : ∀ s, IsKfSmooth L (Ef s))
    (hjc : Continuous fun p : ℂ × AdelicGL2 (𝓞 L) L => Ef p.1 p.2)
    (hhol : ∀ g : AdelicGL2 (𝓞 L) L, Differentiable ℂ (fun s => Ef s g))
    (hKu : ∀ w : InfinitePlace L, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup L w) → ℂ),
      FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 L) L),
        (fun k : ↥(archRowIsometrySubgroup L w) => Ef s (g * (k : AdelicGL2 (𝓞 L) L))) ∈ W) :
    ∃ (O : Set ℂ) (Ec Nc : ℂ → AdelicGL2 (𝓞 L) L → ℂ),
      IsOpen O ∧ IsPreconnected O ∧ {s : ℂ | s.re = 0} ⊆ O ∧ {s : ℂ | 1 / 2 < s.re} ⊆ O ∧
      (∀ g : AdelicGL2 (𝓞 L) L, AnalyticOnNhd ℂ (fun s => Ec s g) O) ∧
      (∀ g : AdelicGL2 (𝓞 L) L, AnalyticOnNhd ℂ (fun s => Nc s g) O) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 L) L => Ec p.1 p.2) (O ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 L) L => Nc p.1 p.2) (O ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → Ec s = pseudoEisenstein L (Ef s)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 L) L,
        Nc s g = (((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ)⁻¹ *
          weylIntertwiningIntegral (𝓞 L) L (adelicAddHaar (𝓞 L) L) (Ef s) g) ∧
      (∀ s : ℂ, IsInducedSection (𝓞 L) L (etaFst ν αn hαn (-s)) (etaSnd μ αn hαn (-s)) (Nc s)) ∧
      (∀ s ∈ O, ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) L) (g : AdelicGL2 (𝓞 L) L),
        Ec s (globalPoints (𝓞 L) L γ * g) = Ec s g) ∧
      (∀ s ∈ O, ∀ (z : (AdeleRing (𝓞 L) L)ˣ) (g : AdelicGL2 (𝓞 L) L),
        Ec s (centralScalar (𝓞 L) L z * g) = ((μ z : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ) * Ec s g) ∧
      (∀ s ∈ O, ∀ g : AdelicGL2 (𝓞 L) L,
        @constantTerm (AdeleRing (𝓞 L) L) (adeleBorel (𝓞 L) L) (AdelicGL2 (𝓞 L) L) _
          (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
          unipotentGL2 (Ec s) g = Ef s g + Nc s g) ∧
      (∀ u₀ : AdelicGL2 (𝓞 L) L, (∀ (s : ℂ) (g : AdelicGL2 (𝓞 L) L), Ef s (g * u₀) = Ef s g) →
        ∀ s ∈ O, ∀ g : AdelicGL2 (𝓞 L) L, Ec s (g * u₀) = Ec s g ∧ Nc s (g * u₀) = Nc s g) := by
  subst hαeq
  haveI : BorelSpace (AdeleRing (𝓞 L) L) := borelSpace_adeleBorel (𝓞 L) L
  haveI hHaar : (adelicAddHaar (𝓞 L) L).IsAddHaarMeasure := isAddHaarMeasure_adelicAddHaar (𝓞 L) L
  haveI hPprob : IsProbabilityMeasure
      (ProbabilityTheory.cond (adelicAddHaar (𝓞 L) L) (adelicBox L)) :=
    isProbabilityMeasure_cond_adelicBox L

  have hcont : ∀ s, Continuous (Ef s) := fun s => hjc.comp (Continuous.prodMk_right s)

  have hprin : IsPrincipalTrivial (R := 𝓞 L) (K := L)
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp (distribHaarChar (AdeleRing (𝓞 L) L))).toHomUnits := by
    intro u
    apply Units.ext
    rw [MonoidHom.coe_toHomUnits, MonoidHom.comp_apply, Units.val_one]
    have h := NumberField.AdeleRing.distribHaarChar_algebraMap L u
    rw [RingHom.toMonoidHom_eq_coe] at h
    rw [h]
    simp

  have hB : ∀ s, ∀ b ∈ borelSubgroup L, ∀ g : AdelicGL2 (𝓞 L) L,
      Ef s (globalPoints (𝓞 L) L b * g) = Ef s g := by
    intro s b hb g
    have hmem := globalPoints_mem_adelicBorel (𝓞 L) L hb
    rw [(hEf s) _ hmem g, borelDiagFst_globalPoints (𝓞 L) L hb hmem,
      borelDiagSnd_globalPoints (𝓞 L) L hb hmem, etaFst_isIdeleClassChar hμc hprin s _,
      etaSnd_isIdeleClassChar hνc hprin s _, Units.val_one, one_mul, one_mul]

  have hS : ∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 L) L,
      Summable (fun ξ : L => Ef s (adelicWeyl (𝓞 L) L
        * unipotentGL2 (algebraMap L (AdeleRing (𝓞 L) L) ξ) * g)) := fun s hs g =>
    Summable.of_norm (AutomorphicForm.bruhatTransversal_summand_norm_summable_of_re_gt_half L hαn
      μ ν hμ hν s hs (Ef s) (hEf s) (hcont s) g)

  obtain ⟨O, Ec, Nc0, hO, hOc, hax, hhp, hEa, hNa, hEc, hNc, hEeq, hNeq⟩ :=
    AutomorphicForm.exists_analyticOnNhd_axis_continuation_bruhatEisenstein_weylIntertwiningIntegral_of_isArchKFinite_family
      L hαn μ ν hμ hν hμc hνc hμk hνk Ef hEf hK hf hjc hhol hKu

  let cvol : ℂ := (((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ)⁻¹
  let Nc : ℂ → AdelicGL2 (𝓞 L) L → ℂ := fun s g => O.indicator (fun s' => cvol * Nc0 s' g) s
  have hNc_mem : ∀ s ∈ O, ∀ g, Nc s g = cvol * Nc0 s g := fun s hs g => Set.indicator_of_mem hs _
  have hNc_nmem : ∀ s ∉ O, ∀ g, Nc s g = 0 := fun s hs g => Set.indicator_of_notMem hs _

  have hEfun : ∀ s : ℂ, 1 / 2 < s.re → Ec s = eis (Ef s) := by
    intro s hs; funext g; exact hEeq s hs g
  have hEfun' : ∀ s : ℂ, 1 / 2 < s.re → Ec s = pseudoEisenstein L (Ef s) := by
    intro s hs; funext g; rw [pseudoEisenstein_apply]; exact hEeq s hs g

  have hNa' : ∀ g : AdelicGL2 (𝓞 L) L, AnalyticOnNhd ℂ (fun s => Nc s g) O := by
    intro g s hs
    have hev : (fun s => cvol * Nc0 s g) =ᶠ[𝓝 s] (fun s => Nc s g) := by
      filter_upwards [hO.mem_nhds hs] with s' hs'
      exact (hNc_mem s' hs' g).symm
    exact (analyticAt_const.mul (hNa g s hs)).congr hev
  have hNeq' : ∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 L) L,
      Nc s g = cvol * weylIntertwiningIntegral (𝓞 L) L (adelicAddHaar (𝓞 L) L) (Ef s) g := by
    intro s hs g
    rw [hNc_mem s (hhp hs) g, hNeq s hs g]
  refine ⟨O, Ec, Nc, hO, hOc, hax, hhp, hEa, hNa', hEc, ?_, hEfun', hNeq', ?_, ?_, ?_, ?_, ?_⟩
  ·
    exact ((continuousOn_const (c := cvol)).mul hNc).congr (fun p hp => hNc_mem p.1 hp.1 p.2)
  ·
    intro s b hb g
    by_cases hs : s ∈ O
    ·
      have key := transport_eq hOc hhp
        (D₁ := fun s' => cvol * Nc0 s' (b * g))
        (D₂ := fun s' => ((etaFst ν _ hαn (-s') (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 L) L)))
            : ℂˣ) : ℂ) * ((etaSnd μ _ hαn (-s') (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 L) L)))
            : ℂˣ) : ℂ) * (cvol * Nc0 s' g))
        (analyticOnNhd_const.mul (hNa (b * g)))
        ((((differentiable_etaFst_val ν _ hαn _).mul (differentiable_etaSnd_val μ _ hαn _)
            ).differentiableOn.analyticOnNhd hO).mul (analyticOnNhd_const.mul (hNa g)))
        (by
          intro s' hs'
          show cvol * Nc0 s' (b * g) = _ * (cvol * Nc0 s' g)
          rw [hNeq s' hs' (b * g), hNeq s' hs' g,
            weylIntertwiningIntegral_borel_mul (etaFst μ _ hαn s') (etaSnd ν _ hαn s') (Ef s')
              (hEf s') b hb g, ← eta_reflect μ ν _ hαn s']
          have hδ : ∀ u : (AdeleRing (𝓞 L) L)ˣ,
              ((distribHaarChar (AdeleRing (𝓞 L) L) u : ℝ≥0) : ℝ)
                = ((((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
                    (distribHaarChar (AdeleRing (𝓞 L) L))).toHomUnits u : ℝˣ) : ℝ) := by
            intro u
            rw [MonoidHom.coe_toHomUnits, MonoidHom.comp_apply]
            rfl
          rw [hδ, hδ]
          ring)
        s hs
      rw [hNc_mem s hs, hNc_mem s hs]
      exact key
    · rw [hNc_nmem s hs, hNc_nmem s hs, mul_zero]
  ·
    intro s hs γ g
    exact transport_eq hOc hhp (hEa (globalPoints (𝓞 L) L γ * g)) (hEa g)
      (fun s' hs' => by
        show Ec s' (globalPoints (𝓞 L) L γ * g) = Ec s' g
        rw [hEfun s' hs']
        exact eis_globalPoints_mul (Ef s') (hB s') (hS s' hs') γ g) s hs
  ·
    intro s hs z g
    exact transport_eq hOc hhp (hEa (centralScalar (𝓞 L) L z * g))
      (analyticOnNhd_const.mul (hEa g))
      (fun s' hs' => by
        show Ec s' (centralScalar (𝓞 L) L z * g) = _ * Ec s' g
        rw [hEfun s' hs']
        have hz : ∀ h : AdelicGL2 (𝓞 L) L, Ef s' (centralScalar (𝓞 L) L z * h)
            = ((μ z : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ) * Ef s' h := by
          intro h
          rw [isInducedSection_centralScalar_mul (hEf s') z h, ← Units.val_mul, ← Units.val_mul,
            etaFst_mul_etaSnd]
        unfold eis
        have hcomm : ∀ ξ : L, adelicWeyl (𝓞 L) L * unipotentGL2 (algebraMap L (AdeleRing (𝓞 L) L) ξ)
            * (centralScalar (𝓞 L) L z * g)
            = centralScalar (𝓞 L) L z * (adelicWeyl (𝓞 L) L
              * unipotentGL2 (algebraMap L (AdeleRing (𝓞 L) L) ξ) * g) := by
          intro ξ
          rw [← mul_assoc, ← centralScalar_mul_comm z, mul_assoc]
        simp_rw [hcomm, hz, tsum_mul_left]
        ring) s hs
  ·
    intro s hs g

    obtain ⟨C, hC, hBC⟩ := exists_isCompact_adelicBox_subset L
    have hPC : ∀ᵐ q ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 L) L) (adelicBox L)), q ∈ C := by
      rw [ProbabilityTheory.cond]
      exact Measure.ae_smul_measure ((ae_restrict_mem (measurableSet_adelicBox L)).mono
        (fun q hq => hBC hq)) _

    have hker : ContinuousOn (fun p : ℂ × AdeleRing (𝓞 L) L => Ec p.1 (unipotentGL2 p.2 * g))
        (O ×ˢ Set.univ) := by
      have hmap : Continuous (fun p : ℂ × AdeleRing (𝓞 L) L =>
          ((p.1, unipotentGL2 p.2 * g) : ℂ × AdelicGL2 (𝓞 L) L)) :=
        continuous_fst.prodMk ((continuous_unipotentGL2.comp continuous_snd).mul continuous_const)
      exact hEc.comp hmap.continuousOn (fun p hp => ⟨hp.1, Set.mem_univ _⟩)
    have hD₁ : AnalyticOnNhd ℂ (fun s' => ∫ q, Ec s' (unipotentGL2 q * g)
        ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 L) L) (adelicBox L))) O :=
      analyticOnNhd_integral hO (fun s' q => Ec s' (unipotentGL2 q * g)) hker
        (fun q => hEa (unipotentGL2 q * g)) _ hC hPC
    have key := transport_eq hOc hhp hD₁
      ((((hhol g).differentiableOn.analyticOnNhd hO)).add (hNa' g))
      (fun s' hs' => by
        show (∫ q, Ec s' (unipotentGL2 q * g)
          ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 L) L) (adelicBox L))) = Ef s' g + Nc s' g
        rw [hNeq' s' hs' g, hEfun s' hs']
        have h := AutomorphicForm.constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral
          L hαn μ ν hμ hν s' hs' (Ef s') (hEf s') (hcont s') g
        exact h) s hs
    exact key
  ·
    intro u₀ hu s hs g
    constructor
    · exact transport_eq hOc hhp (hEa (g * u₀)) (hEa g)
        (fun s' hs' => by
          show Ec s' (g * u₀) = Ec s' g
          rw [hEfun s' hs']
          unfold eis
          congr 1
          · exact hu s' g
          · congr 1
            funext ξ
            rw [← mul_assoc]
            exact hu s' _) s hs
    · rw [hNc_mem s hs, hNc_mem s hs]
      congr 1
      exact transport_eq hOc hhp (hNa (g * u₀)) (hNa g)
        (fun s' hs' => by
          show Nc0 s' (g * u₀) = Nc0 s' g
          rw [hNeq s' hs', hNeq s' hs']
          unfold weylIntertwiningIntegral
          congr 1
          funext x
          rw [← mul_assoc]
          exact hu s' _) s hs

end S_AxisWitness_exists_axisContinuation
end P2MW
export P2MW.S_AxisWitness_exists_axisContinuation (solution)
