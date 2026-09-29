-- Prove2me | solution 1 for AutomorphicForm.tsum_sigmaCentralizer_apply_mulVec_add_eq_inv_ideleNorm_det_mul_tsum_reflectPair_of_forall_ne_scalar_of_finrank_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/a4eb1945-e3eb-5bba-8d02-c0179c5f9d85

import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_SigmaCentralizer
import Theorems.Thm_AutomorphicForm_existsUnique_mul_eq_mul_map_and_mulVec_eq_of_forall_ne_scalar_of_finrank_eq_two
import Theorems.Thm_NumberField_AdelicFourier_tsum_apply_smul_vecMul_add_eq_ideleNorm_cpow_neg_two_mul_tsum_reflectPair_of_mem_schwartzBruhat2
import Theorems.Thm_NumberField_AdelicFourier_tsum_eq_inv_measure_sq_mul_tsum_fourierTransform2_of_mem_schwartzBruhat2
import Theorems.Thm_NumberField_AdelicFourier_continuous_integrable_comp_vecMul_mem_and_bottomRowVec_mem_schwartzBruhat_of_mem_schwartzBruhat2
import Theorems.Thm_NumberField_AdelicFourier_fourierTransform2_mem_schwartzBruhat2_and_reflectPair_mem_schwartzBruhat2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_tsum_sigmaCentralizer_apply_mulVec_add_eq_inv_ideleNorm_det_mul_tsum_reflectPair_of_forall_ne_scalar_of_finrank_eq_two
p2m_attr_erase "instance" "FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom"
p2m_attr_erase "instance" "SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions"
p2m_attr_erase "simp" "AutomorphicForm.IsStableLinearOn.coe_toEnd_apply AutomorphicForm.ArchRepAt.mk.sizeOf_spec AutomorphicForm.IsIsotypicCuspFormAt.toRealization_toFun AutomorphicForm.ArchTypeFamily.mk.sizeOf_spec AutomorphicForm.charRep_apply AutomorphicForm.ArchRepAt.mk.injEq AutomorphicForm.ArchTypeFamily.mk.injEq AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral"
p2m_attr_erase "simp" "AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal"
p2m_attr_erase "simp" "Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply ContinuousAddEquiv.preimage_mulLeft_smul"

set_option autoImplicit false

p2m_open "MeasureTheory NumberField NumberField.AdelicFourier NumberField.AdelicBox NumberField.TateGlobal AutomorphicForm P2MW.S_AutomorphicForm_tsum_sigmaCentralizer_apply_mulVec_add_eq_inv_ideleNorm_det_mul_tsum_reflectPair_of_forall_ne_scalar_of_finrank_eq_two.AutomorphicForm"

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsGlobalAddChar sigmaCentralizer mem_sigmaCentralizer_iff existsUnique_mul_eq_mul_map_and_mulVec_eq_of_forall_ne_scalar_of_finrank_eq_two"
namespace TwistedThetaSol
p2m_open "AutomorphicForm"

section Mat

variable {R : Type} [CommRing R]

def trGL (g : GL (Fin 2) R) : GL (Fin 2) R :=
  ⟨(g : Matrix (Fin 2) (Fin 2) R).transpose, ((g⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R).transpose,
    by rw [← Matrix.transpose_mul, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel]; simp,
    by rw [← Matrix.transpose_mul, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel]; simp⟩

theorem coe_trGL (g : GL (Fin 2) R) :
    ((trGL g : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) = (g : Matrix (Fin 2) (Fin 2) R).transpose := rfl

theorem det_trGL (g : GL (Fin 2) R) :
    Matrix.GeneralLinearGroup.det (trGL g) = Matrix.GeneralLinearGroup.det g := by
  ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, coe_trGL, Matrix.det_transpose]

theorem vecMul_trGL (g : GL (Fin 2) R) (x : Fin 2 → R) :
    Matrix.vecMul x ((trGL g : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) =
      (g : Matrix (Fin 2) (Fin 2) R).mulVec x := by
  rw [coe_trGL, Matrix.vecMul_transpose]

theorem coe_scalar (u : Rˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) =
      Matrix.scalar (Fin 2) (u : R) := rfl

theorem vecMul_scalar_mul (t : Rˣ) (g : GL (Fin 2) R) (x : Fin 2 → R) :
    Matrix.vecMul x ((Matrix.GeneralLinearGroup.scalar (Fin 2) t * g : GL (Fin 2) R) :
        Matrix (Fin 2) (Fin 2) R) =
      (t : R) • Matrix.vecMul x (g : Matrix (Fin 2) (Fin 2) R) := by
  rw [Matrix.GeneralLinearGroup.coe_mul, coe_scalar, ← Matrix.vecMul_vecMul]
  have : Matrix.vecMul x (Matrix.scalar (Fin 2) (t : R)) = (t : R) • x := by
    funext i; simp [Matrix.scalar_apply, Matrix.vecMul_diagonal, mul_comm]
  rw [this, Matrix.smul_vecMul]

end Mat

section Bij

variable (K L : Type) [Field K] [CharZero K] [Field L] [Algebra K L]
  (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
  (δ₀ : GL (Fin 2) L)
  (hN : ∃ z : Lˣ, δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) δ₀ =
    Matrix.GeneralLinearGroup.scalar (Fin 2) z)
  (hns : ∀ (x : GL (Fin 2) L) (z : Lˣ),
    x⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) x ≠
      Matrix.GeneralLinearGroup.scalar (Fin 2) z)

include h2 hgen hN hns

theorem isUnit_of_eq {x : Matrix (Fin 2) (Fin 2) L}
    (hx : x * (δ₀ : Matrix (Fin 2) (Fin 2) L) = (δ₀ : Matrix (Fin 2) (Fin 2) L) * x.map σ) (hx0 : x ≠ 0) :
    IsUnit x := by
  classical
  by_contra hu
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not] at hu
  obtain ⟨u, hu0, hxu⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hu
  obtain ⟨y, -, hyu⟩ :=
    AutomorphicForm.existsUnique_mul_eq_mul_map_and_mulVec_eq_of_forall_ne_scalar_of_finrank_eq_two
      K L h2 σ hgen δ₀ hN hns u hu0 0
  have h0 : (0 : Matrix (Fin 2) (Fin 2) L) * (δ₀ : Matrix (Fin 2) (Fin 2) L) =
      (δ₀ : Matrix (Fin 2) (Fin 2) L) * (0 : Matrix (Fin 2) (Fin 2) L).map σ := by
    rw [zero_mul, show (0 : Matrix (Fin 2) (Fin 2) L).map σ = 0 from by ext i j; simp, mul_zero]
  exact hx0 ((hyu x ⟨hx, hxu⟩).trans (hyu 0 ⟨h0, Matrix.zero_mulVec _⟩).symm)

omit [CharZero K] h2 hgen hN hns in

theorem mem_iff (γ : GL (Fin 2) L) :
    γ ∈ sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ₀ ↔
      (γ : Matrix (Fin 2) (Fin 2) L) * (δ₀ : Matrix (Fin 2) (Fin 2) L) =
        (δ₀ : Matrix (Fin 2) (Fin 2) L) * (γ : Matrix (Fin 2) (Fin 2) L).map σ := by
  rw [mem_sigmaCentralizer_iff, mul_inv_eq_iff_eq_mul]
  constructor
  · intro h
    have := congrArg (fun g : GL (Fin 2) L => (g : Matrix (Fin 2) (Fin 2) L)) h
    simp only [Matrix.GeneralLinearGroup.coe_mul] at this
    exact this
  · intro h
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    have := congrFun (congrFun h i) j
    simp only [Matrix.GeneralLinearGroup.coe_mul] at this ⊢
    exact this

def colFun (v : Fin 2 → L) (hv : v ≠ 0)
    (γ : ↥(sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ₀)) :
    {w : Fin 2 → L // w ≠ 0} :=
  ⟨((γ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L).mulVec v, by
    intro h
    apply hv
    calc v = (((γ : GL (Fin 2) L)⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L).mulVec
          (((γ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L).mulVec v) := by
          rw [Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
            Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
      _ = 0 := by rw [h, Matrix.mulVec_zero]⟩

omit [CharZero K] h2 hgen hN hns in
theorem colFun_val (v : Fin 2 → L) (hv : v ≠ 0)
    (γ : ↥(sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ₀)) :
    (colFun K L σ δ₀ v hv γ : Fin 2 → L) = ((γ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L).mulVec v := rfl

theorem colFun_bijective (v : Fin 2 → L) (hv : v ≠ 0) :
    Function.Bijective (colFun K L σ δ₀ v hv) := by
  constructor
  · intro γ₁ γ₂ h
    have h' := congrArg Subtype.val h
    rw [colFun_val, colFun_val] at h'
    obtain ⟨y, -, hyu⟩ :=
      AutomorphicForm.existsUnique_mul_eq_mul_map_and_mulVec_eq_of_forall_ne_scalar_of_finrank_eq_two
        K L h2 σ hgen δ₀ hN hns v hv (((γ₁ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L).mulVec v)
    have e1 := hyu _ ⟨(mem_iff K L σ δ₀ _).1 γ₁.2, rfl⟩
    have e2 := hyu _ ⟨(mem_iff K L σ δ₀ _).1 γ₂.2, h'.symm⟩
    exact Subtype.ext (Matrix.GeneralLinearGroup.ext fun i j => congrFun (congrFun (e1.trans e2.symm) i) j)
  · intro w
    obtain ⟨x, ⟨hx, hxv⟩, -⟩ :=
      AutomorphicForm.existsUnique_mul_eq_mul_map_and_mulVec_eq_of_forall_ne_scalar_of_finrank_eq_two
        K L h2 σ hgen δ₀ hN hns v hv w
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact w.2 (by rw [← hxv, Matrix.zero_mulVec])
    obtain ⟨u, hu⟩ := isUnit_of_eq K L h2 σ hgen δ₀ hN hns hx hx0
    have hmem : (u : GL (Fin 2) L) ∈ sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ₀ := by
      rw [mem_iff K L σ δ₀]
      rw [hu]; exact hx
    refine ⟨⟨u, hmem⟩, Subtype.ext ?_⟩
    rw [colFun_val]
    change (u : Matrix (Fin 2) (Fin 2) L).mulVec v = w
    rw [hu, hxv]

def colEquiv (v : Fin 2 → L) (hv : v ≠ 0) :
    ↥(sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ₀) ≃ {w : Fin 2 → L // w ≠ 0} :=
  Equiv.ofBijective _ (colFun_bijective K L h2 σ hgen δ₀ hN hns v hv)

theorem colEquiv_apply (v : Fin 2 → L) (hv : v ≠ 0)
    (γ : ↥(sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ₀)) :
    (colEquiv K L h2 σ hgen δ₀ hN hns v hv γ : Fin 2 → L) =
      ((γ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L).mulVec v := rfl

end Bij

end AutomorphicForm.TwistedThetaSol

end

open AutomorphicForm.TwistedThetaSol in
theorem solution
    (K L : Type) [Field K] [CharZero K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (δ₀ : GL (Fin 2) L)
    (hN : ∃ z : Lˣ, δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) δ₀ =
      Matrix.GeneralLinearGroup.scalar (Fin 2) z)
    (hns : ∀ (x : GL (Fin 2) L) (z : Lˣ),
      x⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) x ≠
        Matrix.GeneralLinearGroup.scalar (Fin 2) z)
    (v : Fin 2 → L) (hv : v ≠ 0)
    [MeasurableSpace (AdeleRing (𝓞 L) L)] [BorelSpace (AdeleRing (𝓞 L) L)]
    (μ₁ : Measure (AdeleRing (𝓞 L) L)) [μ₁.IsAddHaarMeasure] (hμ₁ : μ₁ (adelicBox L) = 1)
    {ψ : AddChar (AdeleRing (𝓞 L) L) ℂ} (hψ : IsGlobalAddChar L ψ)
    {Φ : (Fin 2 → AdeleRing (𝓞 L) L) → ℂ} (hΦ : Φ ∈ schwartzBruhat2 L)
    (g : GL (Fin 2) (AdeleRing (𝓞 L) L)) :
    Summable (fun γ : ↥(sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ₀) =>
      Φ ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).mulVec fun i =>
        algebraMap L (AdeleRing (𝓞 L) L)
          ((((γ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L).mulVec v) i))) ∧
    Summable (fun γ : ↥(sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ₀) =>
      reflectPair ψ μ₁ Φ ((((Matrix.GeneralLinearGroup.det g)⁻¹ : (AdeleRing (𝓞 L) L)ˣ) :
          AdeleRing (𝓞 L) L) •
        (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).mulVec fun i =>
          algebraMap L (AdeleRing (𝓞 L) L)
            ((((γ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L).mulVec v) i))) ∧
    ∑' γ : ↥(sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ₀),
        Φ ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).mulVec fun i =>
          algebraMap L (AdeleRing (𝓞 L) L)
            ((((γ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L).mulVec v) i))
      + Φ 0 =
    (((ideleNorm L (Matrix.GeneralLinearGroup.det g))⁻¹ : ℝ) : ℂ) *
      (∑' γ : ↥(sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ₀),
          reflectPair ψ μ₁ Φ ((((Matrix.GeneralLinearGroup.det g)⁻¹ : (AdeleRing (𝓞 L) L)ˣ) :
              AdeleRing (𝓞 L) L) •
            (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).mulVec fun i =>
              algebraMap L (AdeleRing (𝓞 L) L)
                ((((γ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L).mulVec v) i))
        + reflectPair ψ μ₁ Φ 0) := by

  set gT : GL (Fin 2) (AdeleRing (𝓞 L) L) := trGL g with hgT
  set D : (AdeleRing (𝓞 L) L)ˣ := Matrix.GeneralLinearGroup.det g with hD
  set e := colEquiv K L h2 σ hgen δ₀ hN hns v hv with he

  set f₁ : (Fin 2 → L) → ℂ := fun ξ => Φ ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).mulVec
    fun i => algebraMap L (AdeleRing (𝓞 L) L) (ξ i)) with hf₁
  set f₂ : (Fin 2 → L) → ℂ := fun ξ =>
    reflectPair ψ μ₁ Φ (((D⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) •
      (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).mulVec
        fun i => algebraMap L (AdeleRing (𝓞 L) L) (ξ i)) with hf₂

  have hΨ₁ : (fun x : Fin 2 → AdeleRing (𝓞 L) L =>
      Φ (Matrix.vecMul x (gT : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)))) ∈ schwartzBruhat2 L :=
    (NumberField.AdelicFourier.continuous_integrable_comp_vecMul_mem_and_bottomRowVec_mem_schwartzBruhat_of_mem_schwartzBruhat2
      L Φ hΦ).2.2.2.2.1 gT
  have hΦ' : reflectPair ψ μ₁ Φ ∈ schwartzBruhat2 L :=
    (NumberField.AdelicFourier.fourierTransform2_mem_schwartzBruhat2_and_reflectPair_mem_schwartzBruhat2
      L μ₁ hψ hΦ).2
  have hΨ₂ : (fun x : Fin 2 → AdeleRing (𝓞 L) L => reflectPair ψ μ₁ Φ
      (Matrix.vecMul x ((Matrix.GeneralLinearGroup.scalar (Fin 2) D⁻¹ * gT : GL (Fin 2) (AdeleRing (𝓞 L) L)) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)))) ∈ schwartzBruhat2 L :=
    (NumberField.AdelicFourier.continuous_integrable_comp_vecMul_mem_and_bottomRowVec_mem_schwartzBruhat_of_mem_schwartzBruhat2
      L _ hΦ').2.2.2.2.1 _
  have hs₁ : Summable f₁ := by
    have := (NumberField.AdelicFourier.tsum_eq_inv_measure_sq_mul_tsum_fourierTransform2_of_mem_schwartzBruhat2
      L μ₁ hψ hΨ₁).1
    refine this.congr fun ξ => ?_
    rw [hf₁]
    dsimp only
    rw [hgT, vecMul_trGL]
  have hs₂ : Summable f₂ := by
    have := (NumberField.AdelicFourier.tsum_eq_inv_measure_sq_mul_tsum_fourierTransform2_of_mem_schwartzBruhat2
      L μ₁ hψ hΨ₂).1
    refine this.congr fun ξ => ?_
    rw [hf₂]
    dsimp only
    rw [vecMul_scalar_mul, hgT, vecMul_trGL]

  have hsub₁ : Summable (fun w : {w : Fin 2 → L // w ≠ 0} => f₁ w) := hs₁.subtype _
  have hsub₂ : Summable (fun w : {w : Fin 2 → L // w ≠ 0} => f₂ w) := hs₂.subtype _
  have hS₁ : Summable ((fun w : {w : Fin 2 → L // w ≠ 0} => f₁ w) ∘ e) := (Equiv.summable_iff e).2 hsub₁
  have hS₂ : Summable ((fun w : {w : Fin 2 → L // w ≠ 0} => f₂ w) ∘ e) := (Equiv.summable_iff e).2 hsub₂
  refine ⟨?_, ?_, ?_⟩
  · refine hS₁.congr fun γ => ?_
    rw [Function.comp_apply, hf₁, he, colEquiv_apply]
  · refine hS₂.congr fun γ => ?_
    rw [Function.comp_apply, hf₂, he, colEquiv_apply]

  have hθ := NumberField.AdelicFourier.tsum_apply_smul_vecMul_add_eq_ideleNorm_cpow_neg_two_mul_tsum_reflectPair_of_mem_schwartzBruhat2
    L μ₁ hμ₁ hψ hΦ gT 1
  have h1 : ((ideleNorm L (1 : (AdeleRing (𝓞 L) L)ˣ) : ℝ) : ℂ) ^ (-(2 : ℂ)) = 1 := by
    rw [show ideleNorm L (1 : (AdeleRing (𝓞 L) L)ˣ) = 1 from by simp [ideleNorm], Complex.ofReal_one,
      Complex.one_cpow]
  rw [h1, one_mul, det_trGL, ← hD, inv_one, one_mul] at hθ
  simp only [Units.val_one, one_smul, hgT, vecMul_trGL, ← mul_add] at hθ

  have lhs : ∑' γ : ↥(sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ₀),
        Φ ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).mulVec fun i =>
          algebraMap L (AdeleRing (𝓞 L) L) ((((γ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L).mulVec v) i))
      = ∑' w : {w : Fin 2 → L // w ≠ 0}, f₁ w := by
    rw [← Equiv.tsum_eq e (fun w : {w : Fin 2 → L // w ≠ 0} => f₁ w)]
    rfl
  have rhs : ∑' γ : ↥(sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ₀),
        reflectPair ψ μ₁ Φ (((D⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) •
          (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).mulVec fun i =>
            algebraMap L (AdeleRing (𝓞 L) L) ((((γ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L).mulVec v) i))
      = ∑' w : {w : Fin 2 → L // w ≠ 0}, f₂ w := by
    rw [← Equiv.tsum_eq e (fun w : {w : Fin 2 → L // w ≠ 0} => f₂ w)]
    rfl
  rw [lhs, rhs]
  exact hθ

end S_AutomorphicForm_tsum_sigmaCentralizer_apply_mulVec_add_eq_inv_ideleNorm_det_mul_tsum_reflectPair_of_forall_ne_scalar_of_finrank_eq_two
end P2MW
export P2MW.S_AutomorphicForm_tsum_sigmaCentralizer_apply_mulVec_add_eq_inv_ideleNorm_det_mul_tsum_reflectPair_of_forall_ne_scalar_of_finrank_eq_two (solution)
