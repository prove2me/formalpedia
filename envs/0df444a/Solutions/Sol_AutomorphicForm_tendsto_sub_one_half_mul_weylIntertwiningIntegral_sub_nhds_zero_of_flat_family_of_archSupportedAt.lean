-- Prove2me | solution 1 for AutomorphicForm.tendsto_sub_one_half_mul_weylIntertwiningIntegral_sub_nhds_zero_of_flat_family_of_archSupportedAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/30ac89bd-8a4b-50a4-b934-46913395b5f8

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_AdelicHaar
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.ReImTopology
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_AutomorphicForm_exists_meromorphicOn_partialEulerProduct_mul_weylIntertwiningIntegral_eq_mul
import Theorems.Thm_NumberField_multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one
import Theorems.Thm_NumberField_hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta
import Theorems.Thm_NumberField_exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero
import Theorems.Thm_NumberField_dedekindZeta_ne_zero_of_one_lt_re

import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.Asymptotics.Lemmas
import Theorems.Thm_EisensteinGeneral_Glue_integrable_mul_of_integrable_of_integrable
import Theorems.Thm_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod
import Theorems.Thm_EisensteinGeneral_LocalUnr_integrable_twisted_and_integral_norm_eq
import Theorems.Thm_NumberField_summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt
import Theorems.Thm_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family
import Theorems.Thm_AutomorphicForm_LocalIntertwining_integral_adeleRing_pureTensor_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod
import Theorems.Thm_AutomorphicForm_LocalIntertwining_bounded_and_tendsto_integral_weylShift_sub_integral_smoothAtom_adicCompletion
import Theorems.Thm_AutomorphicForm_LocalIntertwining_integrable_smoothAtom_and_integrable_weylShift_adicCompletion
import Theorems.Thm_AutomorphicForm_apply_weylInv_unipotent_mul_archSupportedAt_eq_norm_cpow_mul_apply
import Theorems.Thm_NumberField_AdelicHaar_adelicAddHaar_setOf_fst_apply_eq_eq_zero
import Theorems.Thm_AutomorphicForm_LocalIntertwining_bounded_and_tendsto_integral_moebiusShift_sub_integral_realAtom
import Theorems.Thm_AutomorphicForm_LocalIntertwining_bounded_and_tendsto_integral_moebiusShift_sub_integral_complexAtom
import Theorems.Thm_AutomorphicForm_LocalIntertwining_integrable_realAtom_and_integrable_moebiusShift
import Theorems.Thm_AutomorphicForm_LocalIntertwining_integrable_complexAtom_and_integrable_moebiusShift
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_tendsto_sub_one_half_mul_weylIntertwiningIntegral_sub_nhds_zero_of_flat_family_of_archSupportedAt
p2m_attr_erase "instance" "instCountableOfNumberField_definitions HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions"
p2m_attr_erase "instance" "NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add LocalGL2.swapUnit_val NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul"
p2m_attr_erase "simp" "IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.AdelicHaar NumberField.AdelicLevel IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel Filter Topology
open scoped NNReal
open Asymptotics

namespace A5Kit

open LanglandsTunnell.TateLocal

variable {F : Type} [Field F] [NumberField F]

private theorem finprod_eq_prod_mul_finprod_subtype {ι M : Type*} [CommMonoid M] (T : Finset ι)
    (f : ι → M) (hf : (Function.mulSupport f).Finite) :
    ∏ᶠ i, f i = (∏ i ∈ T, f i) * ∏ᶠ i : {i // i ∉ T}, f i.1 := by
  classical
  rw [← finprod_mem_univ, ← Set.union_compl_self (↑T : Set ι),
    finprod_mem_union' disjoint_compl_right (hf.subset Set.inter_subset_right)
      (hf.subset Set.inter_subset_right),
    finprod_mem_coe_finset]
  congr 1
  rw [← finprod_set_coe_eq_finprod_mem]
  rfl

private noncomputable def atom (v : HeightOneSpectrum (𝓞 F)) (A B : v.adicCompletion F → ℂ) (s : ℂ)
    (y : v.adicCompletion F) : ℂ :=
  (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator A y
    + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
        (fun y => (((modulus y : ℝ≥0) : ℝ) : ℂ) ^ (-(2 * s + 1)) * B y⁻¹) y

private noncomputable def finPart (T : Finset (HeightOneSpectrum (𝓞 F)))
    (χ : ∀ u : HeightOneSpectrum (𝓞 F), (u.adicCompletion F)ˣ →* ℂˣ)
    (h : ∀ u : HeightOneSpectrum (𝓞 F), u.adicCompletion F → ℂ) (s : ℂ)
    (x : FiniteAdeleRing (𝓞 F) F) : ℂ :=
  (∏ u ∈ T, h u (x u))
    * ∏ᶠ u : {u : HeightOneSpectrum (𝓞 F) // u ∉ T},
        ((u.1.adicCompletionIntegers F : Set (u.1.adicCompletion F)).indicator (fun _ => (1 : ℂ)) (x u.1)
          + (u.1.adicCompletionIntegers F : Set (u.1.adicCompletion F))ᶜ.indicator
              (fun y => charExt (χ u.1)⁻¹ y * ((modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))) (x u.1))

private noncomputable def tensor (T : Finset (HeightOneSpectrum (𝓞 F)))
    (χ : ∀ u : HeightOneSpectrum (𝓞 F), (u.adicCompletion F)ˣ →* ℂˣ)
    (f : mixedEmbedding.mixedSpace F → ℂ)
    (h : ∀ u : HeightOneSpectrum (𝓞 F), u.adicCompletion F → ℂ) (s : ℂ)
    (x : AdeleRing (𝓞 F) F) : ℂ :=
  f (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * finPart T χ h s x.2

private theorem ne_zero_of_notMem {v : HeightOneSpectrum (𝓞 F)} {y : v.adicCompletion F}
    (hy : y ∉ (v.adicCompletionIntegers F : Set (v.adicCompletion F))) : y ≠ 0 := by
  rintro rfl
  exact hy (zero_mem _)

private theorem levelAtom_eq_atom (v : HeightOneSpectrum (𝓞 F)) (χ : (v.adicCompletion F)ˣ →* ℂˣ)
    (hχ : ∀ y : v.adicCompletion F, y ≠ 0 → charExt χ⁻¹ y = 1)
    (A B : v.adicCompletion F → ℂ) (s : ℂ) (y : v.adicCompletion F) :
    (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator A y
      + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
          (fun y => charExt χ⁻¹ y * ((modulus y : ℝ) : ℂ) ^ (-(2 * s + 1)) * B y⁻¹) y
      = atom v A B s y := by
  unfold atom
  by_cases hy : y ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))
  · rw [Set.indicator_of_notMem (fun h : y ∈ (_ : Set _)ᶜ => h hy),
      Set.indicator_of_notMem (fun h : y ∈ (_ : Set _)ᶜ => h hy)]
  · rw [Set.indicator_of_mem (Set.mem_compl hy), Set.indicator_of_mem (Set.mem_compl hy),
      hχ y (ne_zero_of_notMem hy), one_mul]

private theorem unrAtom_eq_atom (v : HeightOneSpectrum (𝓞 F)) (χ : (v.adicCompletion F)ˣ →* ℂˣ)
    (hχ : ∀ y : v.adicCompletion F, y ≠ 0 → charExt χ⁻¹ y = 1) (s : ℂ) (y : v.adicCompletion F) :
    (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ => (1 : ℂ)) y
      + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
          (fun y => charExt χ⁻¹ y * ((modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))) y
      = atom v (fun _ => 1) (fun _ => 1) s y := by
  unfold atom
  by_cases hy : y ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))
  · rw [Set.indicator_of_notMem (fun h : y ∈ (_ : Set _)ᶜ => h hy),
      Set.indicator_of_notMem (fun h : y ∈ (_ : Set _)ᶜ => h hy)]
  · rw [Set.indicator_of_mem (Set.mem_compl hy), Set.indicator_of_mem (Set.mem_compl hy),
      hχ y (ne_zero_of_notMem hy), one_mul, mul_one]

private theorem unrAtom_eq_one (v : HeightOneSpectrum (𝓞 F)) (χ : (v.adicCompletion F)ˣ →* ℂˣ) (e : ℂ)
    (y : v.adicCompletion F) (hy : y ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :
    (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ => (1 : ℂ)) y
      + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
          (fun y => charExt χ⁻¹ y * ((modulus y : ℝ) : ℂ) ^ e) y = 1 := by
  rw [Set.indicator_of_mem hy, Set.indicator_of_notMem (fun h : y ∈ (_ : Set _)ᶜ => h hy), add_zero]

private theorem reindex (S T : Finset (HeightOneSpectrum (𝓞 F))) (hST : S ⊆ T)
    (χ : ∀ u : HeightOneSpectrum (𝓞 F), (u.adicCompletion F)ˣ →* ℂˣ)
    (hχ : ∀ (u : HeightOneSpectrum (𝓞 F)) (y : u.adicCompletion F), y ≠ 0 → charExt (χ u)⁻¹ y = 1)
    (A B A' B' : ∀ u : HeightOneSpectrum (𝓞 F), u.adicCompletion F → ℂ)
    (hA'S : ∀ u ∈ S, A' u = A u) (hB'S : ∀ u ∈ S, B' u = B u)
    (hA'c : ∀ u ∉ S, A' u = fun _ => 1) (hB'c : ∀ u ∉ S, B' u = fun _ => 1)
    (s : ℂ) (x : FiniteAdeleRing (𝓞 F) F) :
    (∏ u ∈ S, ((u.adicCompletionIntegers F : Set (u.adicCompletion F)).indicator (A u) (x u)
        + (u.adicCompletionIntegers F : Set (u.adicCompletion F))ᶜ.indicator
            (fun y => charExt (χ u)⁻¹ y * ((modulus y : ℝ) : ℂ) ^ (-(2 * s + 1)) * B u y⁻¹) (x u)))
      * ∏ᶠ u : {u : HeightOneSpectrum (𝓞 F) // u ∉ S},
          ((u.1.adicCompletionIntegers F : Set (u.1.adicCompletion F)).indicator (fun _ => (1 : ℂ)) (x u.1)
            + (u.1.adicCompletionIntegers F : Set (u.1.adicCompletion F))ᶜ.indicator
                (fun y => charExt (χ u.1)⁻¹ y * ((modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))) (x u.1))
    = finPart T χ (fun u => atom u (A' u) (B' u) s) s x := by
  unfold finPart
  set htot : HeightOneSpectrum (𝓞 F) → ℂ := fun u => atom u (A' u) (B' u) s (x u) with hhtot
  have hoff : ∀ u : HeightOneSpectrum (𝓞 F), u ∉ S → htot u =
      (u.adicCompletionIntegers F : Set (u.adicCompletion F)).indicator (fun _ => (1 : ℂ)) (x u)
        + (u.adicCompletionIntegers F : Set (u.adicCompletion F))ᶜ.indicator
            (fun y => charExt (χ u)⁻¹ y * ((modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))) (x u) := by
    intro u hu
    simp only [hhtot, hA'c u hu, hB'c u hu]
    exact (unrAtom_eq_atom u (χ u) (hχ u) s (x u)).symm
  have hsupp : (Function.mulSupport htot).Finite := by
    have hfin : {u : HeightOneSpectrum (𝓞 F) |
        x u ∉ (u.adicCompletionIntegers F : Set (u.adicCompletion F))}.Finite :=
      Filter.eventually_cofinite.1 x.2
    refine (S.finite_toSet.union hfin).subset fun u hu => ?_
    by_contra h'
    simp only [Set.mem_union, Finset.mem_coe, Set.mem_setOf_eq, not_or, not_not] at h'
    exact hu (by rw [hoff u h'.1]; exact unrAtom_eq_one u (χ u) _ (x u) h'.2)
  calc _ = (∏ u ∈ S, htot u) * ∏ᶠ u : {u : HeightOneSpectrum (𝓞 F) // u ∉ S}, htot u.1 := by
        congr 1
        · refine Finset.prod_congr rfl fun u hu => ?_
          simp only [hhtot, hA'S u hu, hB'S u hu]
          exact levelAtom_eq_atom u (χ u) (hχ u) (A u) (B u) s (x u)
        · exact finprod_congr fun u => (hoff u.1 u.2).symm
    _ = ∏ᶠ u, htot u := (finprod_eq_prod_mul_finprod_subtype S htot hsupp).symm
    _ = (∏ u ∈ T, htot u) * ∏ᶠ u : {u : HeightOneSpectrum (𝓞 F) // u ∉ T}, htot u.1 :=
        finprod_eq_prod_mul_finprod_subtype T htot hsupp
    _ = _ := by
        congr 1
        exact finprod_congr fun u => hoff u.1 (fun h => u.2 (hST h))

private theorem two_le_absNorm (v : HeightOneSpectrum (𝓞 F)) : 2 ≤ Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  omega

private theorem norm_cpow_lt_one (v : HeightOneSpectrum (𝓞 F)) (s : ℂ) (hs : 0 < s.re) :
    ‖(((1 : (v.adicCompletion F)ˣ →* ℂˣ) 1 : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))‖ < 1 := by
  have h2 : (2 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by exact_mod_cast two_le_absNorm v
  rw [MonoidHom.one_apply, Units.val_one, one_mul,
    Complex.norm_natCast_cpow_of_pos (by have := two_le_absNorm v; omega) (-(2 * s))]
  have hre : (-(2 * s)).re = -(2 * s.re) := by simp
  rw [hre]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)

private theorem unrTwisted_eq_atom (v : HeightOneSpectrum (𝓞 F)) (s : ℂ) (x : v.adicCompletion F) :
    ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ => (1 : ℂ)) x
        + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
            (fun y => charExt (1 : (v.adicCompletion F)ˣ →* ℂˣ)⁻¹ y * ((modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))) x)
      * (1 : AddChar (v.adicCompletion F) ℂ) (-(0 * x))
      = atom v (fun _ => 1) (fun _ => 1) s x := by
  rw [AddChar.one_apply, mul_one]
  exact unrAtom_eq_atom v 1 (fun y hy => by
    rw [charExt_of_ne_zero _ hy, MonoidHom.inv_apply, MonoidHom.one_apply, inv_one, Units.val_one]) s x

private theorem integrable_atom_one_and_term_le
    (v : HeightOneSpectrum (𝓞 F)) [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (ϖ : (v.adicCompletion F)ˣ) (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (s : ℂ) (hs : 1 / 2 < s.re) :
    Integrable (atom v (fun _ => 1) (fun _ => 1) s) μ ∧
    0 ≤ (μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)))⁻¹
          * (∫ y, ‖atom v (fun _ => 1) (fun _ => 1) s y‖ ∂μ) - 1 ∧
      (μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)))⁻¹
          * (∫ y, ‖atom v (fun _ => 1) (fun _ => 1) s y‖ ∂μ) - 1
        ≤ (1 - (2 : ℝ) ^ (-(2 * s.re)))⁻¹ * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re)) := by
  have hs0 : 0 < s.re := by linarith
  obtain ⟨hint, hval⟩ := EisensteinGeneral.LocalUnr.integrable_twisted_and_integral_norm_eq F v μ ϖ hϖ 1
    (fun _ _ => rfl) s (norm_cpow_lt_one v s hs0) 1 0 (fun _ _ => AddChar.one_apply _) 0
  refine ⟨hint.congr (ae_of_all _ fun x => unrTwisted_eq_atom v _ x), ?_⟩
  have heq : (fun y => ‖atom v (fun _ => 1) (fun _ => 1) s y‖) = fun x =>
      ‖((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ => (1 : ℂ)) x
        + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
            (fun y => charExt (1 : (v.adicCompletion F)ˣ →* ℂˣ)⁻¹ y
              * ((modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))) x)
        * (1 : AddChar (v.adicCompletion F) ℂ) (-(0 * x))‖ :=
    funext fun x => by rw [unrTwisted_eq_atom]
  have hq0 : (2 : ℝ) ^ (-(2 * s.re)) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hN2 : (2 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by exact_mod_cast two_le_absNorm v
  have hN1 : (1 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by linarith
  have hq : ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)
  have hqq0 : ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re)) ≤ (2 : ℝ) ^ (-(2 * s.re)) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hN2 (by linarith)
  have hp0 : 0 ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re + 1)) := Real.rpow_nonneg (by linarith) _
  have hpq : ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re + 1))
      ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re)) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hOopen : IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    (Fact.out : ∀ v : HeightOneSpectrum (𝓞 F), IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) v
  have hOcpt : IsCompact (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    isCompact_iff_compactSpace.mpr (show CompactSpace (v.adicCompletionIntegers F) from inferInstance)
  have hvol : 0 < μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    ENNReal.toReal_pos ((hOopen.measure_pos μ ⟨0, zero_mem _⟩).ne') hOcpt.measure_lt_top.ne
  rw [MonoidHom.one_apply, Units.val_one, norm_one, one_mul, one_mul] at hval
  have hI : ∫ y, ‖atom v (fun _ => 1) (fun _ => 1) s y‖ ∂μ
      = μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F))
        * (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re + 1)))
        * (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re)))⁻¹ := by
    rw [heq]; exact hval
  have hB : (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re))) ≠ 0 := by linarith
  have hterm : (μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)))⁻¹
        * (∫ y, ‖atom v (fun _ => 1) (fun _ => 1) s y‖ ∂μ) - 1
      = (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re))
          - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re + 1)))
        / (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re))) := by
    rw [hI]
    field_simp
    ring
  refine ⟨?_, ?_⟩
  · rw [hterm]
    exact div_nonneg (by linarith) (by linarith)
  rw [hterm, div_eq_mul_inv, mul_comm]
  have h1 : (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re)))⁻¹ ≤ (1 - (2 : ℝ) ^ (-(2 * s.re)))⁻¹ :=
    inv_anti₀ (by linarith) (by linarith)
  calc (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re)))⁻¹
        * (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re))
            - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re + 1)))
      ≤ (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re)))⁻¹
        * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re)) :=
        mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.2 (by linarith))
    _ ≤ (1 - (2 : ℝ) ^ (-(2 * s.re)))⁻¹ * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re)) :=
        mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (by linarith) _)

open scoped Classical in

private theorem integrable_finitePart
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (νf : Measure (FiniteAdeleRing (𝓞 F) F)) [νf.IsAddHaarMeasure]
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
    [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
    (μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (v.adicCompletion F)) [∀ v, (μv v).IsAddHaarMeasure]
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ)
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (T : Finset (HeightOneSpectrum (𝓞 F)))
    (χ : ∀ u : HeightOneSpectrum (𝓞 F), (u.adicCompletion F)ˣ →* ℂˣ)
    (hχ : ∀ (u : HeightOneSpectrum (𝓞 F)) (y : u.adicCompletion F), y ≠ 0 → charExt (χ u)⁻¹ y = 1)
    (h : ∀ u : HeightOneSpectrum (𝓞 F), u.adicCompletion F → ℂ)
    (s : ℂ) (hs : 1 / 2 < s.re) (hint : ∀ u ∈ T, Integrable (h u) (μv u)) :
    Integrable (finPart T χ h s) νf := by
  set hfull : ∀ u : HeightOneSpectrum (𝓞 F), u.adicCompletion F → ℂ :=
    fun u => if u ∈ T then h u else atom u (fun _ => 1) (fun _ => 1) s with hhfull
  have hon : ∀ u ∈ T, hfull u = h u := fun u hu => by simp only [hhfull, if_pos hu]
  have hoff : ∀ u ∉ T, hfull u = atom u (fun _ => 1) (fun _ => 1) s := fun u hu => by
    simp only [hhfull, if_neg hu]
  have h₁ : ∀ u ∉ T, ∀ y : u.adicCompletion F, y ∈ u.adicCompletionIntegers F → hfull u y = 1 := by
    intro u hu y hy
    rw [hoff u hu, ← unrAtom_eq_atom u (χ u) (hχ u)]
    exact unrAtom_eq_one u (χ u) _ y hy
  have hint' : ∀ u, Integrable (hfull u) (μv u) := by
    intro u
    by_cases hu : u ∈ T
    · rw [hon u hu]; exact hint u hu
    · rw [hoff u hu]; exact (integrable_atom_one_and_term_le u (μv u) (ϖ u) (hϖ u) s hs).1
  have hsum : Summable fun u : {u : HeightOneSpectrum (𝓞 F) // u ∉ T} =>
      ((μv u.1).real (u.1.adicCompletionIntegers F : Set (u.1.adicCompletion F)))⁻¹
          * (∫ y, ‖hfull u.1 y‖ ∂(μv u.1)) - 1 := by
    have hmaj : Summable fun u : {u : HeightOneSpectrum (𝓞 F) // u ∉ T} =>
        (1 - (2 : ℝ) ^ (-(2 * s.re)))⁻¹ * ((Ideal.absNorm u.1.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re)) :=
      ((NumberField.summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt F
        (σ := 2 * s.re) (by linarith)).subtype {u | u ∉ T}).mul_left _
    refine Summable.of_nonneg_of_le (fun u => ?_) (fun u => ?_) hmaj
    · rw [hoff u.1 u.2]; exact (integrable_atom_one_and_term_le u.1 (μv u.1) (ϖ u.1) (hϖ u.1) s hs).2.1
    · rw [hoff u.1 u.2]; exact (integrable_atom_one_and_term_le u.1 (μv u.1) (ϖ u.1) (hϖ u.1) s hs).2.2
  have hfin := (EisensteinGeneral.Factorization.integrable_finprod_and_inv_measure_mul_integral_eq_tprod F νf T μv
    hfull h₁ hint' hsum).1
  refine hfin.congr (ae_of_all _ fun x => ?_)
  have hsupp : (Function.mulSupport fun u => hfull u (x u)).Finite := by
    have hfin' : {u : HeightOneSpectrum (𝓞 F) |
        x u ∉ (u.adicCompletionIntegers F : Set (u.adicCompletion F))}.Finite :=
      Filter.eventually_cofinite.1 x.2
    refine (T.finite_toSet.union hfin').subset fun u hu => ?_
    by_contra h'
    simp only [Set.mem_union, Finset.mem_coe, Set.mem_setOf_eq, not_or, not_not] at h'
    exact hu (h₁ u h'.1 (x u) h'.2)
  show ∏ᶠ u, hfull u (x u) = _
  unfold finPart
  rw [finprod_eq_prod_mul_finprod_subtype T _ hsupp]
  congr 1
  · exact Finset.prod_congr rfl fun u hu => by rw [hon u hu]
  · exact finprod_congr fun u => by rw [hoff u.1 u.2, ← unrAtom_eq_atom u.1 (χ u.1) (hχ u.1)]

open scoped Classical in

private theorem integrable_tensor
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (νf : Measure (FiniteAdeleRing (𝓞 F) F)) [νf.IsAddHaarMeasure]
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
    [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
    (μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (v.adicCompletion F)) [∀ v, (μv v).IsAddHaarMeasure]
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ)
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (T : Finset (HeightOneSpectrum (𝓞 F)))
    (χ : ∀ u : HeightOneSpectrum (𝓞 F), (u.adicCompletion F)ˣ →* ℂˣ)
    (hχ : ∀ (u : HeightOneSpectrum (𝓞 F)) (y : u.adicCompletion F), y ≠ 0 → charExt (χ u)⁻¹ y = 1)
    (h : ∀ u : HeightOneSpectrum (𝓞 F), u.adicCompletion F → ℂ)
    (f : mixedEmbedding.mixedSpace F → ℂ) (hf : Integrable f)
    (s : ℂ) (hs : 1 / 2 < s.re) (hint : ∀ u ∈ T, Integrable (h u) (μv u)) :
    letI := NumberField.AdelicHaar.adeleBorel (𝓞 F) F
    Integrable (tensor T χ f h s) (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) := by
  letI := NumberField.AdelicHaar.adeleBorel (𝓞 F) F
  haveI : BorelSpace (AdeleRing (𝓞 F) F) := NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 F) F
  haveI := NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar (𝓞 F) F
  exact EisensteinGeneral.Glue.integrable_mul_of_integrable_of_integrable F
    (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) νf f (finPart T χ h s) hf
    (integrable_finitePart νf μv ϖ hϖ T χ hχ h s hs hint)

open scoped Classical in

private noncomputable def archProd
    (fr : {w : InfinitePlace F // w.IsReal} → ℝ → ℂ)
    (fc : {w : InfinitePlace F // w.IsComplex} → ℂ → ℂ)
    (y : mixedEmbedding.mixedSpace F) : ℂ :=
  (∏ i, fr i (y.1 i)) * (∏ w, fc w (y.2 w))

open scoped Classical in

private theorem integral_archProd
    (fr : {w : InfinitePlace F // w.IsReal} → ℝ → ℂ)
    (fc : {w : InfinitePlace F // w.IsComplex} → ℂ → ℂ) :
    ∫ y, archProd fr fc y = (∏ i, ∫ x, fr i x) * (∏ w, ∫ z, fc w z) := by
  unfold archProd
  rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.integral_prod_mul
    (f := fun x : {w : InfinitePlace F // w.IsReal} → ℝ => ∏ i, fr i (x i))
    (g := fun z : {w : InfinitePlace F // w.IsComplex} → ℂ => ∏ w, fc w (z w))]
  congr 1
  · rw [MeasureTheory.volume_pi]
    exact MeasureTheory.integral_fintype_prod_eq_prod (f := fun i (x : ℝ) => fr i x)
  · rw [MeasureTheory.volume_pi]
    exact MeasureTheory.integral_fintype_prod_eq_prod (f := fun w (z : ℂ) => fc w z)

open scoped Classical in

private theorem integrable_archProd
    (fr : {w : InfinitePlace F // w.IsReal} → ℝ → ℂ)
    (fc : {w : InfinitePlace F // w.IsComplex} → ℂ → ℂ)
    (hfr : ∀ i, Integrable (fr i)) (hfc : ∀ w, Integrable (fc w)) :
    Integrable (archProd fr fc) := by
  unfold archProd
  rw [MeasureTheory.Measure.volume_eq_prod]
  refine Integrable.mul_prod
    (f := fun x : {w : InfinitePlace F // w.IsReal} → ℝ => ∏ i, fr i (x i))
    (g := fun z : {w : InfinitePlace F // w.IsComplex} → ℂ => ∏ w, fc w (z w)) ?_ ?_
  · rw [MeasureTheory.volume_pi]
    exact Integrable.fintype_prod (f := fun i (x : ℝ) => fr i x) hfr
  · rw [MeasureTheory.volume_pi]
    exact Integrable.fintype_prod (f := fun w (z : ℂ) => fc w z) hfc

private noncomputable def rAtom (k : ℤ) (σ : ℝ) (x : ℝ) : ℂ :=
  ((((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ k * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-((σ : ℂ) + 1 / 2))

private noncomputable def cAtom (a b m : ℕ) (σ : ℝ) (z : ℂ) : ℂ :=
  z ^ a * (starRingEnd ℂ) z ^ b * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-(2 * (σ : ℂ) + 1) - ((m : ℂ)) / 2)

private noncomputable def rJ (a b c d : ℝ) (σ : ℝ) (x : ℝ) : ℂ :=
  ((|a * d - b * c| : ℝ) : ℂ) ^ ((σ : ℂ) + 1 / 2) * ((|a + x * c| : ℝ) : ℂ) ^ (-(2 * (σ : ℂ) + 1))

private noncomputable def cJ (a b c d : ℂ) (σ : ℝ) (z : ℂ) : ℂ :=
  ((‖a * d - b * c‖ ^ 2 : ℝ) : ℂ) ^ ((σ : ℂ) + 1 / 2) * ((‖a + z * c‖ ^ 2 : ℝ) : ℂ) ^ (-(2 * (σ : ℂ) + 1))

open scoped Classical in

private theorem arch_eq_archProd (kdat : {w : InfinitePlace F // w.IsReal} → ℤ)
    (abm : {w : InfinitePlace F // w.IsComplex} → ℕ × ℕ × ℕ)
    (Rr : {w : InfinitePlace F // w.IsReal} → ℝ → ℂ)
    (Rc : {w : InfinitePlace F // w.IsComplex} → ℝ → ℂ)
    (hRr : ∀ i (t : ℝ), 0 < t → Rr i t = 1) (hRc : ∀ w (t : ℝ), 0 < t → Rc w t = 1)
    (σ : ℝ) (x : InfiniteAdeleRing F) :
    (∏ i : {w : InfinitePlace F // w.IsReal},
        Rr i ((1 + Completion.extensionEmbeddingOfIsReal i.2 (x i.1) ^ 2) ^ (-(1 / 2 : ℝ)))
          * ((((Completion.extensionEmbeddingOfIsReal i.2 (x i.1) : ℝ) : ℂ) - Complex.I)
              / ((Real.sqrt (1 + Completion.extensionEmbeddingOfIsReal i.2 (x i.1) ^ 2) : ℝ) : ℂ)) ^ (kdat i)
          * (((1 + Completion.extensionEmbeddingOfIsReal i.2 (x i.1) ^ 2 : ℝ) : ℂ)) ^ (-((σ : ℂ) + 1 / 2)))
      * (∏ w : {w : InfinitePlace F // w.IsComplex},
          Rc w ((1 + ‖Completion.extensionEmbedding w.1 (x w.1)‖ ^ 2) ^ (-(1 / 2 : ℝ)))
            * Completion.extensionEmbedding w.1 (x w.1) ^ (abm w).1
            * (starRingEnd ℂ) (Completion.extensionEmbedding w.1 (x w.1)) ^ (abm w).2.1
            * (((1 + ‖Completion.extensionEmbedding w.1 (x w.1)‖ ^ 2 : ℝ) : ℂ))
                ^ (-(2 * (σ : ℂ) + 1) - ((abm w).2.2 : ℂ) / 2))
      = archProd (fun i => rAtom (kdat i) σ) (fun w => cAtom (abm w).1 (abm w).2.1 (abm w).2.2 σ)
          (InfiniteAdeleRing.ringEquiv_mixedSpace F x) := by
  rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  unfold archProd rAtom cAtom
  dsimp only
  congr 1
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [hRr i _ (Real.rpow_pos_of_pos (by positivity) _), one_mul]
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [hRc w _ (Real.rpow_pos_of_pos (by positivity) _), one_mul]

open scoped Classical in

private theorem transport_arch
    (fr fr' : {w : InfinitePlace F // w.IsReal} → ℝ → ℂ)
    (fc fc' : {w : InfinitePlace F // w.IsComplex} → ℂ → ℂ)
    (w : InfinitePlace F) (x : InfiniteAdeleRing F) (t : w.Completion) (M : ℂ)
    (hr : ∀ i : {w : InfinitePlace F // w.IsReal}, i.1 = w →
      M * fr i (Completion.extensionEmbeddingOfIsReal i.2 (Function.update x w t i.1))
        = fr' i (Completion.extensionEmbeddingOfIsReal i.2 (x i.1)))
    (hr' : ∀ i : {w : InfinitePlace F // w.IsReal}, i.1 ≠ w → fr' i = fr i)
    (hc : ∀ v : {w : InfinitePlace F // w.IsComplex}, v.1 = w →
      M * fc v (Completion.extensionEmbedding v.1 (Function.update x w t v.1))
        = fc' v (Completion.extensionEmbedding v.1 (x v.1)))
    (hc' : ∀ v : {w : InfinitePlace F // w.IsComplex}, v.1 ≠ w → fc' v = fc v) :
    M * archProd fr fc (InfiniteAdeleRing.ringEquiv_mixedSpace F (Function.update x w t))
      = archProd fr' fc' (InfiniteAdeleRing.ringEquiv_mixedSpace F x) := by
  rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  unfold archProd
  dsimp only
  rcases w.isReal_or_isComplex with hw | hw
  ·
    set i₀ : {w : InfinitePlace F // w.IsReal} := ⟨w, hw⟩ with hi₀
    have hrest : ∏ i ∈ Finset.univ.erase i₀, fr i (Completion.extensionEmbeddingOfIsReal i.2 (Function.update x w t i.1))
        = ∏ i ∈ Finset.univ.erase i₀, fr' i (Completion.extensionEmbeddingOfIsReal i.2 (x i.1)) := by
      refine Finset.prod_congr rfl fun i hi => ?_
      have hne : i.1 ≠ w := fun h => Finset.ne_of_mem_erase hi (Subtype.ext h)
      rw [Function.update_of_ne hne, hr' i hne]
    have hcx : ∏ v : {w : InfinitePlace F // w.IsComplex}, fc v (Completion.extensionEmbedding v.1 (Function.update x w t v.1))
        = ∏ v : {w : InfinitePlace F // w.IsComplex}, fc' v (Completion.extensionEmbedding v.1 (x v.1)) := by
      refine Finset.prod_congr rfl fun v _ => ?_
      have hne : v.1 ≠ w := fun h => not_isReal_iff_isComplex.mpr v.2 (h ▸ hw)
      rw [Function.update_of_ne hne, hc' v hne]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀),
      ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀), hrest, hcx, ← hr i₀ rfl]
    ring
  ·
    set v₀ : {w : InfinitePlace F // w.IsComplex} := ⟨w, hw⟩ with hv₀
    have hrest : ∏ v ∈ Finset.univ.erase v₀, fc v (Completion.extensionEmbedding v.1 (Function.update x w t v.1))
        = ∏ v ∈ Finset.univ.erase v₀, fc' v (Completion.extensionEmbedding v.1 (x v.1)) := by
      refine Finset.prod_congr rfl fun v hv => ?_
      have hne : v.1 ≠ w := fun h => Finset.ne_of_mem_erase hv (Subtype.ext h)
      rw [Function.update_of_ne hne, hc' v hne]
    have hrx : ∏ i : {w : InfinitePlace F // w.IsReal}, fr i (Completion.extensionEmbeddingOfIsReal i.2 (Function.update x w t i.1))
        = ∏ i : {w : InfinitePlace F // w.IsReal}, fr' i (Completion.extensionEmbeddingOfIsReal i.2 (x i.1)) := by
      refine Finset.prod_congr rfl fun i _ => ?_
      have hne : i.1 ≠ w := fun h => not_isReal_iff_isComplex.mpr (h ▸ hw : i.1.IsComplex) i.2
      rw [Function.update_of_ne hne, hr' i hne]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v₀),
      ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v₀), hrest, hrx, ← hc v₀ rfl]
    ring

private theorem isBigO_and_tendsto_prod_sub_prod {ι : Type*} (s : Finset ι) {l : Filter ℝ}
    (a a' : ι → ℝ → ℂ)
    (ha : ∀ i ∈ s, a i =O[l] (fun _ => (1 : ℝ)))
    (hd : ∀ i ∈ s, Tendsto (fun σ => a' i σ - a i σ) l (𝓝 0)) :
    (fun σ => ∏ i ∈ s, a' i σ) =O[l] (fun _ => (1 : ℝ)) ∧
      Tendsto (fun σ => ∏ i ∈ s, a' i σ - ∏ i ∈ s, a i σ) l (𝓝 0) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨?_, ?_⟩
    · simp only [Finset.prod_empty]; exact isBigO_const_const _ one_ne_zero _
    · simp only [Finset.prod_empty, sub_self]; exact tendsto_const_nhds
  | insert j s hj ih =>
    obtain ⟨hP', hdP⟩ := ih (fun i hi => ha i (Finset.mem_insert_of_mem hi))
      (fun i hi => hd i (Finset.mem_insert_of_mem hi))
    have haj : a j =O[l] (fun _ => (1 : ℝ)) := ha j (Finset.mem_insert_self j s)
    have hdj : (fun σ => a' j σ - a j σ) =o[l] (fun _ => (1 : ℝ)) :=
      (isLittleO_one_iff ℝ).2 (hd j (Finset.mem_insert_self j s))
    have ha'j : a' j =O[l] (fun _ => (1 : ℝ)) :=
      (haj.add hdj.isBigO).congr' (Eventually.of_forall fun σ => by simp) EventuallyEq.rfl
    have hP : (fun σ => ∏ i ∈ s, a i σ) =O[l] (fun _ => (1 : ℝ)) :=
      (hP'.sub ((isLittleO_one_iff ℝ).2 hdP).isBigO).congr' (Eventually.of_forall fun σ => by simp) EventuallyEq.rfl
    refine ⟨?_, ?_⟩
    · have h := ha'j.mul hP'
      simp only [mul_one] at h
      exact h.congr' (Eventually.of_forall fun σ => by simp only [Finset.prod_insert hj]) EventuallyEq.rfl
    · have h1 : (fun σ => a' j σ * (∏ i ∈ s, a' i σ - ∏ i ∈ s, a i σ)) =o[l] (fun _ => (1 : ℝ)) := by
        have := ha'j.mul_isLittleO ((isLittleO_one_iff ℝ).2 hdP)
        simpa only [mul_one] using this
      have h2 : (fun σ => (a' j σ - a j σ) * ∏ i ∈ s, a i σ) =o[l] (fun _ => (1 : ℝ)) := by
        have := hdj.mul_isBigO hP
        simpa only [mul_one] using this
      have h := (isLittleO_one_iff ℝ).1 (h1.add h2)
      refine h.congr fun σ => ?_
      rw [Finset.prod_insert hj, Finset.prod_insert hj]
      ring

private theorem tendsto_zero_of_parts {ι : Type*} (S : Finset ι) {l : Filter ℝ}
    (E : ℝ → ℂ) (K : ℂ) (c : ι → ℂ) (PI dI : ι → ℝ → ℂ)
    (hE : E =O[l] (fun _ => (1 : ℝ)))
    (hPI : ∀ j ∈ S, PI j =O[l] (fun _ => (1 : ℝ))) (hdI : ∀ j ∈ S, Tendsto (dI j) l (𝓝 0)) :
    Tendsto (fun σ => E σ * K * ∑ j ∈ S, c j * (PI j σ * dI j σ)) l (𝓝 0) := by
  have hsum : (fun σ => ∑ j ∈ S, c j * (PI j σ * dI j σ)) =o[l] (fun _ => (1 : ℝ)) := by
    rw [← Finset.sum_fn]
    refine IsLittleO.sum fun j hj => ?_
    have h1 : (dI j) =o[l] (fun _ => (1 : ℝ)) := (isLittleO_one_iff ℝ).2 (hdI j hj)
    have h4 := ((isBigO_const_const (c j) (one_ne_zero : (1 : ℝ) ≠ 0) l).mul_isLittleO
      ((hPI j hj).mul_isLittleO h1))
    exact h4.congr_right fun _ => by norm_num
  have hK : (fun _ : ℝ => K) =O[l] (fun _ => (1 : ℝ)) := isBigO_const_const _ one_ne_zero _
  have h : (fun σ => E σ * K * ∑ j ∈ S, c j * (PI j σ * dI j σ)) =o[l] (fun _ => (1 : ℝ)) :=
    ((hE.mul hK).mul_isLittleO hsum).congr_right fun _ => by norm_num
  exact (isLittleO_one_iff ℝ).1 h

end A5Kit

private theorem hasProd_of_hasProd_inv' {ι : Type*} (f : ι → ℂ) {a : ℂ} (ha : a ≠ 0)
    (h : HasProd (fun i => (f i)⁻¹) a) : HasProd f a⁻¹ := by
  unfold HasProd at h ⊢
  have h' := h.inv₀ ha
  refine h'.congr (fun T => ?_)
  simp [Finset.prod_inv_distrib]

set_option maxHeartbeats 3200000 in
theorem solution
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
      (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst 1 α hα s) (etaSnd 1 α hα s) (φ s))
      (_hφK : ∀ s, IsArchKFinite F (φ s))
      (_hφf : ∀ s, IsKfSmooth F (φ s))
      (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
      (_hφhol : ∀ g, Differentiable ℂ (fun s => φ s g))
      (_hφflat : ∀ (s s' : ℂ) (k : AdelicGL2 (𝓞 F) F),
          glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
          (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
          φ s k = φ s' k)
      (w : InfinitePlace F) (k : AdelicGL2 (𝓞 F) F)
      (_hkf : glFin (𝓞 F) F k = 1)
      (_hka : ∀ w' : InfinitePlace F, w' ≠ w → archComponent F w' (glArch (𝓞 F) F k) = 1)
      (_hkw : IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))),
    letI := NumberField.AdelicHaar.adeleBorel (𝓞 F) F
    Tendsto (fun s : ℂ => (s - 1 / 2) *
        (weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) k
          - weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) 1))
      (𝓝[{s : ℂ | 1 / 2 < s.re}] (1 / 2 : ℂ)) (𝓝 0) := by
  intro α hα φ hφ hφK hφf hφjc hφhol hφflat w k hkf hka hkw
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := NumberField.AdelicHaar.adeleBorel (𝓞 F) F
  haveI : BorelSpace (AdeleRing (𝓞 F) F) := NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 F) F
  set U : Set ℂ := {s : ℂ | 1 / 2 < s.re} with hU

  have hN : ∀ v : HeightOneSpectrum (𝓞 F), (1 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
    intro v
    have h1 : 1 < Ideal.absNorm v.asIdeal := by
      rw [Nat.one_lt_iff_ne_zero_and_ne_one]
      exact ⟨by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot,
        by rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top⟩
    exact_mod_cast h1
  have hNC : ∀ v : HeightOneSpectrum (𝓞 F), (((Ideal.absNorm v.asIdeal : ℕ) : ℂ)) ≠ 0 := fun v => by
    exact_mod_cast (lt_trans zero_lt_one (hN v)).ne'
  have h1u : IsUnitaryChar (𝓞 F) F (1 : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) := fun x => by simp
  have hO0 : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have h2an : ∀ x : ℂ, AnalyticAt ℂ (fun s : ℂ => 2 * s) x := fun x => analyticAt_const.mul analyticAt_id
  have h21an : ∀ x : ℂ, AnalyticAt ℂ (fun s : ℂ => 2 * s + 1) x := fun x =>
    (h2an x).add analyticAt_const
  let FS : Finset (HeightOneSpectrum (𝓞 F)) → ℂ → ℂ := fun S w =>
    ∏ v ∈ S, (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w))
  have hFSdiff : ∀ S, Differentiable ℂ (FS S) := by
    intro S w
    show DifferentiableAt ℂ (fun w : ℂ => ∏ v ∈ S, (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w))) w
    refine DifferentiableAt.fun_finsetProd (fun v _ => ?_)
    exact (differentiableAt_const _).sub (differentiableAt_id.neg.const_cpow (Or.inl (hNC v)))
  have hFSan : ∀ S (x : ℂ), AnalyticAt ℂ (FS S) x := fun S x => (hFSdiff S).analyticAt x
  have hFSne : ∀ S (w : ℂ), 0 < w.re → FS S w ≠ 0 := by
    intro S w hw
    show (∏ v ∈ S, (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w))) ≠ 0
    refine Finset.prod_ne_zero_iff.mpr (fun v _ => ?_)
    have hpos : 0 < Ideal.absNorm v.asIdeal := by exact_mod_cast (lt_trans zero_lt_one (hN v))
    have hlt : ‖((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w)‖ < 1 := by
      rw [Complex.norm_natCast_cpow_of_pos hpos, Complex.neg_re]
      exact Real.rpow_lt_one_of_one_lt_of_neg (hN v) (by linarith)
    intro h
    rw [sub_eq_zero] at h
    rw [← h, norm_one] at hlt
    exact lt_irrefl _ hlt
  obtain ⟨Rζ, hRζd, hRζ1, hRζeq, -⟩ :=
    NumberField.exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero F
  have hRζan : ∀ x : ℂ, AnalyticAt ℂ Rζ x := fun x => hRζd.analyticAt x
  let ζc : ℂ → ℂ := fun w => Rζ w / (w - 1)
  have hζc_eq : ∀ w : ℂ, 1 < w.re → ζc w = NumberField.dedekindZeta F w := by
    intro w hw
    have hw1 : w - 1 ≠ 0 := by
      intro h; rw [sub_eq_zero] at h; rw [h] at hw; norm_num at hw
    simp only [ζc, hRζeq w hw]
    field_simp
  have hζcan : ∀ w : ℂ, w ≠ 1 → AnalyticAt ℂ ζc w := fun w hw =>
    (hRζan w).div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hw)
  have hζcne : ∀ w : ℂ, 1 < w.re → ζc w ≠ 0 := fun w hw => by
    rw [hζc_eq w hw]; exact NumberField.dedekindZeta_ne_zero_of_one_lt_re F hw
  have hpartial : ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (w : ℂ), 1 < w.re →
      NumberField.dedekindZeta F w * FS S w ≠ 0 ∧
      (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
          (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-w))) = (NumberField.dedekindZeta F w * FS S w)⁻¹ := by
    intro S w hw
    have hFSw : FS S w ≠ 0 := hFSne S w (by linarith)
    have hζ : NumberField.dedekindZeta F w ≠ 0 := NumberField.dedekindZeta_ne_zero_of_one_lt_re F hw
    have hne : NumberField.dedekindZeta F w * FS S w ≠ 0 := mul_ne_zero hζ hFSw
    refine ⟨hne, ?_⟩
    have hall := NumberField.hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta F w hw
    set f : HeightOneSpectrum (𝓞 F) → ℂ := fun v => (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w))⁻¹
      with hf_def
    obtain ⟨hmul1, -, -⟩ := NumberField.multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one
      F S (fun _ => 1) (fun _ => by simp)
    have hm : Multipliable (fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} => f v.1) := by
      simpa only [hf_def, one_mul] using hmul1 w hw
    have hb : HasProd (f ∘ (↑) : ((↑S : Set (HeightOneSpectrum (𝓞 F)))ᶜ : Set _) → ℂ)
        (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, f v.1) := hm.hasProd
    have hS := Finset.hasProd S f
    have hfull := hS.mul_compl hb
    have hall' : HasProd f (NumberField.dedekindZeta F w) := hall
    have huniq := hall'.unique hfull
    have hprodS : ∏ b ∈ S, f b = (FS S w)⁻¹ := by
      simp only [hf_def, Finset.prod_inv_distrib]
      rfl
    have hval : (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, f v.1) =
        NumberField.dedekindZeta F w * FS S w := by
      rw [hprodS] at huniq
      field_simp at huniq
      exact huniq.symm
    have hcompl : HasProd (fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} =>
        (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-w))⁻¹)
        (NumberField.dedekindZeta F w * FS S w) := by
      rw [← hval]; exact hm.hasProd
    exact (hasProd_of_hasProd_inv' _ hne hcompl).tprod_eq

  have hJg : ∀ g : AdelicGL2 (𝓞 F) F, ∃ J : ℂ → ℂ, AnalyticAt ℂ J (1 / 2) ∧
      ∀ s : ℂ, 1 / 2 < s.re → J s = (s - 1 / 2) * weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) g := by
    intro g
    obtain ⟨T, ϖ₁, hϖ₁, R, hRmero, hRdiff, hRid⟩ :=
      AutomorphicForm.exists_meromorphicOn_partialEulerProduct_mul_weylIntertwiningIntegral_eq_mul
        F hα 1 1 h1u h1u φ hφ hφK hφf hφjc hφhol g
    have hloc : ∀ (v : HeightOneSpectrum (𝓞 F)) (u : (v.adicCompletion F)ˣ),
        ((NumberField.TateGlobal.localChar (1 * 1⁻¹ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) v u : ℂˣ) : ℂ) = 1 := by
      intro v u
      simp [NumberField.TateGlobal.localChar]
    simp only [hloc, one_mul] at hRid
    have hRan : ∀ x : ℂ, 0 < x.re → AnalyticAt ℂ R x := fun x hx => hRdiff.analyticAt (hO0.mem_nhds hx)
    have hM1 : ∀ s : ℂ, 1 / 2 < s.re →
        weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) g =
          (NumberField.dedekindZeta F (2 * s) * FS T (2 * s)) *
            ((NumberField.dedekindZeta F (2 * s + 1) * FS T (2 * s + 1))⁻¹ * R s) := by
      intro s hs
      have h2s : 1 < (2 * s).re := by simp; linarith
      have h2s1 : 1 < (2 * s + 1).re := by simp; linarith
      obtain ⟨hA, hP2s⟩ := hpartial T (2 * s) h2s
      obtain ⟨hB, hP2s1⟩ := hpartial T (2 * s + 1) h2s1
      have hid := hRid s hs
      rw [hP2s, hP2s1] at hid
      rw [← hid, ← mul_assoc, mul_inv_cancel₀ hA, one_mul]
    let J : ℂ → ℂ := fun s => Rζ (2 * s) / 2 * FS T (2 * s) / (ζc (2 * s + 1) * FS T (2 * s + 1)) * R s
    have hJeq : ∀ s : ℂ, 1 / 2 < s.re →
        J s = (s - 1 / 2) * weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) g := by
      intro s hs
      have h2s : 1 < (2 * s).re := by simp; linarith
      have h2s1 : 1 < (2 * s + 1).re := by simp; linarith
      have hz : NumberField.dedekindZeta F (2 * s) ≠ 0 := NumberField.dedekindZeta_ne_zero_of_one_lt_re F h2s
      have hz1 : NumberField.dedekindZeta F (2 * s + 1) ≠ 0 :=
        NumberField.dedekindZeta_ne_zero_of_one_lt_re F h2s1
      have hf1 : FS T (2 * s + 1) ≠ 0 := hFSne T _ (by linarith)
      have hf2 : FS T (2 * s) ≠ 0 := hFSne T _ (by linarith)
      have hR2s : Rζ (2 * s) = (2 * s - 1) * NumberField.dedekindZeta F (2 * s) := hRζeq _ h2s
      rw [hM1 s hs]
      simp only [J, hζc_eq _ h2s1, hR2s]
      field_simp
    have hx : (0 : ℝ) < (1 / 2 : ℂ).re := by norm_num
    have hre2 : 1 < (2 * (1 / 2 : ℂ) + 1).re := by norm_num
    have h2ne : (2 * (1 / 2 : ℂ) + 1) ≠ 1 := by norm_num
    have hJan : AnalyticAt ℂ J (1 / 2) := by
      have hRζ2 : AnalyticAt ℂ (fun s : ℂ => Rζ (2 * s)) (1 / 2) := (hRζan _).comp_of_eq (h2an _) rfl
      have hFS2 : AnalyticAt ℂ (fun s : ℂ => FS T (2 * s)) (1 / 2) := (hFSan T _).comp_of_eq (h2an _) rfl
      have hFS21 : AnalyticAt ℂ (fun s : ℂ => FS T (2 * s + 1)) (1 / 2) := (hFSan T _).comp_of_eq (h21an _) rfl
      have hζ21 : AnalyticAt ℂ (fun s : ℂ => ζc (2 * s + 1)) (1 / 2) := (hζcan _ h2ne).comp_of_eq (h21an _) rfl
      exact (((hRζ2.div analyticAt_const two_ne_zero).mul hFS2).div (hζ21.mul hFS21)
        (mul_ne_zero (hζcne _ hre2) (hFSne T _ (by norm_num)))).mul (hRan _ hx)
    exact ⟨J, hJan, hJeq⟩
  obtain ⟨JW, hJWan, hJWeq⟩ := hJg k
  obtain ⟨J1, hJ1an, hJ1eq⟩ := hJg 1

  have hDeq : ∀ s : ℂ, 1 / 2 < s.re →
      (s - 1 / 2) * (weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) k
          - weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) 1) = JW s - J1 s := by
    intro s hs; rw [hJWeq s hs, hJ1eq s hs]; ring
  have hDan : AnalyticAt ℂ (fun s => JW s - J1 s) (1 / 2) := hJWan.sub hJ1an
  have hDlim : Tendsto (fun s : ℂ => (s - 1 / 2) *
      (weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) k
        - weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) 1))
      (𝓝[U] (1 / 2 : ℂ)) (𝓝 (JW (1 / 2) - J1 (1 / 2))) :=
    (hDan.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
      (eventually_nhdsWithin_of_forall (fun s hs => (hDeq s hs).symm))

  suffices hray : Tendsto (fun σ : ℝ => ((σ : ℂ) - 1 / 2) *
      (weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ σ) k
        - weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ σ) 1))
      (𝓝[>] (1 / 2 : ℝ)) (𝓝 0) by
    have hmap : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] (1 / 2 : ℝ)) (𝓝[U] (1 / 2 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by push_cast; ring
        rw [← this]
        exact (Complex.continuous_ofReal.tendsto _).mono_left nhdsWithin_le_nhds
      · refine eventually_nhdsWithin_of_forall (fun σ hσ => ?_)
        show 1 / 2 < (σ : ℂ).re
        simpa using hσ
    have h1 := hDlim.comp hmap
    have h0 : JW (1 / 2) - J1 (1 / 2) = 0 := tendsto_nhds_unique h1 hray
    rw [h0] at hDlim
    exact hDlim

  by_cases hz : ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F), φ s g = 0
  · refine (tendsto_const_nhds (x := (0 : ℂ))).congr' (Eventually.of_forall fun σ => ?_)
    simp only [weylIntertwiningIntegral, hz, integral_zero, sub_self, mul_zero]
  push Not at hz
  obtain ⟨s₀, g₀, hne⟩ := hz
  have hφc : ∀ s, Continuous (φ s) := fun s => hφjc.comp (continuous_const.prodMk continuous_id)

  obtain ⟨S, n, c, kdat, abm, m, A, B, Rr, Rc, habm, hm, hA, hB, -, -, hRr, hRc, hbig⟩ :=
    AutomorphicForm.bigCell_eq_sum_pureTensor_of_flat_family F hα 1 1 φ hφ hφK hφf hφc hφflat ⟨s₀, g₀, hne⟩

  have h11 : (1 * 1⁻¹ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) = 1 := by
    ext t
    simp
  set χ₀ : ∀ u : HeightOneSpectrum (𝓞 F), (u.adicCompletion F)ˣ →* ℂˣ :=
    NumberField.TateGlobal.localChar (1 * 1⁻¹ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) with hχ₀
  have hχ₀U : ∀ (u : HeightOneSpectrum (𝓞 F)) (t : (u.adicCompletion F)ˣ), χ₀ u t = 1 := by
    intro u t
    rw [hχ₀, h11, NumberField.TateGlobal.localChar_apply, MonoidHom.one_apply]
  have hχext : ∀ (u : HeightOneSpectrum (𝓞 F)) (y : u.adicCompletion F), y ≠ 0 →
      LanglandsTunnell.TateLocal.charExt (χ₀ u)⁻¹ y = 1 := by
    intro u y hy
    rw [LanglandsTunnell.TateLocal.charExt_of_ne_zero _ hy, MonoidHom.inv_apply, hχ₀U, inv_one, Units.val_one]
  have hRr1 : ∀ (i : {w : InfinitePlace F // w.IsReal}) (t : ℝ), 0 < t → Rr i t = 1 := by
    intro i t ht
    obtain ⟨y, hy⟩ := NumberField.InfinitePlace.Completion.surjective_extensionEmbeddingOfIsReal i.2 t
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [map_zero] at hy
      exact ht.ne' hy.symm
    have h := hRr i (Units.mk0 y hy0) (by rw [Units.val_mk0, hy]; exact ht)
    rw [Units.val_mk0, hy] at h
    rw [h, h11, MonoidHom.one_apply, Units.val_one]
  have hRc1 : ∀ (w : {w : InfinitePlace F // w.IsComplex}) (t : ℝ), 0 < t → Rc w t = 1 := by
    intro w t ht
    obtain ⟨y, hy⟩ := NumberField.InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex w.2 (t : ℂ)
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [map_zero] at hy
      exact (Complex.ofReal_ne_zero.mpr ht.ne') hy.symm
    rw [hRc w (Units.mk0 y hy0) t ht (by rw [Units.val_mk0, hy]), h11, MonoidHom.one_apply, Units.val_one]

  classical
  set T : Finset (HeightOneSpectrum (𝓞 F)) := S with hT
  have hST : S ⊆ T := subset_rfl
  set A' : Fin n → ∀ u : HeightOneSpectrum (𝓞 F), u.adicCompletion F → ℂ :=
    fun j u => if u ∈ S then A j u else fun _ => 1 with hA'
  set B' : Fin n → ∀ u : HeightOneSpectrum (𝓞 F), u.adicCompletion F → ℂ :=
    fun j u => if u ∈ S then B j u else fun _ => 1 with hB'
  have hA'S : ∀ j, ∀ u ∈ S, A' j u = A j u := fun j u hu => by simp only [hA', if_pos hu]
  have hB'S : ∀ j, ∀ u ∈ S, B' j u = B j u := fun j u hu => by simp only [hB', if_pos hu]
  have hA'c : ∀ j, ∀ u ∉ S, A' j u = fun _ => 1 := fun j u hu => by simp only [hA', if_neg hu]
  have hB'c : ∀ j, ∀ u ∉ S, B' j u = fun _ => 1 := fun j u hu => by simp only [hB', if_neg hu]
  have hA'lc : ∀ (j : Fin n) (u : HeightOneSpectrum (𝓞 F)), ∀ x ∈ u.adicCompletionIntegers F,
      ∀ y ∈ u.adicCompletionIntegers F,
        Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → A' j u y = A' j u x := by
    intro j u x hx y hy hxy
    by_cases hu : u ∈ S
    · rw [hA'S j u hu]; exact hA j u hu x hx y hy hxy
    · rw [hA'c j u hu]
  have hB'lc : ∀ (j : Fin n) (u : HeightOneSpectrum (𝓞 F)) (x y : u.adicCompletion F),
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B' j u y = B' j u x := by
    intro j u x y hxy
    by_cases hu : u ∈ S
    · rw [hB'S j u hu]; exact hB j u hu x y hxy
    · rw [hB'c j u hu]

  letI mK : ∀ u : HeightOneSpectrum (𝓞 F), MeasurableSpace (u.adicCompletion F) := fun u => borel _
  haveI : ∀ u : HeightOneSpectrum (𝓞 F), BorelSpace (u.adicCompletion F) := fun u => ⟨rfl⟩
  set μv : ∀ u : HeightOneSpectrum (𝓞 F), Measure (u.adicCompletion F) := fun u => Measure.addHaar with hμv
  haveI hμvH : ∀ u, (μv u).IsAddHaarMeasure := fun u => by rw [hμv]; infer_instance
  letI mf : MeasurableSpace (FiniteAdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  set νf : Measure (FiniteAdeleRing (𝓞 F) F) := Measure.addHaar with hνf
  haveI hμAH : (adelicAddHaar (𝓞 F) F).IsAddHaarMeasure :=
    NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar (𝓞 F) F
  obtain ⟨ϖ, hϖ⟩ : ∃ ϖ : ∀ u : HeightOneSpectrum (𝓞 F), (u.adicCompletion F)ˣ,
      ∀ u, Valued.v (ϖ u : u.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ) := by
    have key : ∀ u : HeightOneSpectrum (𝓞 F),
        ∃ t : (u.adicCompletion F)ˣ, Valued.v (t : u.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ) := by
      intro u
      obtain ⟨r, hr⟩ := u.valuation_exists_uniformizer' F
      obtain ⟨x, hx⟩ : ∃ x : u.adicCompletion F, Valued.v x = WithZero.exp (-1 : ℤ) :=
        ⟨_, (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation u r).trans hr⟩
      have hne : x ≠ 0 := by
        intro h0
        rw [h0, map_zero] at hx
        exact WithZero.exp_ne_zero hx.symm
      exact ⟨Units.mk0 x hne, hx⟩
    choose ϖ hϖ using key
    exact ⟨ϖ, hϖ⟩

  set K : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F) :=
    ((glArch (𝓞 F) F k : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) with hKdef
  set kw : Matrix (Fin 2) (Fin 2) w.Completion :=
    ((archComponent F w (glArch (𝓞 F) F k) : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) with hkwdef
  have hkwK : ∀ i j : Fin 2, kw i j = K i j w := fun i j => rfl
  set aR : {w : InfinitePlace F // w.IsReal} → ℝ := fun i => Completion.extensionEmbeddingOfIsReal i.2 (K 0 0 i.1) with haR
  set bR : {w : InfinitePlace F // w.IsReal} → ℝ := fun i => Completion.extensionEmbeddingOfIsReal i.2 (K 0 1 i.1) with hbR
  set cR : {w : InfinitePlace F // w.IsReal} → ℝ := fun i => Completion.extensionEmbeddingOfIsReal i.2 (K 1 0 i.1) with hcR
  set dR : {w : InfinitePlace F // w.IsReal} → ℝ := fun i => Completion.extensionEmbeddingOfIsReal i.2 (K 1 1 i.1) with hdR
  set aC : {w : InfinitePlace F // w.IsComplex} → ℂ := fun v => Completion.extensionEmbedding v.1 (K 0 0 v.1) with haC
  set bC : {w : InfinitePlace F // w.IsComplex} → ℂ := fun v => Completion.extensionEmbedding v.1 (K 0 1 v.1) with hbC
  set cC : {w : InfinitePlace F // w.IsComplex} → ℂ := fun v => Completion.extensionEmbedding v.1 (K 1 0 v.1) with hcC
  set dC : {w : InfinitePlace F // w.IsComplex} → ℂ := fun v => Completion.extensionEmbedding v.1 (K 1 1 v.1) with hdC
  have hdetR : ∀ i : {w : InfinitePlace F // w.IsReal}, aR i * dR i - bR i * cR i ≠ 0 := by
    intro i
    have h' := (map_ne_zero (Completion.extensionEmbeddingOfIsReal i.2)).2
      (Matrix.GeneralLinearGroup.det_ne_zero (archComponent F i.1 (glArch (𝓞 F) F k)))
    rw [Matrix.det_fin_two, map_sub, map_mul, map_mul] at h'
    exact h'
  have hdetC : ∀ v : {w : InfinitePlace F // w.IsComplex}, aC v * dC v - bC v * cC v ≠ 0 := by
    intro v
    have h' := (map_ne_zero (Completion.extensionEmbedding v.1)).2
      (Matrix.GeneralLinearGroup.det_ne_zero (archComponent F v.1 (glArch (𝓞 F) F k)))
    rw [Matrix.det_fin_two, map_sub, map_mul, map_mul] at h'
    exact h'

  set fr : Fin n → ℝ → {w : InfinitePlace F // w.IsReal} → ℝ → ℂ :=
    fun j σ i => A5Kit.rAtom (kdat j i) σ with hfr
  set fc : Fin n → ℝ → {w : InfinitePlace F // w.IsComplex} → ℂ → ℂ :=
    fun j σ v => A5Kit.cAtom (abm j v).1 (abm j v).2.1 (abm j v).2.2 σ with hfc
  set fr' : Fin n → ℝ → {w : InfinitePlace F // w.IsReal} → ℝ → ℂ :=
    fun j σ i => if i.1 = w then
      (fun u => A5Kit.rJ (aR i) (bR i) (cR i) (dR i) σ u
        * A5Kit.rAtom (kdat j i) σ ((bR i + u * dR i) / (aR i + u * cR i)))
      else A5Kit.rAtom (kdat j i) σ with hfr'
  set fc' : Fin n → ℝ → {w : InfinitePlace F // w.IsComplex} → ℂ → ℂ :=
    fun j σ v => if v.1 = w then
      (fun z => A5Kit.cJ (aC v) (bC v) (cC v) (dC v) σ z
        * A5Kit.cAtom (abm j v).1 (abm j v).2.1 (abm j v).2.2 σ ((bC v + z * dC v) / (aC v + z * cC v)))
      else A5Kit.cAtom (abm j v).1 (abm j v).2.1 (abm j v).2.2 σ with hfc'
  have hfr'w : ∀ j σ (i : {w : InfinitePlace F // w.IsReal}), i.1 = w → fr' j σ i =
      fun u => A5Kit.rJ (aR i) (bR i) (cR i) (dR i) σ u
        * A5Kit.rAtom (kdat j i) σ ((bR i + u * dR i) / (aR i + u * cR i)) := by
    intro j σ i hi; simp only [hfr', if_pos hi]
  have hfr'ne : ∀ j σ (i : {w : InfinitePlace F // w.IsReal}), i.1 ≠ w → fr' j σ i = fr j σ i := by
    intro j σ i hi; simp only [hfr', hfr, if_neg hi]
  have hfc'w : ∀ j σ (v : {w : InfinitePlace F // w.IsComplex}), v.1 = w → fc' j σ v =
      fun z => A5Kit.cJ (aC v) (bC v) (cC v) (dC v) σ z
        * A5Kit.cAtom (abm j v).1 (abm j v).2.1 (abm j v).2.2 σ ((bC v + z * dC v) / (aC v + z * cC v)) := by
    intro j σ v hv; simp only [hfc', if_pos hv]
  have hfc'ne : ∀ j σ (v : {w : InfinitePlace F // w.IsComplex}), v.1 ≠ w → fc' j σ v = fc j σ v := by
    intro j σ v hv; simp only [hfc', hfc, if_neg hv]
  set fA : Fin n → ℝ → mixedEmbedding.mixedSpace F → ℂ := fun j σ => A5Kit.archProd (fr j σ) (fc j σ) with hfA
  set fA' : Fin n → ℝ → mixedEmbedding.mixedSpace F → ℂ := fun j σ => A5Kit.archProd (fr' j σ) (fc' j σ) with hfA'
  set hfun : Fin n → ℝ → ∀ u : HeightOneSpectrum (𝓞 F), u.adicCompletion F → ℂ :=
    fun j σ u => A5Kit.atom u (A' j u) (B' j u) (σ : ℂ) with hhfun

  have hexp1 : ∀ (σ : ℝ) (x : AdeleRing (𝓞 F) F),
      φ σ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x)
        = ∑ j : Fin n, c j * A5Kit.tensor T χ₀ (fA j σ) (hfun j σ) (σ : ℂ) x := by
    intro σ x
    rw [hbig]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_assoc (c j), A5Kit.arch_eq_archProd (kdat j) (abm j) Rr Rc hRr1 hRc1, mul_assoc,
      A5Kit.reindex S T hST χ₀ hχext (A j) (B j) (A' j) (B' j) (hA'S j) (hB'S j) (hA'c j) (hB'c j),
      mul_assoc]
    rfl

  have hnormR : ∀ (i : {w : InfinitePlace F // w.IsReal}) (y : i.1.Completion),
      ‖y‖ = |Completion.extensionEmbeddingOfIsReal i.2 y| := fun i y => by
    rw [← Real.norm_eq_abs, (Completion.isometry_extensionEmbeddingOfIsReal i.2).norm_map_of_map_zero (map_zero _)]
  have hnormC : ∀ (v : {w : InfinitePlace F // w.IsComplex}) (y : v.1.Completion),
      ‖y‖ = ‖Completion.extensionEmbedding v.1 y‖ := fun v y => by
    rw [(Completion.isometry_extensionEmbedding v.1).norm_map_of_map_zero (map_zero _)]
  have hexpK : ∀ (σ : ℝ) (x : AdeleRing (𝓞 F) F), kw 0 0 + x.1 w * kw 1 0 ≠ 0 →
      φ σ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * k)
        = ∑ j : Fin n, c j * A5Kit.tensor T χ₀ (fA' j σ) (hfun j σ) (σ : ℂ) x := by
    intro σ x hx
    set t : w.Completion := (kw 0 1 + x.1 w * kw 1 1) / (kw 0 0 + x.1 w * kw 1 0) with ht
    set M : ℂ := (((‖kw.det‖ ^ w.mult : ℝ)) : ℂ) ^ ((σ : ℂ) + 1 / 2)
        * (((‖kw 0 0 + x.1 w * kw 1 0‖ ^ w.mult : ℝ)) : ℂ) ^ (-(2 * (σ : ℂ) + 1)) with hM
    have hA1 : φ σ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * k)
        = M * φ σ ((adelicWeyl (𝓞 F) F)⁻¹
            * unipotentGL2 (R := AdeleRing (𝓞 F) F) (Function.update x.1 w t, x.2)) := by
      have h := AutomorphicForm.apply_weylInv_unipotent_mul_archSupportedAt_eq_norm_cpow_mul_apply F hα (σ : ℂ)
        (φ σ) (hφ σ) w k hkf hka x hx
      rw [hM]
      exact h
    rw [hA1, hexp1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_left_comm]
    congr 1
    simp only [A5Kit.tensor]
    rw [← mul_assoc]
    congr 1
    refine A5Kit.transport_arch (fr j σ) (fr' j σ) (fc j σ) (fc' j σ) w x.1 t M ?_ (hfr'ne j σ) ?_ (hfc'ne j σ)
    · rintro ⟨i, hi2⟩ hi
      change i = w at hi
      subst hi
      rw [hfr'w j σ ⟨i, hi2⟩ rfl]
      simp only [hfr]
      rw [Function.update_self]
      have hm : i.mult = 1 := mult_isReal ⟨i, hi2⟩
      have ht' : Completion.extensionEmbeddingOfIsReal hi2 t
          = (bR ⟨i, hi2⟩ + Completion.extensionEmbeddingOfIsReal hi2 (x.1 i) * dR ⟨i, hi2⟩)
            / (aR ⟨i, hi2⟩ + Completion.extensionEmbeddingOfIsReal hi2 (x.1 i) * cR ⟨i, hi2⟩) := by
        rw [ht, map_div₀, map_add, map_add, map_mul, map_mul]
        rfl
      have hM' : M = A5Kit.rJ (aR ⟨i, hi2⟩) (bR ⟨i, hi2⟩) (cR ⟨i, hi2⟩) (dR ⟨i, hi2⟩) σ
          (Completion.extensionEmbeddingOfIsReal hi2 (x.1 i)) := by
        rw [hM, hm, pow_one, pow_one, hnormR ⟨i, hi2⟩, hnormR ⟨i, hi2⟩, Matrix.det_fin_two,
          map_sub, map_mul, map_mul, map_add, map_mul]
        rfl
      rw [ht', hM']
    · rintro ⟨v, hv2⟩ hv
      change v = w at hv
      subst hv
      rw [hfc'w j σ ⟨v, hv2⟩ rfl]
      simp only [hfc]
      rw [Function.update_self]
      have hm : v.mult = 2 := mult_isComplex ⟨v, hv2⟩
      have ht' : Completion.extensionEmbedding v t
          = (bC ⟨v, hv2⟩ + Completion.extensionEmbedding v (x.1 v) * dC ⟨v, hv2⟩)
            / (aC ⟨v, hv2⟩ + Completion.extensionEmbedding v (x.1 v) * cC ⟨v, hv2⟩) := by
        rw [ht, map_div₀, map_add, map_add, map_mul, map_mul]
        rfl
      have hM' : M = A5Kit.cJ (aC ⟨v, hv2⟩) (bC ⟨v, hv2⟩) (cC ⟨v, hv2⟩) (dC ⟨v, hv2⟩) σ
          (Completion.extensionEmbedding v (x.1 v)) := by
        rw [hM, hm, hnormC ⟨v, hv2⟩, hnormC ⟨v, hv2⟩, Matrix.det_fin_two,
          map_sub, map_mul, map_mul, map_add, map_mul]
        rfl
      rw [ht', hM']

  have hnull : adelicAddHaar (𝓞 F) F {x : AdeleRing (𝓞 F) F | kw 0 0 + x.1 w * kw 1 0 = 0} = 0 := by
    by_cases hc0 : kw 1 0 = 0
    · have h00 : kw 0 0 ≠ 0 := by
        intro h0
        apply Matrix.GeneralLinearGroup.det_ne_zero (archComponent F w (glArch (𝓞 F) F k))
        rw [Matrix.det_fin_two]
        change kw 0 0 * kw 1 1 - kw 0 1 * kw 1 0 = 0
        rw [h0, hc0]; ring
      have he : {x : AdeleRing (𝓞 F) F | kw 0 0 + x.1 w * kw 1 0 = 0} = ∅ :=
        Set.eq_empty_of_forall_notMem fun x hx => h00 (by simpa [hc0] using hx)
      rw [he, measure_empty]
    · refine measure_mono_null (fun x hx => ?_)
        (NumberField.AdelicHaar.adelicAddHaar_setOf_fst_apply_eq_eq_zero F w (-(kw 0 0) / kw 1 0))
      simp only [Set.mem_setOf_eq] at hx ⊢
      field_simp
      linear_combination hx

  have hM1 : ∀ σ : ℝ, weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ σ) 1
      = ∫ x, ∑ j : Fin n, c j * A5Kit.tensor T χ₀ (fA j σ) (hfun j σ) (σ : ℂ) x ∂(adelicAddHaar (𝓞 F) F) := by
    intro σ
    simp only [weylIntertwiningIntegral, mul_one]
    exact integral_congr_ae (Eventually.of_forall fun x => hexp1 σ x)
  have hMK : ∀ σ : ℝ, weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ σ) k
      = ∫ x, ∑ j : Fin n, c j * A5Kit.tensor T χ₀ (fA' j σ) (hfun j σ) (σ : ℂ) x ∂(adelicAddHaar (𝓞 F) F) := by
    intro σ
    simp only [weylIntertwiningIntegral]
    refine integral_congr_ae ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with x hx
    exact hexpK σ x hx

  have hintfin : ∀ (j : Fin n) (σ : ℝ), 1 / 2 < σ → ∀ u ∈ T, Integrable (hfun j σ u) (μv u) := by
    intro j σ hσ u _
    have hσ0 : 0 < ((σ : ℂ)).re := by simp; linarith
    exact (AutomorphicForm.LocalIntertwining.integrable_smoothAtom_and_integrable_weylShift_adicCompletion F u
      (μv u) m hm (A' j u) (B' j u) (hA'lc j u) (hB'lc j u) (σ : ℂ) hσ0).1
  have hintfA : ∀ (j : Fin n) (σ : ℝ), 1 / 2 < σ → Integrable (fA j σ) := by
    intro j σ hσ
    have hσ0 : 0 < σ := by linarith
    refine A5Kit.integrable_archProd _ _ (fun i => ?_) (fun v => ?_)
    · exact (AutomorphicForm.LocalIntertwining.integrable_realAtom_and_integrable_moebiusShift
        (aR i) (bR i) (cR i) (dR i) (hdetR i) (kdat j i) σ hσ0).1
    · exact (AutomorphicForm.LocalIntertwining.integrable_complexAtom_and_integrable_moebiusShift
        (aC v) (bC v) (cC v) (dC v) (hdetC v) (abm j v).1 (abm j v).2.1 (abm j v).2.2 (habm j v) σ hσ0).1
  have hintfA' : ∀ (j : Fin n) (σ : ℝ), 1 / 2 < σ → Integrable (fA' j σ) := by
    intro j σ hσ
    have hσ0 : 0 < σ := by linarith
    refine A5Kit.integrable_archProd _ _ (fun i => ?_) (fun v => ?_)
    · by_cases hi : i.1 = w
      · rw [hfr'w j σ i hi]
        exact (AutomorphicForm.LocalIntertwining.integrable_realAtom_and_integrable_moebiusShift
          (aR i) (bR i) (cR i) (dR i) (hdetR i) (kdat j i) σ hσ0).2
      · rw [hfr'ne j σ i hi]
        exact (AutomorphicForm.LocalIntertwining.integrable_realAtom_and_integrable_moebiusShift
          (aR i) (bR i) (cR i) (dR i) (hdetR i) (kdat j i) σ hσ0).1
    · by_cases hv : v.1 = w
      · rw [hfc'w j σ v hv]
        exact (AutomorphicForm.LocalIntertwining.integrable_complexAtom_and_integrable_moebiusShift
          (aC v) (bC v) (cC v) (dC v) (hdetC v) (abm j v).1 (abm j v).2.1 (abm j v).2.2 (habm j v) σ hσ0).2
      · rw [hfc'ne j σ v hv]
        exact (AutomorphicForm.LocalIntertwining.integrable_complexAtom_and_integrable_moebiusShift
          (aC v) (bC v) (cC v) (dC v) (hdetC v) (abm j v).1 (abm j v).2.1 (abm j v).2.2 (habm j v) σ hσ0).1
  have hint1 : ∀ (j : Fin n) (σ : ℝ), 1 / 2 < σ →
      Integrable (A5Kit.tensor T χ₀ (fA j σ) (hfun j σ) (σ : ℂ)) (adelicAddHaar (𝓞 F) F) := by
    intro j σ hσ
    exact A5Kit.integrable_tensor νf μv ϖ hϖ T χ₀ hχext (hfun j σ) (fA j σ) (hintfA j σ hσ) (σ : ℂ)
      (by simpa using hσ) (hintfin j σ hσ)
  have hintK : ∀ (j : Fin n) (σ : ℝ), 1 / 2 < σ →
      Integrable (A5Kit.tensor T χ₀ (fA' j σ) (hfun j σ) (σ : ℂ)) (adelicAddHaar (𝓞 F) F) := by
    intro j σ hσ
    exact A5Kit.integrable_tensor νf μv ϖ hϖ T χ₀ hχext (hfun j σ) (fA' j σ) (hintfA' j σ hσ) (σ : ℂ)
      (by simpa using hσ) (hintfin j σ hσ)
  have hM1' : ∀ σ : ℝ, 1 / 2 < σ → weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ σ) 1
      = ∑ j : Fin n, c j * ∫ x, A5Kit.tensor T χ₀ (fA j σ) (hfun j σ) (σ : ℂ) x ∂(adelicAddHaar (𝓞 F) F) := by
    intro σ hσ
    rw [hM1 σ, integral_finsetSum _ (fun j _ => (hint1 j σ hσ).const_mul (c j))]
    exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
  have hMK' : ∀ σ : ℝ, 1 / 2 < σ → weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ σ) k
      = ∑ j : Fin n, c j * ∫ x, A5Kit.tensor T χ₀ (fA' j σ) (hfun j σ) (σ : ℂ) x ∂(adelicAddHaar (𝓞 F) F) := by
    intro σ hσ
    rw [hMK σ, integral_finsetSum _ (fun j _ => (hintK j σ hσ).const_mul (c j))]
    exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _

  set cbox : ℂ := ((adelicAddHaar (𝓞 F) F (NumberField.AdelicBox.adelicBox F)).toReal : ℂ) with hcbox
  set cF : ℂ := (((2 : ℝ) ^ NumberField.InfinitePlace.nrComplexPlaces F / Real.sqrt |(discr F : ℝ)| : ℝ) : ℂ)
    with hcF
  have hcbox0 : cbox ≠ 0 := by
    rw [hcbox]
    exact Complex.ofReal_ne_zero.2 (ENNReal.toReal_pos (NumberField.AdelicBox.adelicAddHaar_adelicBox_pos F).ne'
      (NumberField.AdelicBox.adelicAddHaar_adelicBox_lt_top F).ne).ne'

  set I : Fin n → ℝ → HeightOneSpectrum (𝓞 F) → ℂ := fun j σ u =>
    (((μv u).real (u.adicCompletionIntegers F : Set (u.adicCompletion F)) : ℂ)⁻¹
      * ∫ y, hfun j σ u y ∂(μv u)) with hI
  set Af : Fin n → ℝ → ℂ := fun j σ => ∫ y, fA j σ y with hAf
  set Af' : Fin n → ℝ → ℂ := fun j σ => ∫ y, fA' j σ y with hAf'

  set Z0 : ℝ → ℂ := fun σ => NumberField.dedekindZeta F (2 * (σ : ℂ)) * FS T (2 * (σ : ℂ)) with hZ0
  set Z1 : ℝ → ℂ := fun σ => NumberField.dedekindZeta F (2 * (σ : ℂ) + 1) * FS T (2 * (σ : ℂ) + 1) with hZ1
  have hZ0ne : ∀ σ : ℝ, 1 / 2 < σ → Z0 σ ≠ 0 := fun σ hσ => (hpartial T (2 * (σ : ℂ)) (by simp; linarith)).1
  have hZ1ne : ∀ σ : ℝ, 1 / 2 < σ → Z1 σ ≠ 0 := fun σ hσ => (hpartial T (2 * (σ : ℂ) + 1) (by simp; linarith)).1
  have hGK : ∀ (σ : ℝ), 1 / 2 < σ →
      ∀ (f : mixedEmbedding.mixedSpace F → ℂ) (h : ∀ u : HeightOneSpectrum (𝓞 F), u.adicCompletion F → ℂ),
        cbox⁻¹ * (∫ x, A5Kit.tensor T χ₀ f h (σ : ℂ) x ∂(adelicAddHaar (𝓞 F) F)) * (Z0 σ)⁻¹
          = cF * (∫ y, f y)
            * ((∏ u ∈ T, (((μv u).real (u.adicCompletionIntegers F : Set (u.adicCompletion F)) : ℂ)⁻¹
                * ∫ y, h u y ∂(μv u))) * (Z1 σ)⁻¹) := by
    intro σ hσ f h
    have hσ' : 1 / 2 < ((σ : ℂ)).re := by simpa using hσ
    have h0 := AutomorphicForm.LocalIntertwining.integral_adeleRing_pureTensor_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod
      F (adelicAddHaar (𝓞 F) F) T μv f h ϖ (fun u _ => hϖ u) χ₀ (fun u _ t _ => hχ₀U u t)
      (fun u _ => by rw [hχ₀U, Units.val_one, norm_one]) (σ : ℂ) hσ'
    simp only [hχ₀U, Units.val_one, one_mul] at h0
    rw [(hpartial T (2 * (σ : ℂ)) (by simp; linarith)).2,
      (hpartial T (2 * (σ : ℂ) + 1) (by simp; linarith)).2] at h0
    exact h0
  have hval : ∀ (σ : ℝ), 1 / 2 < σ →
      ∀ (f : mixedEmbedding.mixedSpace F → ℂ) (h : ∀ u : HeightOneSpectrum (𝓞 F), u.adicCompletion F → ℂ),
        ∫ x, A5Kit.tensor T χ₀ f h (σ : ℂ) x ∂(adelicAddHaar (𝓞 F) F)
          = cbox * Z0 σ * (Z1 σ)⁻¹ * cF * (∫ y, f y)
            * ∏ u ∈ T, (((μv u).real (u.adicCompletionIntegers F : Set (u.adicCompletion F)) : ℂ)⁻¹
                * ∫ y, h u y ∂(μv u)) := by
    intro σ hσ f h
    have h0 := hGK σ hσ f h
    have hz0 := hZ0ne σ hσ
    calc _ = cbox * Z0 σ * (cbox⁻¹ * (∫ x, A5Kit.tensor T χ₀ f h (σ : ℂ) x ∂(adelicAddHaar (𝓞 F) F))
              * (Z0 σ)⁻¹) := by field_simp
      _ = _ := by rw [h0]; ring

  set E : ℝ → ℂ := fun σ => ((σ : ℂ) - 1 / 2) * Z0 σ * (Z1 σ)⁻¹ with hE
  let Ean : ℂ → ℂ := fun s => Rζ (2 * s) / 2 * FS T (2 * s) / (ζc (2 * s + 1) * FS T (2 * s + 1))
  have hre2 : 1 < (2 * (1 / 2 : ℂ) + 1).re := by norm_num
  have h2ne : (2 * (1 / 2 : ℂ) + 1) ≠ 1 := by norm_num
  have hEan : AnalyticAt ℂ Ean (1 / 2) := by
    have hRζ2 : AnalyticAt ℂ (fun s : ℂ => Rζ (2 * s)) (1 / 2) := (hRζan _).comp_of_eq (h2an _) rfl
    have hFS2 : AnalyticAt ℂ (fun s : ℂ => FS T (2 * s)) (1 / 2) := (hFSan T _).comp_of_eq (h2an _) rfl
    have hFS21 : AnalyticAt ℂ (fun s : ℂ => FS T (2 * s + 1)) (1 / 2) := (hFSan T _).comp_of_eq (h21an _) rfl
    have hζ21 : AnalyticAt ℂ (fun s : ℂ => ζc (2 * s + 1)) (1 / 2) := (hζcan _ h2ne).comp_of_eq (h21an _) rfl
    exact ((hRζ2.div analyticAt_const two_ne_zero).mul hFS2).div (hζ21.mul hFS21)
      (mul_ne_zero (hζcne _ hre2) (hFSne T _ (by norm_num)))
  have hEeq : ∀ σ : ℝ, 1 / 2 < σ → E σ = Ean (σ : ℂ) := by
    intro σ hσ
    have h2s : 1 < (2 * (σ : ℂ)).re := by simp; linarith
    have h2s1 : 1 < (2 * (σ : ℂ) + 1).re := by simp; linarith
    have hz : NumberField.dedekindZeta F (2 * (σ : ℂ)) ≠ 0 := NumberField.dedekindZeta_ne_zero_of_one_lt_re F h2s
    have hz1 : NumberField.dedekindZeta F (2 * (σ : ℂ) + 1) ≠ 0 :=
      NumberField.dedekindZeta_ne_zero_of_one_lt_re F h2s1
    have hf1 : FS T (2 * (σ : ℂ) + 1) ≠ 0 := hFSne T _ (by linarith)
    have hf2 : FS T (2 * (σ : ℂ)) ≠ 0 := hFSne T _ (by linarith)
    have hR2s : Rζ (2 * (σ : ℂ)) = (2 * (σ : ℂ) - 1) * NumberField.dedekindZeta F (2 * (σ : ℂ)) := hRζeq _ h2s
    simp only [hE, hZ0, hZ1, Ean, hζc_eq _ h2s1, hR2s]
    field_simp
  have hmap0 : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] (1 / 2 : ℝ)) (𝓝 (1 / 2 : ℂ)) := by
    have : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by push_cast; ring
    rw [← this]
    exact (Complex.continuous_ofReal.tendsto _).mono_left nhdsWithin_le_nhds
  have hElim : Tendsto E (𝓝[>] (1 / 2 : ℝ)) (𝓝 (Ean (1 / 2))) :=
    (hEan.continuousAt.tendsto.comp hmap0).congr'
      (eventually_nhdsWithin_of_forall fun σ hσ => (hEeq σ hσ).symm)

  have hIoo : Set.Ioo (1 / 2 : ℝ) 1 ∈ 𝓝[>] (1 / 2 : ℝ) := Ioo_mem_nhdsGT (by norm_num)
  have hIO : ∀ (j : Fin n), ∀ u ∈ T, (fun σ => I j σ u) =O[𝓝[>] (1 / 2 : ℝ)] (fun _ => (1 : ℝ)) := by
    intro j u hu
    obtain ⟨C, hC⟩ := (AutomorphicForm.LocalIntertwining.bounded_and_tendsto_integral_weylShift_sub_integral_smoothAtom_adicCompletion
      F u (μv u) m hm (A' j u) (B' j u) (hA'lc j u) (hB'lc j u)).1
    refine Asymptotics.IsBigO.of_bound
      (‖((μv u).real (u.adicCompletionIntegers F : Set (u.adicCompletion F)) : ℂ)⁻¹‖ * C) ?_
    filter_upwards [hIoo] with σ hσ
    rw [norm_one, mul_one, hI]
    dsimp only
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hC σ hσ.1 hσ.2.le) (norm_nonneg _)
  have hPIO : ∀ j : Fin n, (fun σ => ∏ u ∈ T, I j σ u) =O[𝓝[>] (1 / 2 : ℝ)] (fun _ => (1 : ℝ)) := by
    intro j
    have h := Asymptotics.IsBigO.finsetProd (fun u hu => hIO j u hu)
    exact h.congr_right fun _ => Finset.prod_const_one

  have hRO : ∀ (j : Fin n) (i : {w : InfinitePlace F // w.IsReal}),
      (fun σ => ∫ x, fr j σ i x) =O[𝓝[>] (1 / 2 : ℝ)] (fun _ => (1 : ℝ)) := by
    intro j i
    obtain ⟨C, hC⟩ := (AutomorphicForm.LocalIntertwining.bounded_and_tendsto_integral_moebiusShift_sub_integral_realAtom
      (aR i) (bR i) (cR i) (dR i) (hdetR i) (kdat j i)).1
    refine Asymptotics.IsBigO.of_bound C ?_
    filter_upwards [hIoo] with σ hσ
    rw [norm_one, mul_one]
    exact hC σ hσ.1 hσ.2.le
  have hRd : ∀ (j : Fin n) (i : {w : InfinitePlace F // w.IsReal}),
      Tendsto (fun σ => (∫ x, fr' j σ i x) - ∫ x, fr j σ i x) (𝓝[>] (1 / 2 : ℝ)) (𝓝 0) := by
    intro j i
    by_cases hi : i.1 = w
    · have h := (AutomorphicForm.LocalIntertwining.bounded_and_tendsto_integral_moebiusShift_sub_integral_realAtom
        (aR i) (bR i) (cR i) (dR i) (hdetR i) (kdat j i)).2
      refine h.congr fun σ => ?_
      simp only [hfr'w j σ i hi, hfr, A5Kit.rJ, A5Kit.rAtom]
    · refine (tendsto_const_nhds (x := (0 : ℂ))).congr fun σ => ?_
      rw [hfr'ne j σ i hi, sub_self]
  have hCO : ∀ (j : Fin n) (v : {w : InfinitePlace F // w.IsComplex}),
      (fun σ => ∫ z, fc j σ v z) =O[𝓝[>] (1 / 2 : ℝ)] (fun _ => (1 : ℝ)) := by
    intro j v
    obtain ⟨C, hC⟩ := (AutomorphicForm.LocalIntertwining.bounded_and_tendsto_integral_moebiusShift_sub_integral_complexAtom
      (aC v) (bC v) (cC v) (dC v) (hdetC v) (abm j v).1 (abm j v).2.1 (abm j v).2.2 (habm j v)).1
    refine Asymptotics.IsBigO.of_bound C ?_
    filter_upwards [hIoo] with σ hσ
    rw [norm_one, mul_one]
    exact hC σ hσ.1 hσ.2.le
  have hCd : ∀ (j : Fin n) (v : {w : InfinitePlace F // w.IsComplex}),
      Tendsto (fun σ => (∫ z, fc' j σ v z) - ∫ z, fc j σ v z) (𝓝[>] (1 / 2 : ℝ)) (𝓝 0) := by
    intro j v
    by_cases hv : v.1 = w
    · have h := (AutomorphicForm.LocalIntertwining.bounded_and_tendsto_integral_moebiusShift_sub_integral_complexAtom
        (aC v) (bC v) (cC v) (dC v) (hdetC v) (abm j v).1 (abm j v).2.1 (abm j v).2.2 (habm j v)).2
      refine h.congr fun σ => ?_
      simp only [hfc'w j σ v hv, hfc, A5Kit.cJ, A5Kit.cAtom]
    · refine (tendsto_const_nhds (x := (0 : ℂ))).congr fun σ => ?_
      rw [hfc'ne j σ v hv, sub_self]

  have hAfd : ∀ j : Fin n, Tendsto (fun σ => Af' j σ - Af j σ) (𝓝[>] (1 / 2 : ℝ)) (𝓝 0) := by
    intro j
    obtain ⟨hP'O, hPd⟩ := A5Kit.isBigO_and_tendsto_prod_sub_prod (Finset.univ : Finset {w : InfinitePlace F // w.IsReal})
      (fun i σ => ∫ x, fr j σ i x) (fun i σ => ∫ x, fr' j σ i x) (fun i _ => hRO j i) (fun i _ => hRd j i)
    obtain ⟨hQ'O, hQd⟩ := A5Kit.isBigO_and_tendsto_prod_sub_prod (Finset.univ : Finset {w : InfinitePlace F // w.IsComplex})
      (fun v σ => ∫ z, fc j σ v z) (fun v σ => ∫ z, fc' j σ v z) (fun v _ => hCO j v) (fun v _ => hCd j v)
    have hQO : (fun σ => ∏ v, ∫ z, fc j σ v z) =O[𝓝[>] (1 / 2 : ℝ)] (fun _ => (1 : ℝ)) :=
      (Asymptotics.IsBigO.finsetProd (fun v _ => hCO j v)).congr_right fun _ => Finset.prod_const_one
    have h1 := hP'O.mul_isLittleO ((isLittleO_one_iff ℝ).2 hQd)
    have h2 := ((isLittleO_one_iff ℝ).2 hPd).mul_isBigO hQO
    have h := (isLittleO_one_iff ℝ).1 ((h1.add h2).congr_right fun _ => by norm_num)
    refine h.congr fun σ => ?_
    simp only [hAf', hAf, hfA, hfA', A5Kit.integral_archProd]
    ring

  have hD : ∀ σ : ℝ, 1 / 2 < σ →
      ((σ : ℂ) - 1 / 2) * (weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ σ) k
        - weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ σ) 1)
      = E σ * (cbox * cF) * ∑ j : Fin n, c j * ((∏ u ∈ T, I j σ u) * (Af' j σ - Af j σ)) := by
    intro σ hσ
    rw [hMK' σ hσ, hM1' σ hσ, ← Finset.sum_sub_distrib, hE, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hval σ hσ (fA' j σ) (hfun j σ), hval σ hσ (fA j σ) (hfun j σ)]
    simp only [hI, hAf, hAf']
    ring
  refine (A5Kit.tendsto_zero_of_parts (Finset.univ : Finset (Fin n)) E (cbox * cF) c
    (fun j σ => ∏ u ∈ T, I j σ u) (fun j σ => Af' j σ - Af j σ)
    (hElim.isBigO_one ℝ) (fun j _ => hPIO j) (fun j _ => hAfd j)).congr' ?_
  exact eventually_nhdsWithin_of_forall fun σ hσ => (hD σ hσ).symm

end S_AutomorphicForm_tendsto_sub_one_half_mul_weylIntertwiningIntegral_sub_nhds_zero_of_flat_family_of_archSupportedAt
end P2MW
export P2MW.S_AutomorphicForm_tendsto_sub_one_half_mul_weylIntertwiningIntegral_sub_nhds_zero_of_flat_family_of_archSupportedAt (solution)
