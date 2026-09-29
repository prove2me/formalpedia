-- Prove2me | solution 1 for AutomorphicForm.tendsto_sub_one_half_mul_weylIntertwiningIntegral_localWeyl_sub_nhds_zero_of_flat_family
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/976008fc-43df-53e1-8b93-331e3e15f4b1

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
import Definitions.Def_AdelicDock_LocalEmbedding
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
import Theorems.Thm_AutomorphicForm_apply_weylInv_unipotent_mul_localWeyl_eq_modulus_cpow_mul_apply
import Theorems.Thm_AutomorphicForm_LocalIntertwining_bounded_and_tendsto_integral_weylShift_sub_integral_smoothAtom_adicCompletion
import Theorems.Thm_AutomorphicForm_LocalIntertwining_exists_bound_norm_integral_mixedSpace_archAtom_prod
import Theorems.Thm_AutomorphicForm_LocalIntertwining_integrable_smoothAtom_and_integrable_weylShift_adicCompletion
import Theorems.Thm_NumberField_AdelicHaar_adelicAddHaar_setOf_snd_apply_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_tendsto_sub_one_half_mul_weylIntertwiningIntegral_localWeyl_sub_nhds_zero_of_flat_family
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

namespace W6Kit

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

private theorem transport (T : Finset (HeightOneSpectrum (𝓞 F))) (v : HeightOneSpectrum (𝓞 F)) (hv : v ∈ T)
    (χ : ∀ u : HeightOneSpectrum (𝓞 F), (u.adicCompletion F)ˣ →* ℂˣ)
    (h h' m : ∀ u : HeightOneSpectrum (𝓞 F), u.adicCompletion F → ℂ) (s : ℂ)
    (hv' : h' v = fun y => m v y * h v y⁻¹) (hne : ∀ u, u ≠ v → h' u = h u)
    (x : FiniteAdeleRing (𝓞 F) F) :
    m v (x v) * finPart T χ h s (AdelicDock.splice (𝓞 F) F v x (x v)⁻¹) = finPart T χ h' s x := by
  classical
  unfold finPart
  have h1 : ∏ u ∈ T, h u (AdelicDock.splice (𝓞 F) F v x (x v)⁻¹ u)
      = h v (x v)⁻¹ * ∏ u ∈ T.erase v, h u (x u) := by
    rw [← Finset.mul_prod_erase T _ hv, AdelicDock.splice_apply_self]
    congr 1
    refine Finset.prod_congr rfl fun u hu => ?_
    rw [AdelicDock.splice_apply_of_ne _ _ _ _ _ (Finset.ne_of_mem_erase hu)]
  have h2 : ∏ u ∈ T, h' u (x u) = (m v (x v) * h v (x v)⁻¹) * ∏ u ∈ T.erase v, h u (x u) := by
    rw [← Finset.mul_prod_erase T _ hv, hv']
    congr 1
    refine Finset.prod_congr rfl fun u hu => ?_
    rw [hne u (Finset.ne_of_mem_erase hu)]
  rw [h1, h2]
  simp only [mul_assoc]
  congr 3
  exact finprod_congr fun u => by
    have hu : (u.1 : HeightOneSpectrum (𝓞 F)) ≠ v := fun huv => u.2 (by rw [huv]; exact hv)
    rw [AdelicDock.splice_apply_of_ne _ _ _ _ _ hu]

open scoped Classical in

private noncomputable def archF (kdat : {w : InfinitePlace F // w.IsReal} → ℤ)
    (abm : {w : InfinitePlace F // w.IsComplex} → ℕ × ℕ × ℕ) (s : ℂ)
    (y : mixedEmbedding.mixedSpace F) : ℂ :=
  (∏ i : {w : InfinitePlace F // w.IsReal},
      ((((y.1 i : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + (y.1 i) ^ 2) : ℝ) : ℂ)) ^ (kdat i)
        * (((1 + (y.1 i) ^ 2 : ℝ) : ℂ)) ^ (-(s + 1 / 2)))
  * (∏ w : {w : InfinitePlace F // w.IsComplex},
      (y.2 w) ^ (abm w).1 * (starRingEnd ℂ) (y.2 w) ^ (abm w).2.1
        * (((1 + ‖y.2 w‖ ^ 2 : ℝ) : ℂ)) ^ (-(2 * s + 1) - ((abm w).2.2 : ℂ) / 2))

open scoped Classical in

private theorem arch_eq_archF (kdat : {w : InfinitePlace F // w.IsReal} → ℤ)
    (abm : {w : InfinitePlace F // w.IsComplex} → ℕ × ℕ × ℕ)
    (Rr : {w : InfinitePlace F // w.IsReal} → ℝ → ℂ)
    (Rc : {w : InfinitePlace F // w.IsComplex} → ℝ → ℂ)
    (hRr : ∀ i (t : ℝ), 0 < t → Rr i t = 1) (hRc : ∀ w (t : ℝ), 0 < t → Rc w t = 1)
    (s : ℂ) (x : InfiniteAdeleRing F) :
    (∏ i : {w : InfinitePlace F // w.IsReal},
        Rr i ((1 + Completion.extensionEmbeddingOfIsReal i.2 (x i.1) ^ 2) ^ (-(1 / 2 : ℝ)))
          * ((((Completion.extensionEmbeddingOfIsReal i.2 (x i.1) : ℝ) : ℂ) - Complex.I)
              / ((Real.sqrt (1 + Completion.extensionEmbeddingOfIsReal i.2 (x i.1) ^ 2) : ℝ) : ℂ)) ^ (kdat i)
          * (((1 + Completion.extensionEmbeddingOfIsReal i.2 (x i.1) ^ 2 : ℝ) : ℂ)) ^ (-(s + 1 / 2)))
      * (∏ w : {w : InfinitePlace F // w.IsComplex},
          Rc w ((1 + ‖Completion.extensionEmbedding w.1 (x w.1)‖ ^ 2) ^ (-(1 / 2 : ℝ)))
            * Completion.extensionEmbedding w.1 (x w.1) ^ (abm w).1
            * (starRingEnd ℂ) (Completion.extensionEmbedding w.1 (x w.1)) ^ (abm w).2.1
            * (((1 + ‖Completion.extensionEmbedding w.1 (x w.1)‖ ^ 2 : ℝ) : ℂ))
                ^ (-(2 * s + 1) - ((abm w).2.2 : ℂ) / 2))
      = archF kdat abm s (InfiniteAdeleRing.ringEquiv_mixedSpace F x) := by
  rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  unfold archF
  dsimp only
  congr 1
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [hRr i _ (Real.rpow_pos_of_pos (by positivity) _), one_mul]
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [hRc w _ (Real.rpow_pos_of_pos (by positivity) _), one_mul]

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

private theorem norm_sub_I (x : ℝ) : ‖(x : ℂ) - Complex.I‖ = Real.sqrt (1 + x ^ 2) := by
  rw [← Real.sqrt_sq (norm_nonneg ((x : ℂ) - Complex.I)), Complex.sq_norm, Complex.normSq_apply]
  congr 1
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.I_re, sub_zero, Complex.sub_im, Complex.ofReal_im,
    Complex.I_im, zero_sub]
  ring

private theorem norm_unit (x : ℝ) :
    ‖((x : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)‖ = 1 := by
  have hpos : 0 < Real.sqrt (1 + x ^ 2) := Real.sqrt_pos.2 (by positivity)
  rw [norm_div, norm_sub_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos, div_self hpos.ne']

private theorem unit_ne_zero (x : ℝ) : ((x : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ) ≠ 0 := by
  intro h
  have h1 := norm_unit x
  rw [h, norm_zero] at h1
  exact zero_ne_one h1

private theorem integrable_realFactor (k : ℤ) (s : ℂ) (hs : 0 < s.re) :
    Integrable (fun x : ℝ => (((x : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ k
      * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-(s + 1 / 2))) := by
  have hmaj : Integrable (fun x : ℝ => ((1 : ℝ) + ‖x‖ ^ 2) ^ (-(2 * s.re + 1) / 2)) :=
    integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (by rw [Module.finrank_self]; push_cast; linarith)
  refine hmaj.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · refine (Continuous.mul ?_ ?_).aestronglyMeasurable
    · exact Continuous.zpow₀ (Continuous.div (by fun_prop) (by fun_prop)
        (fun x => Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (by positivity)).ne')) k
        (fun x => Or.inl (unit_ne_zero x))
    · exact Continuous.cpow (by fun_prop) continuous_const
        (fun x => Complex.ofReal_mem_slitPlane.2 (by positivity))
  · have hre : (-(s + 1 / 2)).re = -(2 * s.re + 1) / 2 := by
      simp; ring
    have heq : ‖(((x : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ k
        * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-(s + 1 / 2))‖
          = ((1 : ℝ) + ‖x‖ ^ 2) ^ (-(2 * s.re + 1) / 2) := by
      rw [norm_mul, norm_zpow, norm_unit x, one_zpow, one_mul,
        Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), hre, Real.norm_eq_abs, sq_abs]
    exact heq.le

private theorem integrable_complexFactor (a b m : ℕ) (habm : a + b ≤ m) (s : ℂ) (hs : 0 < s.re) :
    Integrable (fun z : ℂ => z ^ a * (starRingEnd ℂ) z ^ b
      * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-(2 * s + 1) - (m : ℂ) / 2)) := by
  have hmaj : Integrable (fun z : ℂ => ((1 : ℝ) + ‖z‖ ^ 2) ^ (-(2 * (2 * s.re + 1)) / 2)) :=
    integrable_rpow_neg_one_add_norm_sq (E := ℂ) (μ := volume)
      (by rw [Complex.finrank_real_complex]; push_cast; linarith)
  refine hmaj.mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
  · refine ((Continuous.mul (by fun_prop) (by fun_prop)).mul ?_).aestronglyMeasurable
    exact Continuous.cpow (by fun_prop) continuous_const (fun z => Complex.ofReal_mem_slitPlane.2 (by positivity))
  · have hB1 : (1 : ℝ) ≤ 1 + ‖z‖ ^ 2 := le_add_of_nonneg_right (sq_nonneg _)
    have hBpos : (0 : ℝ) < 1 + ‖z‖ ^ 2 := by linarith
    have hre : (-(2 * s + 1) - (m : ℂ) / 2).re = -(2 * s.re + 1 + (m : ℝ) / 2) := by
      simp; ring
    rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_conj,
      Complex.norm_cpow_eq_rpow_re_of_pos hBpos, hre]
    have hz : ‖z‖ ≤ (1 + ‖z‖ ^ 2) ^ ((1 : ℝ) / 2) := by
      calc ‖z‖ = Real.sqrt (‖z‖ ^ 2) := (Real.sqrt_sq (norm_nonneg z)).symm
        _ ≤ Real.sqrt (1 + ‖z‖ ^ 2) := Real.sqrt_le_sqrt (by linarith)
        _ = (1 + ‖z‖ ^ 2) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _
    have hzab : ‖z‖ ^ a * ‖z‖ ^ b ≤ (1 + ‖z‖ ^ 2) ^ ((m : ℝ) / 2) := by
      calc ‖z‖ ^ a * ‖z‖ ^ b = ‖z‖ ^ (a + b) := (pow_add _ _ _).symm
        _ ≤ ((1 + ‖z‖ ^ 2) ^ ((1 : ℝ) / 2)) ^ (a + b) := pow_le_pow_left₀ (norm_nonneg z) hz _
        _ = (1 + ‖z‖ ^ 2) ^ ((1 : ℝ) / 2 * ((a + b : ℕ) : ℝ)) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hBpos.le]
        _ ≤ (1 + ‖z‖ ^ 2) ^ ((m : ℝ) / 2) := by
            refine Real.rpow_le_rpow_of_exponent_le hB1 ?_
            have hm : ((a + b : ℕ) : ℝ) ≤ m := by exact_mod_cast habm
            linarith
    calc ‖z‖ ^ a * ‖z‖ ^ b * (1 + ‖z‖ ^ 2) ^ (-(2 * s.re + 1 + (m : ℝ) / 2))
        ≤ (1 + ‖z‖ ^ 2) ^ ((m : ℝ) / 2) * (1 + ‖z‖ ^ 2) ^ (-(2 * s.re + 1 + (m : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_right hzab (Real.rpow_nonneg hBpos.le _)
      _ = ((1 : ℝ) + ‖z‖ ^ 2) ^ (-(2 * (2 * s.re + 1)) / 2) := by
          rw [← Real.rpow_add hBpos]; congr 1; ring

open scoped Classical in

private theorem integrable_archF (kdat : {w : InfinitePlace F // w.IsReal} → ℤ)
    (abm : {w : InfinitePlace F // w.IsComplex} → ℕ × ℕ × ℕ)
    (habm : ∀ w, (abm w).1 + (abm w).2.1 ≤ (abm w).2.2) (s : ℂ) (hs : 0 < s.re) :
    Integrable (archF kdat abm s) := by
  unfold archF
  rw [MeasureTheory.Measure.volume_eq_prod]
  refine Integrable.mul_prod
    (f := fun x : {w : InfinitePlace F // w.IsReal} → ℝ => ∏ i,
      ((((x i : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + (x i) ^ 2) : ℝ) : ℂ)) ^ (kdat i)
        * (((1 + (x i) ^ 2 : ℝ) : ℂ)) ^ (-(s + 1 / 2)))
    (g := fun z : {w : InfinitePlace F // w.IsComplex} → ℂ => ∏ w,
      (z w) ^ (abm w).1 * (starRingEnd ℂ) (z w) ^ (abm w).2.1
        * (((1 + ‖z w‖ ^ 2 : ℝ) : ℂ)) ^ (-(2 * s + 1) - ((abm w).2.2 : ℂ) / 2)) ?_ ?_
  · rw [MeasureTheory.volume_pi]
    exact Integrable.fintype_prod (f := fun i (x : ℝ) =>
      ((((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ (kdat i)
        * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-(s + 1 / 2))) fun i => integrable_realFactor _ s hs
  · rw [MeasureTheory.volume_pi]
    exact Integrable.fintype_prod (f := fun w (z : ℂ) =>
      z ^ (abm w).1 * (starRingEnd ℂ) z ^ (abm w).2.1
        * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-(2 * s + 1) - ((abm w).2.2 : ℂ) / 2))
      fun w => integrable_complexFactor _ _ _ (habm w) s hs

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

open Asymptotics _root_.Filter _root_.Asymptotics.Filter Topology in

private theorem tendsto_zero_of_parts {ι : Type*} (S : Finset ι) {l : Filter ℝ}
    (E : ℝ → ℂ) (K : ℂ) (c : ι → ℂ) (Af PI dI : ι → ℝ → ℂ)
    (hE : E =O[l] (fun _ => (1 : ℝ))) (hAf : ∀ j ∈ S, Af j =O[l] (fun _ => (1 : ℝ)))
    (hPI : ∀ j ∈ S, PI j =O[l] (fun _ => (1 : ℝ))) (hdI : ∀ j ∈ S, Tendsto (dI j) l (𝓝 0)) :
    Tendsto (fun σ => E σ * K * ∑ j ∈ S, c j * (Af j σ * (PI j σ * dI j σ))) l (𝓝 0) := by
  have hsum : (fun σ => ∑ j ∈ S, c j * (Af j σ * (PI j σ * dI j σ))) =o[l] (fun _ => (1 : ℝ)) := by
    refine IsLittleO.fun_sum fun j hj => ?_
    have h1 : (dI j) =o[l] (fun _ => (1 : ℝ)) := (isLittleO_one_iff ℝ).2 (hdI j hj)
    have h4 := ((isBigO_const_const (c j) (one_ne_zero : (1 : ℝ) ≠ 0) l).mul_isLittleO
      ((hAf j hj).mul_isLittleO ((hPI j hj).mul_isLittleO h1)))
    exact h4.congr_right fun _ => by norm_num
  have hK : (fun _ : ℝ => K) =O[l] (fun _ => (1 : ℝ)) := isBigO_const_const _ one_ne_zero _
  have h : (fun σ => E σ * K * ∑ j ∈ S, c j * (Af j σ * (PI j σ * dI j σ))) =o[l] (fun _ => (1 : ℝ)) :=
    ((hE.mul hK).mul_isLittleO hsum).congr_right fun _ => by norm_num
  exact (isLittleO_one_iff ℝ).1 h

end W6Kit

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
      (v : HeightOneSpectrum (𝓞 F)),
    letI := NumberField.AdelicHaar.adeleBorel (𝓞 F) F
    Tendsto (fun s : ℂ => (s - 1 / 2) *
        (weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s)
            (AdelicDock.finEmbed (𝓞 F) F (AdelicDock.localEmbed (𝓞 F) F v gl2Weyl))
          - weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) 1))
      (𝓝[{s : ℂ | 1 / 2 < s.re}] (1 / 2 : ℂ)) (𝓝 0) := by
  intro α hα φ hφ hφK hφf hφjc hφhol hφflat v
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := NumberField.AdelicHaar.adeleBorel (𝓞 F) F
  haveI : BorelSpace (AdeleRing (𝓞 F) F) := NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 F) F
  set U : Set ℂ := {s : ℂ | 1 / 2 < s.re} with hU
  set W : AdelicGL2 (𝓞 F) F := AdelicDock.finEmbed (𝓞 F) F (AdelicDock.localEmbed (𝓞 F) F v gl2Weyl) with hWdef

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
  obtain ⟨JW, hJWan, hJWeq⟩ := hJg W
  obtain ⟨J1, hJ1an, hJ1eq⟩ := hJg 1

  have hDeq : ∀ s : ℂ, 1 / 2 < s.re →
      (s - 1 / 2) * (weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) W
          - weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) 1) = JW s - J1 s := by
    intro s hs; rw [hJWeq s hs, hJ1eq s hs]; ring
  have hDan : AnalyticAt ℂ (fun s => JW s - J1 s) (1 / 2) := hJWan.sub hJ1an
  have hDlim : Tendsto (fun s : ℂ => (s - 1 / 2) *
      (weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) W
        - weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) 1))
      (𝓝[U] (1 / 2 : ℂ)) (𝓝 (JW (1 / 2) - J1 (1 / 2))) :=
    (hDan.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
      (eventually_nhdsWithin_of_forall (fun s hs => (hDeq s hs).symm))

  suffices hray : Tendsto (fun σ : ℝ => ((σ : ℂ) - 1 / 2) *
      (weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ σ) W
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
  set T : Finset (HeightOneSpectrum (𝓞 F)) := insert v S with hT
  have hvT : v ∈ T := Finset.mem_insert_self v S
  have hST : S ⊆ T := Finset.subset_insert v S
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

  set fA : Fin n → ℝ → mixedEmbedding.mixedSpace F → ℂ :=
    fun j σ => W6Kit.archF (kdat j) (abm j) (σ : ℂ) with hfA
  set hfun : Fin n → ℝ → ∀ u : HeightOneSpectrum (𝓞 F), u.adicCompletion F → ℂ :=
    fun j σ u => W6Kit.atom u (A' j u) (B' j u) (σ : ℂ) with hhfun
  set mW : ℝ → ∀ u : HeightOneSpectrum (𝓞 F), u.adicCompletion F → ℂ :=
    fun σ u y => (((LanglandsTunnell.TateLocal.modulus y : ℝ≥0) : ℝ) : ℂ) ^ (-(2 * (σ : ℂ) + 1)) with hmW
  set htil : Fin n → ℝ → ∀ u : HeightOneSpectrum (𝓞 F), u.adicCompletion F → ℂ :=
    fun j σ u y => if u = v then mW σ u y * hfun j σ u y⁻¹ else hfun j σ u y with hhtil
  have hhtil_v : ∀ j σ, htil j σ v = fun y => mW σ v y * hfun j σ v y⁻¹ := by
    intro j σ; funext y; simp only [hhtil, if_pos rfl]
  have hhtil_ne : ∀ j σ u, u ≠ v → htil j σ u = hfun j σ u := by
    intro j σ u hu; funext y; simp only [hhtil, if_neg hu]

  have hexp1 : ∀ (σ : ℝ) (x : AdeleRing (𝓞 F) F),
      φ σ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x)
        = ∑ j : Fin n, c j * W6Kit.tensor T χ₀ (fA j σ) (hfun j σ) (σ : ℂ) x := by
    intro σ x
    rw [hbig]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_assoc (c j), W6Kit.arch_eq_archF (kdat j) (abm j) Rr Rc hRr1 hRc1, mul_assoc,
      W6Kit.reindex S T hST χ₀ hχext (A j) (B j) (A' j) (B' j) (hA'S j) (hB'S j) (hA'c j) (hB'c j),
      mul_assoc]
    rfl

  have hexpW : ∀ (σ : ℝ) (x : AdeleRing (𝓞 F) F), x.2 v ≠ 0 →
      φ σ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * W)
        = ∑ j : Fin n, c j * W6Kit.tensor T χ₀ (fA j σ) (htil j σ) (σ : ℂ) x := by
    intro σ x hx
    have hW1 : φ σ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * W)
        = mW σ v (x.2 v)
          * φ σ ((adelicWeyl (𝓞 F) F)⁻¹
              * unipotentGL2 (R := AdeleRing (𝓞 F) F) (x.1, AdelicDock.splice (𝓞 F) F v x.2 (x.2 v)⁻¹)) :=
      AutomorphicForm.apply_weylInv_unipotent_mul_localWeyl_eq_modulus_cpow_mul_apply F hα σ (φ σ) (hφ σ) v x hx
    rw [hW1]; erw [hexp1]; rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_left_comm]
    congr 1
    simp only [W6Kit.tensor]
    rw [mul_left_comm]
    congr 1
    exact W6Kit.transport T v hvT χ₀ (hfun j σ) (htil j σ) (mW σ) (σ : ℂ) (hhtil_v j σ) (hhtil_ne j σ) x.2

  have hM1 : ∀ σ : ℝ, weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ σ) 1
      = ∫ x, ∑ j : Fin n, c j * W6Kit.tensor T χ₀ (fA j σ) (hfun j σ) (σ : ℂ) x ∂(adelicAddHaar (𝓞 F) F) := by
    intro σ
    simp only [weylIntertwiningIntegral, mul_one]
    exact integral_congr_ae (Eventually.of_forall fun x => hexp1 σ x)
  have hMW : ∀ σ : ℝ, weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ σ) W
      = ∫ x, ∑ j : Fin n, c j * W6Kit.tensor T χ₀ (fA j σ) (htil j σ) (σ : ℂ) x ∂(adelicAddHaar (𝓞 F) F) := by
    intro σ
    simp only [weylIntertwiningIntegral]
    refine integral_congr_ae ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1
      (NumberField.AdelicHaar.adelicAddHaar_setOf_snd_apply_eq_zero F v)] with x hx
    exact hexpW σ x hx

  have hint1 : ∀ (j : Fin n) (σ : ℝ), 1 / 2 < σ →
      Integrable (W6Kit.tensor T χ₀ (fA j σ) (hfun j σ) (σ : ℂ)) (adelicAddHaar (𝓞 F) F) := by
    intro j σ hσ
    have hσ0 : 0 < ((σ : ℂ)).re := by simp; linarith
    refine W6Kit.integrable_tensor νf μv ϖ hϖ T χ₀ hχext (hfun j σ) (fA j σ)
      (W6Kit.integrable_archF _ _ (habm j) _ hσ0) (σ : ℂ) (by simpa using hσ) (fun u _ => ?_)
    exact (AutomorphicForm.LocalIntertwining.integrable_smoothAtom_and_integrable_weylShift_adicCompletion F u
      (μv u) m hm (A' j u) (B' j u) (hA'lc j u) (hB'lc j u) (σ : ℂ) hσ0).1
  have hintW : ∀ (j : Fin n) (σ : ℝ), 1 / 2 < σ →
      Integrable (W6Kit.tensor T χ₀ (fA j σ) (htil j σ) (σ : ℂ)) (adelicAddHaar (𝓞 F) F) := by
    intro j σ hσ
    have hσ0 : 0 < ((σ : ℂ)).re := by simp; linarith
    refine W6Kit.integrable_tensor νf μv ϖ hϖ T χ₀ hχext (htil j σ) (fA j σ)
      (W6Kit.integrable_archF _ _ (habm j) _ hσ0) (σ : ℂ) (by simpa using hσ) (fun u _ => ?_)
    by_cases hu : u = v
    · subst hu
      rw [hhtil_v]
      exact (AutomorphicForm.LocalIntertwining.integrable_smoothAtom_and_integrable_weylShift_adicCompletion F u
        (μv u) m hm (A' j u) (B' j u) (hA'lc j u) (hB'lc j u) (σ : ℂ) hσ0).2
    · rw [hhtil_ne j σ u hu]
      exact (AutomorphicForm.LocalIntertwining.integrable_smoothAtom_and_integrable_weylShift_adicCompletion F u
        (μv u) m hm (A' j u) (B' j u) (hA'lc j u) (hB'lc j u) (σ : ℂ) hσ0).1
  have hM1' : ∀ σ : ℝ, 1 / 2 < σ → weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ σ) 1
      = ∑ j : Fin n, c j * ∫ x, W6Kit.tensor T χ₀ (fA j σ) (hfun j σ) (σ : ℂ) x ∂(adelicAddHaar (𝓞 F) F) := by
    intro σ hσ
    rw [hM1 σ, integral_finsetSum _ (fun j _ => (hint1 j σ hσ).const_mul (c j))]
    exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
  have hMW' : ∀ σ : ℝ, 1 / 2 < σ → weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ σ) W
      = ∑ j : Fin n, c j * ∫ x, W6Kit.tensor T χ₀ (fA j σ) (htil j σ) (σ : ℂ) x ∂(adelicAddHaar (𝓞 F) F) := by
    intro σ hσ
    rw [hMW σ, integral_finsetSum _ (fun j _ => (hintW j σ hσ).const_mul (c j))]
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
  set It : Fin n → ℝ → HeightOneSpectrum (𝓞 F) → ℂ := fun j σ u =>
    (((μv u).real (u.adicCompletionIntegers F : Set (u.adicCompletion F)) : ℂ)⁻¹
      * ∫ y, htil j σ u y ∂(μv u)) with hIt

  set Af : Fin n → ℝ → ℂ := fun j σ => ∫ y, fA j σ y with hAf

  set Z0 : ℝ → ℂ := fun σ => NumberField.dedekindZeta F (2 * (σ : ℂ)) * FS T (2 * (σ : ℂ)) with hZ0
  set Z1 : ℝ → ℂ := fun σ => NumberField.dedekindZeta F (2 * (σ : ℂ) + 1) * FS T (2 * (σ : ℂ) + 1) with hZ1
  have hZ0ne : ∀ σ : ℝ, 1 / 2 < σ → Z0 σ ≠ 0 := fun σ hσ => (hpartial T (2 * (σ : ℂ)) (by simp; linarith)).1
  have hZ1ne : ∀ σ : ℝ, 1 / 2 < σ → Z1 σ ≠ 0 := fun σ hσ => (hpartial T (2 * (σ : ℂ) + 1) (by simp; linarith)).1
  have hGK : ∀ (j : Fin n) (σ : ℝ), 1 / 2 < σ →
      ∀ (h : ∀ u : HeightOneSpectrum (𝓞 F), u.adicCompletion F → ℂ),
        cbox⁻¹ * (∫ x, W6Kit.tensor T χ₀ (fA j σ) h (σ : ℂ) x ∂(adelicAddHaar (𝓞 F) F)) * (Z0 σ)⁻¹
          = cF * Af j σ
            * ((∏ u ∈ T, (((μv u).real (u.adicCompletionIntegers F : Set (u.adicCompletion F)) : ℂ)⁻¹
                * ∫ y, h u y ∂(μv u))) * (Z1 σ)⁻¹) := by
    intro j σ hσ h
    have hσ' : 1 / 2 < ((σ : ℂ)).re := by simpa using hσ
    have h0 := AutomorphicForm.LocalIntertwining.integral_adeleRing_pureTensor_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod
      F (adelicAddHaar (𝓞 F) F) T μv (fA j σ) h ϖ (fun u _ => hϖ u) χ₀ (fun u _ t _ => hχ₀U u t)
      (fun u _ => by rw [hχ₀U, Units.val_one, norm_one]) (σ : ℂ) hσ'
    simp only [hχ₀U, Units.val_one, one_mul] at h0
    rw [(hpartial T (2 * (σ : ℂ)) (by simp; linarith)).2,
      (hpartial T (2 * (σ : ℂ) + 1) (by simp; linarith)).2] at h0
    exact h0

  have hval : ∀ (j : Fin n) (σ : ℝ), 1 / 2 < σ →
      ∀ (h : ∀ u : HeightOneSpectrum (𝓞 F), u.adicCompletion F → ℂ),
        ∫ x, W6Kit.tensor T χ₀ (fA j σ) h (σ : ℂ) x ∂(adelicAddHaar (𝓞 F) F)
          = cbox * Z0 σ * (Z1 σ)⁻¹ * cF * Af j σ
            * ∏ u ∈ T, (((μv u).real (u.adicCompletionIntegers F : Set (u.adicCompletion F)) : ℂ)⁻¹
                * ∫ y, h u y ∂(μv u)) := by
    intro j σ hσ h
    have h0 := hGK j σ hσ h
    have hz0 := hZ0ne σ hσ
    calc _ = cbox * Z0 σ * (cbox⁻¹ * (∫ x, W6Kit.tensor T χ₀ (fA j σ) h (σ : ℂ) x ∂(adelicAddHaar (𝓞 F) F))
              * (Z0 σ)⁻¹) := by field_simp
      _ = _ := by rw [h0]; ring

  have hprod : ∀ (j : Fin n) (σ : ℝ),
      (∏ u ∈ T, It j σ u) - (∏ u ∈ T, I j σ u) = (∏ u ∈ T.erase v, I j σ u) * (It j σ v - I j σ v) := by
    intro j σ
    rw [← Finset.mul_prod_erase T _ hvT, ← Finset.mul_prod_erase T _ hvT]
    have he : ∏ u ∈ T.erase v, It j σ u = ∏ u ∈ T.erase v, I j σ u :=
      Finset.prod_congr rfl fun u hu => by
        simp only [hIt, hI, hhtil_ne j σ u (Finset.ne_of_mem_erase hu)]
    rw [he]
    ring

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
  have hAfO : ∀ j : Fin n, Af j =O[𝓝[>] (1 / 2 : ℝ)] (fun _ => (1 : ℝ)) := by
    intro j
    obtain ⟨C, hC⟩ := AutomorphicForm.LocalIntertwining.exists_bound_norm_integral_mixedSpace_archAtom_prod F
      (kdat j) (abm j) (habm j)
    refine Asymptotics.IsBigO.of_bound C ?_
    filter_upwards [hIoo] with σ hσ
    rw [norm_one, mul_one]
    exact hC σ hσ.1 hσ.2.le
  have hIO : ∀ (j : Fin n), ∀ u ∈ T.erase v, (fun σ => I j σ u) =O[𝓝[>] (1 / 2 : ℝ)] (fun _ => (1 : ℝ)) := by
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
  have hPIO : ∀ j : Fin n, (fun σ => ∏ u ∈ T.erase v, I j σ u) =O[𝓝[>] (1 / 2 : ℝ)] (fun _ => (1 : ℝ)) := by
    intro j
    have h := Asymptotics.IsBigO.finsetProd (fun u hu => hIO j u hu)
    exact h.congr_right fun _ => Finset.prod_const_one
  have hdI : ∀ j : Fin n, Tendsto (fun σ => It j σ v - I j σ v) (𝓝[>] (1 / 2 : ℝ)) (𝓝 0) := by
    intro j
    have h := (AutomorphicForm.LocalIntertwining.bounded_and_tendsto_integral_weylShift_sub_integral_smoothAtom_adicCompletion
      F v (μv v) m hm (A' j v) (B' j v) (hA'lc j v) (hB'lc j v)).2.const_mul
      (((μv v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℂ)⁻¹)
    rw [mul_zero] at h
    refine h.congr fun σ => ?_
    simp only [hIt, hI, hhtil_v j σ, hmW, hhfun, W6Kit.atom, mul_sub]

  have hD : ∀ σ : ℝ, 1 / 2 < σ →
      ((σ : ℂ) - 1 / 2) * (weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ σ) W
        - weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ σ) 1)
      = E σ * (cbox * cF) * ∑ j : Fin n, c j * (Af j σ * ((∏ u ∈ T.erase v, I j σ u) * (It j σ v - I j σ v))) := by
    intro σ hσ
    rw [hMW' σ hσ, hM1' σ hσ, ← Finset.sum_sub_distrib, hE, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hval j σ hσ (htil j σ), hval j σ hσ (hfun j σ), ← hprod j σ]
    simp only [hIt, hI]
    ring
  refine (W6Kit.tendsto_zero_of_parts (Finset.univ : Finset (Fin n)) E (cbox * cF) c Af
    (fun j σ => ∏ u ∈ T.erase v, I j σ u) (fun j σ => It j σ v - I j σ v)
    (hElim.isBigO_one ℝ) (fun j _ => hAfO j) (fun j _ => hPIO j) (fun j _ => hdI j)).congr' ?_
  exact eventually_nhdsWithin_of_forall fun σ hσ => (hD σ hσ).symm

end S_AutomorphicForm_tendsto_sub_one_half_mul_weylIntertwiningIntegral_localWeyl_sub_nhds_zero_of_flat_family
end P2MW
export P2MW.S_AutomorphicForm_tendsto_sub_one_half_mul_weylIntertwiningIntegral_localWeyl_sub_nhds_zero_of_flat_family (solution)
