-- Prove2me | solution 1 for AutomorphicForm.summable_norm_a_sq_mul_rpow_absNorm_of_isArithGenuineCuspRealizable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/177e5160-1567-57dd-a5c6-6fdba3d5911e

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_NarrowRayClassGroup
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.NumberTheory.LSeries.Deriv
import Theorems.Thm_AutomorphicForm_exists_finset_lt_one_meromorphicOn_analyticAt_hasProd_rsEulerPoly_self_and_eval_inv_absNorm_ne_zero
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_nonneg_hasSum_mul_pow_inv_eval_rsEulerPoly_conj_self
import Theorems.Thm_LSeries_exists_hasProd_tsum_eq_lseries_of_norm_le_pow
import Theorems.Thm_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball
import Theorems.Thm_LanglandsTunnell_Converse_exists_finset_sq_eq_real_mul_b_and_norm_sq_lt_of_isArithGenuineCuspRealizable
import Theorems.Thm_AutomorphicForm_SiegelCovering_coversModCentre_productionPinsGeneral_D_rat
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_exists_prime_and_asIdeal_eq_span_ringOfIntegers_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_summable_norm_a_sq_mul_rpow_absNorm_of_isArithGenuineCuspRealizable
p2m_attr_erase "instance" "AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension"
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.isScalarTower_fixFldDetKer_fixFldQuatH_L LanglandsTunnell.isScalarTower_rat_fixFldSylowH_fixFldQuatH LanglandsTunnell.detKer_normal LanglandsTunnell.isScalarTower_rat_fixFldDetKer_fixFldQuatH LanglandsTunnell.algebra_fixFldDetKer_fixFldQuatH LanglandsTunnell.isScalarTower_fixFldSylowH_fixFldQuatH_L LanglandsTunnell.algebra_fixFldSylowH_fixFldQuatH LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalConstituent.rightRegular_apply AutomorphicForm.IsStableLinearOn.coe_toEnd_apply AutomorphicForm.ArchRepAt.mk.sizeOf_spec AutomorphicForm.IsIsotypicCuspFormAt.toRealization_toFun AutomorphicForm.ArchTypeFamily.mk.sizeOf_spec AutomorphicForm.charRep_apply AutomorphicForm.ArchRepAt.mk.injEq AutomorphicForm.ArchTypeFamily.mk.injEq M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq AutomorphicForm.mem_inducedSectionSubmodule_iff AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val AutomorphicForm.cpowChar_apply_val AutomorphicForm.gl2Weyl_val AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.StandardAddChar.ratArchLine_apply NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.charExt_zero UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AutomorphicForm.rightTranslationEmbed_smul_apply NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def"
p2m_attr_erase "simp" "TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul AutomorphicForm.mem_sigmaCentralizer_iff M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply"
p2m_attr_erase "simp" "Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec LanglandsTunnell.signShift_zero LanglandsTunnell.RealArchParam.twist_zero LanglandsTunnell.RealArchParam.discrete.sizeOf_spec LanglandsTunnell.RealArchParam.principal.injEq LanglandsTunnell.ComplexArchParam.dual_dual LanglandsTunnell.ComplexArchParam.mk.sizeOf_spec LanglandsTunnell.RealArchParam.dual_dual LanglandsTunnell.RealArchParam.discrete.injEq LanglandsTunnell.ComplexArchParam.twist_zero LanglandsTunnell.RealArchParam.principal.sizeOf_spec LanglandsTunnell.signShift_one LanglandsTunnell.ComplexArchParam.mk.injEq AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.ArchDirComplex.iH.sizeOf_spec AutomorphicForm.ArchDirComplex.H.sizeOf_spec AutomorphicForm.ArchDirComplex.Fm.sizeOf_spec AutomorphicForm.ArchDirComplex.iFm.sizeOf_spec AutomorphicForm.ArchDirComplex.iE.sizeOf_spec AutomorphicForm.ArchDirComplex.E.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply AutomorphicForm.iotaZsqrtdNegTwo_apply AutomorphicForm.JPSSCubicLiftPackage.mk.sizeOf_spec AutomorphicForm.formalBaseChange_a AutomorphicForm.JPSSCubicLiftPackage.mk.injEq AutomorphicForm.formalBaseChange_b LanglandsTunnell.signEpsilon_one LanglandsTunnell.RealArchParam.epsilonFactor_principal LanglandsTunnell.RealArchParam.epsilonFactor_discrete LanglandsTunnell.signEpsilon_zero"

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped Classical
open scoped ComplexOrder

noncomputable section

namespace RS11

open Polynomial Filter Topology

variable {K : Type} [Field K] [NumberField K]

abbrev locPoly (Θ : HeckeEigensystem K ℂ) (v : HeightOneSpectrum (𝓞 K)) : ℂ[X] :=
  LanglandsTunnell.RankinSelberg.rsEulerPoly (Θ.a v / Θ.b v) (Θ.b v)⁻¹ (Θ.a v) (Θ.b v) 0

abbrev locEval (Θ : HeckeEigensystem K ℂ) (v : HeightOneSpectrum (𝓞 K)) (s : ℂ) : ℂ :=
  (locPoly Θ v).eval (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))

theorem absNorm_ne_zero (v : HeightOneSpectrum (𝓞 K)) : Ideal.absNorm v.asIdeal ≠ 0 := by
  rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot

theorem two_le_absNorm (v : HeightOneSpectrum (𝓞 K)) : 2 ≤ Ideal.absNorm v.asIdeal := by
  have h0 := absNorm_ne_zero v
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  omega

theorem rsEulerPoly_coeff_zero {R : Type*} [CommRing R] (a b e₁ e₂ e₃ : R) :
    (LanglandsTunnell.RankinSelberg.rsEulerPoly a b e₁ e₂ e₃).coeff 0 = 1 := by
  simp [LanglandsTunnell.RankinSelberg.rsEulerPoly, coeff_one, coeff_X, coeff_C, coeff_X_pow]

theorem exists_forall_eval_cpow_neg_ne_zero (P : ℂ[X]) (hP : P.coeff 0 = 1) (N : ℕ) (hN : 2 ≤ N) :
    ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re → P.eval (((N : ℕ) : ℂ) ^ (-s)) ≠ 0 := by
  have h0 : P.eval 0 = 1 := by rw [← coeff_zero_eq_eval_zero]; exact hP
  have hcont : ContinuousAt (fun x : ℂ => P.eval x) 0 := P.continuous.continuousAt
  obtain ⟨δ, hδ, hδP⟩ := (Metric.continuousAt_iff.mp hcont) (1 / 2) (by norm_num)
  have hNr : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hN)
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_trans zero_lt_one hNr
  refine ⟨Real.logb N (1 / δ), fun s hs => ?_⟩
  have hsmall : ‖((N : ℕ) : ℂ) ^ (-s)‖ < δ := by
    rw [Complex.norm_natCast_cpow_of_pos (lt_of_lt_of_le (by norm_num) hN), Complex.neg_re]
    calc (N : ℝ) ^ (-s.re) < (N : ℝ) ^ (-Real.logb N (1 / δ)) :=
          Real.rpow_lt_rpow_of_exponent_lt hNr (by linarith)
      _ = δ := by
          rw [Real.rpow_neg hNpos.le, Real.rpow_logb hNpos hNr.ne' (by positivity), one_div, inv_inv]
  intro hzero
  have := hδP (x := ((N : ℕ) : ℂ) ^ (-s)) (by simpa [dist_zero_right] using hsmall)
  rw [hzero, h0, dist_eq_norm] at this
  norm_num at this

theorem differentiable_locEval (Θ : HeckeEigensystem K ℂ) (v : HeightOneSpectrum (𝓞 K)) :
    Differentiable ℂ (locEval Θ v) := by
  have hN : (((Ideal.absNorm v.asIdeal : ℕ) : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (absNorm_ne_zero v)
  have h : (fun s : ℂ => (((Ideal.absNorm v.asIdeal : ℕ) : ℂ)) ^ (-s)) =
      fun s => Complex.exp (Complex.log (((Ideal.absNorm v.asIdeal : ℕ) : ℂ)) * (-s)) := by
    funext s; rw [Complex.cpow_def_of_ne_zero hN]
  have hd : Differentiable ℂ (fun s : ℂ => (((Ideal.absNorm v.asIdeal : ℕ) : ℂ)) ^ (-s)) := by
    rw [h]; fun_prop
  exact (locPoly Θ v).differentiable.comp hd

theorem hasProd_subtype_notMem_of_subset {β : Type*} (f : β → ℂ) {S T : Finset β} (hST : S ⊆ T)
    {a : ℂ} (h : HasProd (fun x : {x // x ∉ S} => f x) a) (hf : ∀ b ∈ T \ S, f b ≠ 0) :
    HasProd (fun x : {x // x ∉ T} => f x) (a * ∏ b ∈ T \ S, (f b)⁻¹) := by
  classical

  have h1 : HasProd (({x | x ∉ S} : Set β).mulIndicator f) a :=
    (hasProd_subtype_iff_mulIndicator (s := ({x | x ∉ S} : Set β)) (f := f)).mp h

  have h2 : HasProd (((↑(T \ S) : Set β)).mulIndicator fun x => (f x)⁻¹) (∏ b ∈ T \ S, (f b)⁻¹) :=
    (hasProd_subtype_iff_mulIndicator (s := ((↑(T \ S) : Set β))) (f := fun x => (f x)⁻¹)).mp
      (Finset.hasProd (T \ S) fun x => (f x)⁻¹)
  have h3 := h1.mul h2

  have hpt : (fun x => ({x | x ∉ S} : Set β).mulIndicator f x *
      ((↑(T \ S) : Set β)).mulIndicator (fun x => (f x)⁻¹) x) = ({x | x ∉ T} : Set β).mulIndicator f := by
    funext x
    by_cases hxT : x ∈ T
    · by_cases hxS : x ∈ S
      · have h1' : x ∉ ({x | x ∉ S} : Set β) := fun h => h hxS
        have h2' : x ∉ ((↑(T \ S) : Set β)) := by
          rw [Finset.mem_coe, Finset.mem_sdiff]; exact fun h => h.2 hxS
        have h3' : x ∉ ({x | x ∉ T} : Set β) := fun h => h hxT
        rw [Set.mulIndicator_of_notMem h1', Set.mulIndicator_of_notMem h2', Set.mulIndicator_of_notMem h3',
          one_mul]
      · have h1' : x ∈ ({x | x ∉ S} : Set β) := hxS
        have h2' : x ∈ ((↑(T \ S) : Set β)) := by
          rw [Finset.mem_coe, Finset.mem_sdiff]; exact ⟨hxT, hxS⟩
        have h3' : x ∉ ({x | x ∉ T} : Set β) := fun h => h hxT
        rw [Set.mulIndicator_of_mem h1', Set.mulIndicator_of_mem h2', Set.mulIndicator_of_notMem h3',
          mul_inv_cancel₀ (hf x (Finset.mem_sdiff.mpr ⟨hxT, hxS⟩))]
    · have hxS : x ∉ S := fun h => hxT (hST h)
      have h1' : x ∈ ({x | x ∉ S} : Set β) := hxS
      have h2' : x ∉ ((↑(T \ S) : Set β)) := by
        rw [Finset.mem_coe, Finset.mem_sdiff]; exact fun h => hxT h.1
      have h3' : x ∈ ({x | x ∉ T} : Set β) := hxT
      rw [Set.mulIndicator_of_mem h1', Set.mulIndicator_of_notMem h2', Set.mulIndicator_of_mem h3', mul_one]
  rw [hpt] at h3
  exact (hasProd_subtype_iff_mulIndicator (s := ({x | x ∉ T} : Set β)) (f := f)).mpr h3

theorem exists_prime_absNorm_eq (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ p : ℕ, p.Prime ∧ v.asIdeal = Ideal.span {(p : 𝓞 ℚ)} ∧ Ideal.absNorm v.asIdeal = p := by
  obtain ⟨p, hp, hv⟩ :=
    IsDedekindDomain.HeightOneSpectrum.exists_prime_and_asIdeal_eq_span_ringOfIntegers_rat v
  refine ⟨p, hp, hv, ?_⟩
  rw [hv, Ideal.absNorm_span_natCast, NumberField.RingOfIntegers.rank, Module.finrank_self, pow_one]

theorem absNorm_prime (v : HeightOneSpectrum (𝓞 ℚ)) : (Ideal.absNorm v.asIdeal).Prime := by
  obtain ⟨p, hp, -, h⟩ := exists_prime_absNorm_eq v
  rwa [h]

theorem absNorm_injective :
    Function.Injective fun v : HeightOneSpectrum (𝓞 ℚ) => Ideal.absNorm v.asIdeal := by
  intro v w hvw
  obtain ⟨p, -, hv, hvp⟩ := exists_prime_absNorm_eq v
  obtain ⟨q, -, hw, hwq⟩ := exists_prime_absNorm_eq w
  have hpq : p = q := by simp only at hvw; rw [hvp, hwq] at hvw; exact hvw
  ext1
  rw [hv, hw, hpq]

theorem conj_table {a b : ℂ} {t : ℝ} (hb : ‖b‖ = 1) (ht : 0 ≤ t) (h : a ^ 2 = (t : ℂ) * b) :
    a / b = (starRingEnd ℂ) a ∧ b⁻¹ = (starRingEnd ℂ) b ∧ ‖a‖ ^ 2 = t := by
  have hb0 : b ≠ 0 := fun h0 => by simp [h0] at hb
  have hbinv : b⁻¹ = (starRingEnd ℂ) b := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hb]; simp
  have hnorm : ‖a‖ ^ 2 = t := by
    have := congrArg (fun z : ℂ => ‖z‖) h
    simp only [norm_pow, norm_mul, Complex.norm_real, hb, mul_one] at this
    rw [this, Real.norm_eq_abs, abs_of_nonneg ht]
  refine ⟨?_, hbinv, hnorm⟩
  rw [div_eq_mul_inv, hbinv]

  by_cases ha : a = 0
  · simp [ha]
  · have key : a * (a * (starRingEnd ℂ) b) = a * (starRingEnd ℂ) a := by
      rw [← mul_assoc, ← pow_two, h, mul_assoc, Complex.mul_conj, Complex.mul_conj,
        Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, hb, hnorm]
      push_cast; ring
    exact mul_left_cancel₀ ha key

theorem eq_of_meromorphicOn_halfPlane {f g : ℂ → ℂ} {x₀ σ₂ : ℝ}
    (hf : MeromorphicOn f {w : ℂ | x₀ < w.re}) (hg : AnalyticOnNhd ℂ g {w : ℂ | x₀ < w.re})
    (hfg : ∀ w : ℂ, σ₂ < w.re → f w = g w) {z : ℂ} (hz : x₀ < z.re) (hfz : ContinuousAt f z) :
    f z = g z := by
  set U : Set ℂ := {w : ℂ | x₀ < w.re} with hU
  set d : ℂ → ℂ := fun w => f w - g w with hd
  have hdm : MeromorphicOn d U := hf.sub hg.meromorphicOn
  have hUpre : IsPreconnected U := (convex_halfSpace_re_gt x₀).isPreconnected
  set x₁ : ℂ := ((max σ₂ x₀ + 1 : ℝ) : ℂ) with hx₁
  have hx₁re : x₁.re = max σ₂ x₀ + 1 := by simp [hx₁]
  have hx₁U : x₁ ∈ U := by
    show x₀ < x₁.re
    rw [hx₁re]; linarith [le_max_right σ₂ x₀]
  have hx₁top : meromorphicOrderAt d x₁ = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    have hopen : IsOpen {w : ℂ | σ₂ < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have hmem : x₁ ∈ {w : ℂ | σ₂ < w.re} := by
      show σ₂ < x₁.re
      rw [hx₁re]; linarith [le_max_left σ₂ x₀]
    exact eventually_nhdsWithin_of_eventually_nhds
      (Filter.eventually_of_mem (hopen.mem_nhds hmem) fun w hw => by simp only [hd, hfg w hw, sub_self])
  have hztop : meromorphicOrderAt d z = ⊤ := by
    by_contra hne
    exact (hdm.meromorphicOrderAt_ne_top_of_isPreconnected hUpre hz hx₁U hne) hx₁top
  rw [meromorphicOrderAt_eq_top_iff] at hztop
  have hev : ∀ᶠ w in 𝓝[≠] z, f w = g w := hztop.mono fun w hw => sub_eq_zero.mp hw
  have h1 : Tendsto f (𝓝[≠] z) (𝓝 (f z)) := hfz.continuousWithinAt.tendsto
  have h2 : Tendsto g (𝓝[≠] z) (𝓝 (g z)) := (hg z hz).continuousAt.continuousWithinAt.tendsto
  exact tendsto_nhds_unique (h2.congr' (hev.mono fun w hw => hw.symm)) h1 |>.symm

theorem sq_bound_of_table {N : ℕ} (hN : 2 ≤ N) {x : ℝ} (hx0 : 0 ≤ x)
    (hx : x ^ 2 < (N : ℝ) + 2 + ((N : ℝ))⁻¹) : (2 * (x + 1 + 1)) ^ 2 < (N : ℝ) ^ 8 := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hinv : ((N : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have hx3 : x < N + 3 := by
    by_contra hle
    push Not at hle
    nlinarith
  have h1 : 2 * (x + 1 + 1) < 2 * N + 10 := by linarith
  have h2 : (2 * (N : ℝ) + 10) ≤ (N : ℝ) ^ 4 := by
    have hN2 : (4 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    calc (2 * (N : ℝ) + 10) ≤ 8 * N := by linarith
      _ ≤ 4 * (N : ℝ) ^ 2 := by nlinarith
      _ ≤ (N : ℝ) ^ 2 * (N : ℝ) ^ 2 := by nlinarith
      _ = (N : ℝ) ^ 4 := by ring
  have h3 : 0 ≤ 2 * (x + 1 + 1) := by linarith
  calc (2 * (x + 1 + 1)) ^ 2 < (2 * (N : ℝ) + 10) ^ 2 := by
        exact pow_lt_pow_left₀ h1 h3 (by norm_num)
    _ ≤ ((N : ℝ) ^ 4) ^ 2 := by
        exact pow_le_pow_left₀ (by linarith) h2 2
    _ = (N : ℝ) ^ 8 := by ring

theorem norm_coeff_le {N : ℕ} {C e : ℝ} (hC0 : 0 ≤ C) (hC : C ^ 2 < (N : ℝ) ^ 8) (k : ℕ)
    (he0 : 0 ≤ e) (he : e ≤ C ^ (2 * k)) : ‖(e : ℂ)‖ ≤ (((N : ℝ) ^ k) ^ (8 : ℝ)) := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg he0]
  calc e ≤ C ^ (2 * k) := he
    _ = (C ^ 2) ^ k := by rw [pow_mul]
    _ ≤ ((N : ℝ) ^ 8) ^ k := pow_le_pow_left₀ (sq_nonneg C) hC.le k
    _ = ((N : ℝ) ^ k) ^ (8 : ℕ) := by ring
    _ = ((N : ℝ) ^ k) ^ (8 : ℝ) := by rw [← Real.rpow_natCast]; norm_num

theorem radius_bound {N : ℕ} (hN : 2 ≤ N) {C : ℝ} (hC0 : 0 ≤ C) (hC : (2 * C) ^ 2 < (N : ℝ) ^ 8)
    {s : ℂ} (hs : 9 < s.re) : ‖((N : ℕ) : ℂ) ^ (-s)‖ * C ^ 2 < 1 := by
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) < N := by linarith
  rw [Complex.norm_natCast_cpow_of_pos hNpos, Complex.neg_re]
  have hC' : C ^ 2 < (N : ℝ) ^ 8 := by nlinarith
  have h1 : (N : ℝ) ^ (-s.re) ≤ (N : ℝ) ^ (-(9 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hN1.le (by linarith)
  have h2 : (N : ℝ) ^ (-(9 : ℝ)) = ((N : ℝ) ^ (9 : ℕ))⁻¹ := by
    rw [Real.rpow_neg (by linarith)]; norm_num
  have h9pos : 0 < (N : ℝ) ^ 9 := by positivity
  calc (N : ℝ) ^ (-s.re) * C ^ 2 ≤ ((N : ℝ) ^ 9)⁻¹ * C ^ 2 := by
        rw [← h2]; exact mul_le_mul_of_nonneg_right h1 (sq_nonneg C)
    _ ≤ ((N : ℝ) ^ 9)⁻¹ * (N : ℝ) ^ 8 := by
        exact mul_le_mul_of_nonneg_left hC'.le (inv_nonneg.mpr h9pos.le)
    _ = ((N : ℝ))⁻¹ := by
        rw [show ((N : ℝ)) ^ 9 = (N : ℝ) ^ 8 * (N : ℝ) by ring, mul_inv_rev, mul_assoc,
          inv_mul_cancel₀ (by positivity), mul_one]
    _ < 1 := inv_lt_one_of_one_lt₀ hN1

theorem main (Φ : HeckeEigensystem ℚ ℂ)
    (hΦ : IsArithGenuineCuspRealizable ℚ (productionPinsGeneral ℚ) Φ)
    (SQ₀ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hb : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ₀ → ‖Φ.b p‖ = 1) :
    ∀ σ : ℝ, 1 < σ →
      Summable fun p : HeightOneSpectrum (𝓞 ℚ) => ‖Φ.a p‖ ^ 2 * (Ideal.absNorm p.asIdeal : ℝ) ^ (-σ) := by

  obtain ⟨S, σ₀, Λ, ⟨a, ha, hmero⟩, -, hreal, hprod, -⟩ :=
    AutomorphicForm.exists_finset_lt_one_meromorphicOn_analyticAt_hasProd_rsEulerPoly_self_and_eval_inv_absNorm_ne_zero
      ℚ (1 / 2) 1 (1 / 2) 2 (classRepTranslates ℚ) (by norm_num) (by norm_num) (by norm_num)
      AutomorphicForm.SiegelCovering.coversModCentre_productionPinsGeneral_D_rat Φ hΦ
  have hprod' : ∀ s : ℂ, σ₀ < s.re →
      HasProd (fun v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S} => (locEval Φ v.1 s)⁻¹) (Λ s) := hprod

  obtain ⟨S', hS'⟩ :=
    LanglandsTunnell.Converse.exists_finset_sq_eq_real_mul_b_and_norm_sq_lt_of_isArithGenuineCuspRealizable
      Φ hΦ
  set T : Finset (HeightOneSpectrum (𝓞 ℚ)) := S ∪ S' ∪ SQ₀ with hT
  have hST : S ⊆ T := Finset.subset_union_left.trans Finset.subset_union_left
  have good : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ T →
      Φ.a v / Φ.b v = (starRingEnd ℂ) (Φ.a v) ∧ (Φ.b v)⁻¹ = (starRingEnd ℂ) (Φ.b v) ∧
      ‖Φ.b v‖ = 1 ∧
      ‖Φ.a v‖ ^ 2 < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) + 2 + (((Ideal.absNorm v.asIdeal : ℕ) : ℝ))⁻¹ := by
    intro v hv
    have hvS' : v ∉ S' := fun h => hv (by simp [hT, h])
    have hvQ : v ∉ SQ₀ := fun h => hv (by simp [hT, h])
    obtain ⟨⟨t, ht, hat⟩, hlt⟩ := hS' v hvS'
    obtain ⟨h1, h2, -⟩ := conj_table (hb v hvQ) ht hat
    refine ⟨h1, h2, hb v hvQ, ?_⟩
    rw [hb v hvQ, one_mul] at hlt
    exact hlt

  have hσv : ∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ σv : ℝ, ∀ s : ℂ, σv < s.re → locEval Φ v s ≠ 0 :=
    fun v => exists_forall_eval_cpow_neg_ne_zero (locPoly Φ v) (rsEulerPoly_coeff_zero _ _ _ _ _)
      (Ideal.absNorm v.asIdeal) (two_le_absNorm v)
  choose σv hσv using hσv
  set σ₁ : ℝ := max σ₀ 0 + ∑ v ∈ T \ S, max (σv v) 0 with hσ₁
  have hσ₁₀ : σ₀ ≤ σ₁ := by
    have : 0 ≤ ∑ v ∈ T \ S, max (σv v) 0 := Finset.sum_nonneg fun v _ => le_max_right _ _
    rw [hσ₁]; linarith [le_max_left σ₀ 0]
  have hσ₁v : ∀ v ∈ T \ S, σv v ≤ σ₁ := by
    intro v hv
    have h1 : max (σv v) 0 ≤ ∑ w ∈ T \ S, max (σv w) 0 :=
      Finset.single_le_sum (f := fun w => max (σv w) 0) (fun w _ => le_max_right _ _) hv
    rw [hσ₁]; linarith [le_max_left (σv v) 0, le_max_right σ₀ 0]
  set Q : ℂ → ℂ := fun s => ∏ v ∈ T \ S, locEval Φ v s with hQ
  have hQdiff : Differentiable ℂ Q := by
    rw [hQ]; exact Differentiable.fun_finsetProd fun v _ => differentiable_locEval Φ v
  set Λ₁ : ℂ → ℂ := fun s => Λ s * Q s with hΛ₁
  have hmero₁ : MeromorphicOn Λ₁ {s : ℂ | a < s.re} := fun x hx =>
    (hmero x hx).mul (hQdiff.analyticAt x).meromorphicAt
  have hreal₁ : ∀ σ : ℝ, 1 < σ → AnalyticAt ℂ Λ₁ (σ : ℂ) := fun σ hσ =>
    (hreal σ hσ).mul (hQdiff.analyticAt _)
  have hprod₁ : ∀ s : ℂ, σ₁ < s.re →
      HasProd (fun v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ T} => (locEval Φ v.1 s)⁻¹) (Λ₁ s) := by
    intro s hs
    have hs₀ : σ₀ < s.re := lt_of_le_of_lt hσ₁₀ hs
    have hne : ∀ v ∈ T \ S, (locEval Φ v s)⁻¹ ≠ 0 := fun v hv =>
      inv_ne_zero (hσv v s (lt_of_le_of_lt (hσ₁v v hv) hs))
    have key := hasProd_subtype_notMem_of_subset (fun v => (locEval Φ v s)⁻¹) hST (hprod' s hs₀) hne
    simp only [inv_inv] at key
    exact key

  choose e he0 he1 hepos hebd hesum using fun v : HeightOneSpectrum (𝓞 ℚ) =>
    LanglandsTunnell.RankinSelberg.exists_nonneg_hasSum_mul_pow_inv_eval_rsEulerPoly_conj_self (Φ.a v) (Φ.b v)
  set E : HeightOneSpectrum (𝓞 ℚ) → ℕ → ℂ := fun v k =>
    if v ∈ T then (if k = 0 then 1 else 0) else ((e v k : ℝ) : ℂ) with hE
  have hE0 : ∀ v, E v 0 = 1 := by
    intro v
    by_cases hv : v ∈ T
    · simp [hE, hv]
    · simp [hE, hv, he0 v]
  have hEpos : ∀ v k, 0 ≤ E v k := by
    intro v k
    by_cases hv : v ∈ T
    · by_cases hk : k = 0
      · simp only [hE, if_pos hv, if_pos hk]; exact zero_le_one
      · simp only [hE, if_pos hv, if_neg hk]; exact le_rfl
    · simp only [hE, if_neg hv]; exact Complex.zero_le_real.mpr (hepos v k)
  have hEA : ∀ v k, ‖E v k‖ ≤ ((((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ k) ^ (8 : ℝ)) := by
    intro v k
    have hone : (1 : ℝ) ≤ ((((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ k) ^ (8 : ℝ)) := by
      apply Real.one_le_rpow _ (by norm_num)
      exact one_le_pow₀ (by exact_mod_cast (le_trans (by norm_num) (two_le_absNorm v)))
    by_cases hv : v ∈ T
    · by_cases hk : k = 0
      · simp only [hE, if_pos hv, if_pos hk, norm_one]; exact hone
      · simp only [hE, if_pos hv, if_neg hk, norm_zero]; linarith
    · simp only [hE, if_neg hv]
      obtain ⟨-, -, hb1, hlt⟩ := good v hv
      have hC := sq_bound_of_table (two_le_absNorm v) (norm_nonneg (Φ.a v)) hlt
      refine norm_coeff_le (by positivity) hC k (hepos v k) ?_
      have := hebd v k
      rw [hb1] at this
      exact this

  obtain ⟨c, hcE, hcpos, habs, heul⟩ :=
    LSeries.exists_hasProd_tsum_eq_lseries_of_norm_le_pow
      (fun v : HeightOneSpectrum (𝓞 ℚ) => Ideal.absNorm v.asIdeal) absNorm_prime absNorm_injective E hE0 8 hEA
  have hc0 : 0 ≤ c := hcpos hEpos
  set σ₂ : ℝ := max σ₁ 9 with hσ₂
  have hmatch : ∀ s : ℂ, σ₂ < s.re → Λ₁ s = LSeries c s := by
    intro s hs
    have hs₁ : σ₁ < s.re := lt_of_le_of_lt (le_max_left _ _) hs
    have hs9 : (9 : ℝ) < s.re := lt_of_le_of_lt (le_max_right _ _) hs
    have hs9' : (8 : ℝ) + 1 < s.re := by norm_num; exact hs9
    have hP := hprod₁ s hs₁
    have hEs := heul s hs9'
    have hind : (fun v : HeightOneSpectrum (𝓞 ℚ) =>
          ∑' k : ℕ, E v k * ((((Ideal.absNorm v.asIdeal : ℕ) : ℕ) : ℂ) ^ (-s)) ^ k) =
        ({v | v ∉ T} : Set (HeightOneSpectrum (𝓞 ℚ))).mulIndicator (fun v => (locEval Φ v s)⁻¹) := by
      funext v
      by_cases hv : v ∈ T
      · rw [Set.mulIndicator_of_notMem (show v ∉ ({v | v ∉ T} : Set _) from fun h => h hv)]
        rw [tsum_eq_single 0 (fun k hk => by simp [hE, hv, hk])]
        simp [hE, hv]
      · rw [Set.mulIndicator_of_mem (show v ∈ ({v | v ∉ T} : Set _) from hv)]
        obtain ⟨h1, h2, hb1, hlt⟩ := good v hv
        have hC := sq_bound_of_table (two_le_absNorm v) (norm_nonneg (Φ.a v)) hlt
        have hy : ‖(((Ideal.absNorm v.asIdeal : ℕ) : ℂ)) ^ (-s)‖ * (‖Φ.a v‖ + ‖Φ.b v‖ + 1) ^ 2 < 1 := by
          rw [hb1]
          exact radius_bound (two_le_absNorm v) (by positivity) hC hs9
        have hloc := (hesum v _ hy).tsum_eq
        simp only [hE, if_neg hv]
        rw [hloc, ← h1, ← h2]
    rw [hind] at hEs
    have hEs' := (hasProd_subtype_iff_mulIndicator (s := ({v | v ∉ T} : Set (HeightOneSpectrum (𝓞 ℚ))))
      (f := fun v => (locEval Φ v s)⁻¹)).mpr hEs
    exact hP.unique hEs'

  have habs1 : LSeries.abscissaOfAbsConv c ≤ 1 := by
    by_contra hgt
    push Not at hgt
    have hne_top : LSeries.abscissaOfAbsConv c ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) habs
    have hne_bot : LSeries.abscissaOfAbsConv c ≠ ⊥ := by
      intro h; rw [h] at hgt; exact absurd hgt (not_lt.mpr bot_le)
    obtain ⟨x₀, hx₀⟩ : ∃ x₀ : ℝ, (x₀ : EReal) = LSeries.abscissaOfAbsConv c :=
      ⟨_, EReal.coe_toReal hne_top hne_bot⟩
    have hx₀1 : 1 < x₀ := by
      rw [← hx₀] at hgt
      exact_mod_cast hgt
    obtain ⟨r, hr, hball⟩ := (hreal₁ x₀ hx₀1).exists_ball_analyticOnNhd
    have hmeroV : MeromorphicOn Λ₁ {w : ℂ | x₀ < w.re} := fun w hw =>
      hmero₁ w (show a < w.re by simp only [Set.mem_setOf_eq] at hw; linarith)
    have hgV : AnalyticOnNhd ℂ (LSeries c) {w : ℂ | x₀ < w.re} := fun w hw =>
      LSeries_analyticOnNhd c w (by simp only [Set.mem_setOf_eq] at hw ⊢; rw [← hx₀]; exact_mod_cast hw)
    have hid : ∀ z ∈ Metric.ball (x₀ : ℂ) r, x₀ < z.re → Λ₁ z = LSeries c z := fun z hz hzre =>
      eq_of_meromorphicOn_halfPlane hmeroV hgV hmatch hzre (hball z hz).continuousAt
    have hlt := LSeries.abscissaOfAbsConv_lt_of_differentiableOn_ball hc0 (x := x₀) hx₀.symm.le hr
      hball.differentiableOn hid
    rw [← hx₀] at hlt
    exact lt_irrefl _ hlt

  intro σ hσ
  have hσabs : LSeries.abscissaOfAbsConv c < ((σ : ℂ)).re := by
    rw [Complex.ofReal_re]
    exact lt_of_le_of_lt habs1 (by exact_mod_cast hσ)
  have hsum : LSeriesSummable c σ := LSeriesSummable_of_abscissaOfAbsConv_lt_re hσabs
  have hsumn : Summable fun n : ℕ => ‖LSeries.term c σ n‖ := summable_norm_iff.mpr hsum
  have hcomp : Summable fun v : HeightOneSpectrum (𝓞 ℚ) => ‖LSeries.term c σ (Ideal.absNorm v.asIdeal)‖ :=
    hsumn.comp_injective absNorm_injective
  rw [← Finset.summable_compl_iff T]
  have hsub := hcomp.subtype {v | v ∉ T}
  refine hsub.congr ?_
  rintro ⟨v, hv⟩
  have hv' : v ∉ T := hv
  have hn0 : Ideal.absNorm v.asIdeal ≠ 0 := absNorm_ne_zero v
  have hnpos : 0 < Ideal.absNorm v.asIdeal := Nat.pos_of_ne_zero hn0
  have hcv : c (Ideal.absNorm v.asIdeal) = ((‖Φ.a v‖ ^ 2 : ℝ) : ℂ) := by
    have := hcE v 1
    rw [pow_one] at this
    rw [this]
    simp only [hE, if_neg hv', he1 v]
  simp only [Function.comp_apply, LSeries.term_of_ne_zero hn0, norm_div, hcv, Complex.norm_real,
    Complex.norm_natCast_cpow_of_pos hnpos, Complex.ofReal_re, Real.norm_eq_abs]
  rw [abs_of_nonneg (sq_nonneg _), Real.rpow_neg (Nat.cast_nonneg _), div_eq_mul_inv]

end RS11

theorem solution
    (Φ : AutomorphicForm.HeckeEigensystem ℚ ℂ)
    (hΦ : AutomorphicForm.IsArithGenuineCuspRealizable ℚ (AutomorphicForm.productionPinsGeneral ℚ) Φ)
    (SQ₀ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hb : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ₀ → ‖Φ.b p‖ = 1) :
    ∀ σ : ℝ, 1 < σ →
      Summable fun p : HeightOneSpectrum (𝓞 ℚ) => ‖Φ.a p‖ ^ 2 * (Ideal.absNorm p.asIdeal : ℝ) ^ (-σ) :=
  RS11.main Φ hΦ SQ₀ hb

end
end S_AutomorphicForm_summable_norm_a_sq_mul_rpow_absNorm_of_isArithGenuineCuspRealizable
end P2MW
export P2MW.S_AutomorphicForm_summable_norm_a_sq_mul_rpow_absNorm_of_isArithGenuineCuspRealizable (solution)
