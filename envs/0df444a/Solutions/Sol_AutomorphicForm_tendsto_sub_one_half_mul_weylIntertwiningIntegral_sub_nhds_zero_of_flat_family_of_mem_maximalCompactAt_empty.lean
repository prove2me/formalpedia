-- Prove2me | solution 1 for AutomorphicForm.tendsto_sub_one_half_mul_weylIntertwiningIntegral_sub_nhds_zero_of_flat_family_of_mem_maximalCompactAt_empty
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/22c83fbc-5318-5e64-9d0c-7d2bc3b104f7

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
import Theorems.Thm_AutomorphicForm_exists_eq_mul_archSupportedAt_of_mem_maximalCompactAt_empty
import Theorems.Thm_AutomorphicForm_tendsto_sub_one_half_mul_weylIntertwiningIntegral_sub_nhds_zero_of_flat_family_of_archSupportedAt
import Theorems.Thm_AutomorphicForm_flat_family_comp_mul_of_mem_adelicMaximalCompact
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_tendsto_sub_one_half_mul_weylIntertwiningIntegral_sub_nhds_zero_of_flat_family_of_mem_maximalCompactAt_empty
p2m_attr_erase "instance" "NumberField.AdelicCentre.locallyCompactSpace_adelicPGL2 NumberField.AdelicCentre.isTopologicalGroup_adelicPGL2 NumberField.AdelicCentre.t2Space_adelicPGL2 NumberField.AdelicCentre.isClosed_center instCountableOfNumberField_definitions HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass"
p2m_attr_erase "instance" "instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add LocalGL2.swapUnit_val NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply"
p2m_attr_erase "simp" "Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ"
p2m_attr_erase "simp" "AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport"
p2m_attr_erase "simp" "RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel Filter Topology
open scoped NNReal

namespace A6Kit

variable {F : Type} [Field F] [NumberField F]

omit [NumberField F] in

private theorem glInfinite_ext {g h : GL (Fin 2) (InfiniteAdeleRing F)}
    (H : ∀ w : InfinitePlace F, archComponent F w g = archComponent F w h) : g = h := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  funext w
  have := congrArg (fun m : GL (Fin 2) w.Completion => (m : Matrix (Fin 2) (Fin 2) w.Completion) i j) (H w)
  simpa [archComponent_apply] using this

private theorem adelicGL2_ext {g h : AdelicGL2 (𝓞 F) F}
    (h₁ : glArch (𝓞 F) F g = glArch (𝓞 F) F h)
    (h₂ : ∀ v : HeightOneSpectrum (𝓞 F),
      finComponent (𝓞 F) F v (glFin (𝓞 F) F g) = finComponent (𝓞 F) F v (glFin (𝓞 F) F h)) :
    g = h := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  apply Prod.ext
  · have := congrArg (fun m : GL (Fin 2) (InfiniteAdeleRing F) =>
      (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j) h₁
    simpa [glArch_apply] using this
  · apply Subtype.ext
    funext v
    have := congrArg (fun m : GL (Fin 2) (v.adicCompletion F) =>
      (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j) (h₂ v)
    simp [finComponent_apply, glFin_apply] at this
    exact this

private theorem eq_one_of_forall_archComponent_eq_one {k : AdelicGL2 (𝓞 F) F} (hk : k ∈ maximalCompactAt F ∅)
    (h : ∀ w : InfinitePlace F, archComponent F w (glArch (𝓞 F) F k) = 1) : k = 1 := by
  rw [mem_maximalCompactAt_iff] at hk
  refine adelicGL2_ext ?_ (fun v => ?_)
  · rw [map_one]
    exact glInfinite_ext fun w => by rw [h w, map_one]
  · rw [map_one, map_one]
    exact hk.2 v (Finset.notMem_empty v)

end A6Kit

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
      (kinf : AdelicGL2 (𝓞 F) F) (_hkinf : kinf ∈ maximalCompactAt F ∅),
    letI := NumberField.AdelicHaar.adeleBorel (𝓞 F) F
    Tendsto (fun s : ℂ => (s - 1 / 2) *
        (weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) kinf
          - weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) 1))
      (𝓝[{s : ℂ | 1 / 2 < s.re}] (1 / 2 : ℂ)) (𝓝 0) := by
  intro α hα φ hφ hφK hφf hφjc hφhol hφflat kinf hkinf
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := NumberField.AdelicHaar.adeleBorel (𝓞 F) F
  classical

  let supp : AdelicGL2 (𝓞 F) F → Finset (InfinitePlace F) :=
    fun k => Finset.univ.filter (fun w => archComponent F w (glArch (𝓞 F) F k) ≠ 1)

  suffices hmain : ∀ (N : ℕ) (k : AdelicGL2 (𝓞 F) F), k ∈ maximalCompactAt F ∅ → (supp k).card ≤ N →
      Tendsto (fun s : ℂ => (s - 1 / 2) *
          (weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) k
            - weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) 1))
        (𝓝[{s : ℂ | 1 / 2 < s.re}] (1 / 2 : ℂ)) (𝓝 0) from
    hmain _ kinf hkinf le_rfl
  intro N
  induction N with
  | zero =>
    intro k hk hcard
    have hsupp : supp k = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hcard)
    have hall : ∀ w : InfinitePlace F, archComponent F w (glArch (𝓞 F) F k) = 1 := by
      intro w
      by_contra hw
      have : w ∈ supp k := Finset.mem_filter.2 ⟨Finset.mem_univ w, hw⟩
      rw [hsupp] at this
      exact Finset.notMem_empty w this
    have hk1 : k = 1 := A6Kit.eq_one_of_forall_archComponent_eq_one hk hall
    subst hk1
    refine (tendsto_const_nhds (x := (0 : ℂ))).congr' (Eventually.of_forall fun s => ?_)
    simp only [sub_self, mul_zero]
  | succ N ih =>
    intro k hk hcard

    by_cases hsmall : (supp k).card ≤ N
    · exact ih k hk hsmall
    have hne : (supp k).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h0
      rw [h0, Finset.card_empty] at hsmall
      exact hsmall (Nat.zero_le N)
    obtain ⟨w, hw⟩ := hne
    obtain ⟨k₁, k₂, hk12, -, hk1f, hk1a, -, hk1iso, hk2, hk2w⟩ :=
      AutomorphicForm.exists_eq_mul_archSupportedAt_of_mem_maximalCompactAt_empty F k hk w

    have hsupp2 : supp k₂ ⊆ (supp k).erase w := by
      intro w' hw'
      have hw'2 : archComponent F w' (glArch (𝓞 F) F k₂) ≠ 1 := (Finset.mem_filter.1 hw').2
      have hne' : w' ≠ w := fun h => hw'2 (h ▸ hk2w)
      refine Finset.mem_erase.2 ⟨hne', Finset.mem_filter.2 ⟨Finset.mem_univ w', ?_⟩⟩
      rw [hk12, map_mul, map_mul, hk1a w' hne', one_mul]
      exact hw'2
    have hcard2 : (supp k₂).card ≤ N := by
      have h1 := Finset.card_le_card hsupp2
      rw [Finset.card_erase_of_mem hw] at h1
      omega
    have ih2 := ih k₂ hk2 hcard2

    have hk2K : k₂ ∈ adelicMaximalCompact F := maximalCompactAt_le F ∅ hk2
    obtain ⟨hψ, hψK, hψf, hψjc, hψhol, hψflat⟩ :=
      AutomorphicForm.flat_family_comp_mul_of_mem_adelicMaximalCompact F hα φ hφ hφK hφf hφjc hφhol hφflat k₂ hk2K

    have hA5 := AutomorphicForm.tendsto_sub_one_half_mul_weylIntertwiningIntegral_sub_nhds_zero_of_flat_family_of_archSupportedAt
      F hα (fun s h => φ s (h * k₂)) hψ hψK hψf hψjc hψhol hψflat w k₁ hk1f hk1a (hk1iso w)

    have hMk : ∀ s, weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (fun h => φ s (h * k₂)) k₁
        = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) k := by
      intro s
      simp only [weylIntertwiningIntegral, hk12, mul_assoc]
    have hM1 : ∀ s, weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (fun h => φ s (h * k₂)) 1
        = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) k₂ := by
      intro s
      simp only [weylIntertwiningIntegral, mul_one]
    have hsum := hA5.add ih2
    rw [add_zero] at hsum
    refine hsum.congr fun s => ?_
    rw [hMk, hM1]
    ring

end S_AutomorphicForm_tendsto_sub_one_half_mul_weylIntertwiningIntegral_sub_nhds_zero_of_flat_family_of_mem_maximalCompactAt_empty
end P2MW
export P2MW.S_AutomorphicForm_tendsto_sub_one_half_mul_weylIntertwiningIntegral_sub_nhds_zero_of_flat_family_of_mem_maximalCompactAt_empty (solution)
