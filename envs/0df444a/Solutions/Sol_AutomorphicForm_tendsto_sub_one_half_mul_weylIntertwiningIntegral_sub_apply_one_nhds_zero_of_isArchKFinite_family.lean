-- Prove2me | solution 1 for AutomorphicForm.tendsto_sub_one_half_mul_weylIntertwiningIntegral_sub_apply_one_nhds_zero_of_isArchKFinite_family
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/7c0662ba-a601-5d5b-96fc-daa1cedf7a7f

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.ReImTopology
import Theorems.Thm_AutomorphicForm_tendsto_sub_one_half_mul_weylIntertwiningIntegral_sub_apply_one_nhds_zero_of_mem_maximalCompact
import Theorems.Thm_AutomorphicForm_isInducedSection_etaFst_etaSnd_neg_weylIntertwiningIntegral
import Theorems.Thm_AutomorphicForm_exists_mem_adelicBorel_mul_eq
import Theorems.Thm_AutomorphicForm_exists_meromorphicOn_partialEulerProduct_mul_weylIntertwiningIntegral_eq_mul
import Theorems.Thm_NumberField_multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one
import Theorems.Thm_NumberField_hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta
import Theorems.Thm_NumberField_exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero
import Theorems.Thm_NumberField_dedekindZeta_ne_zero_of_one_lt_re
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_tendsto_sub_one_half_mul_weylIntertwiningIntegral_sub_apply_one_nhds_zero_of_isArchKFinite_family
p2m_attr_erase "instance" "AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions instCountableOfNumberField_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem"
p2m_attr_erase "instance" "Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add LocalGL2.swapUnit_val AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply SemialgHom.baseChange_of_algebraMap_tmul_left"
p2m_attr_erase "simp" "SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν"
p2m_attr_erase "simp" "AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply"
p2m_attr_erase "simp" "RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel Filter Topology
open scoped NNReal

namespace ConstFromConstK

theorem hasProd_of_hasProd_inv {ι : Type*} (f : ι → ℂ) {a : ℂ} (ha : a ≠ 0)
    (h : HasProd (fun i => (f i)⁻¹) a) : HasProd f a⁻¹ := by
  unfold HasProd at h ⊢
  have h' := h.inv₀ ha
  refine h'.congr (fun T => ?_)
  simp [Finset.prod_inv_distrib]

end ConstFromConstK

open ConstFromConstK

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
      (_hφhol : ∀ g, Differentiable ℂ (fun s => φ s g)),
    letI := NumberField.AdelicHaar.adeleBorel (𝓞 F) F
    ∀ g : AdelicGL2 (𝓞 F) F,
      Tendsto (fun s : ℂ => (s - 1 / 2) *
          (weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) g
            - weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) 1))
        (𝓝[{s : ℂ | 1 / 2 < s.re}] (1 / 2 : ℂ)) (𝓝 0) := by
  intro α hα φ hφ hφK hφf hφjc hφhol
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := NumberField.AdelicHaar.adeleBorel (𝓞 F) F

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
    exact (hasProd_of_hasProd_inv _ hne hcompl).tprod_eq

  obtain ⟨T, ϖ₁, hϖ₁, R, hRmero, hRdiff, hRid⟩ :=
    AutomorphicForm.exists_meromorphicOn_partialEulerProduct_mul_weylIntertwiningIntegral_eq_mul
      F hα 1 1 h1u h1u φ hφ hφK hφf hφjc hφhol 1
  have hloc : ∀ (v : HeightOneSpectrum (𝓞 F)) (u : (v.adicCompletion F)ˣ),
      ((NumberField.TateGlobal.localChar (1 * 1⁻¹ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) v u : ℂˣ) : ℂ) = 1 := by
    intro v u
    simp [NumberField.TateGlobal.localChar]
  simp only [hloc, one_mul] at hRid
  have hRan : ∀ x : ℂ, 0 < x.re → AnalyticAt ℂ R x := fun x hx => hRdiff.analyticAt (hO0.mem_nhds hx)
  have hM1 : ∀ s : ℂ, 1 / 2 < s.re →
      weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) 1 =
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
      J s = (s - 1 / 2) * weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) 1 := by
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
  set κ : ℂ := J (1 / 2) with hκ
  have hT1lim : Tendsto (fun s : ℂ => (s - 1 / 2) *
      weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) 1)
      (𝓝[{s : ℂ | 1 / 2 < s.re}] (1 / 2 : ℂ)) (𝓝 κ) :=
    (hJan.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
      (eventually_nhdsWithin_of_forall (fun s hs => hJeq s hs))

  have hK :=
    AutomorphicForm.tendsto_sub_one_half_mul_weylIntertwiningIntegral_sub_apply_one_nhds_zero_of_mem_maximalCompact
      F hα φ hφ hφK hφf hφjc hφhol
  have hTR : ∀ s : ℂ, IsInducedSection (𝓞 F) F (etaFst 1 α hα (-s)) (etaSnd 1 α hα (-s))
      (weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s)) := fun s =>
    AutomorphicForm.isInducedSection_etaFst_etaSnd_neg_weylIntertwiningIntegral F hα 1 1 s (φ s) (hφ s)

  intro g
  obtain ⟨b, k, hb, hkf, hka, rfl⟩ := AutomorphicForm.exists_mem_adelicBorel_mul_eq F g

  let f : ℂ → ℂ := fun s =>
    ((etaFst 1 α hα (-s) (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ)
      * ((etaSnd 1 α hα (-s) (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ)
  have hfb : ∀ s : ℂ, weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) (b * k)
      = f s * weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) k := by
    intro s
    exact hTR s b hb k
  set A₁ : ℝ := ((α (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℝˣ) : ℝ) with hA₁
  set A₂ : ℝ := ((α (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℝˣ) : ℝ) with hA₂
  have hA₁pos : 0 < A₁ := hα _
  have hA₂pos : 0 < A₂ := hα _
  have hfeq : ∀ s : ℂ, f s = ((A₁ : ℂ)) ^ (-s + 1 / 2) * ((A₂ : ℂ)) ^ (-(-s + 1 / 2)) := by
    intro s
    simp only [f, etaFst_apply, etaSnd_apply, MonoidHom.one_apply, one_mul,
      cpowChar_apply_val, hA₁, hA₂]
  have hfcont : Continuous f := by
    have : f = fun s : ℂ => ((A₁ : ℂ)) ^ (-s + 1 / 2) * ((A₂ : ℂ)) ^ (-(-s + 1 / 2)) := funext hfeq
    rw [this]
    refine Continuous.mul ?_ ?_
    · exact Continuous.const_cpow (by fun_prop) (Or.inl (Complex.ofReal_ne_zero.mpr hA₁pos.ne'))
    · exact Continuous.const_cpow (by fun_prop) (Or.inl (Complex.ofReal_ne_zero.mpr hA₂pos.ne'))
  have hf12 : f (1 / 2) = 1 := by
    rw [hfeq]
    have e : (-(1 / 2 : ℂ) + 1 / 2) = 0 := by ring
    rw [e, neg_zero, Complex.cpow_zero, Complex.cpow_zero, one_mul]
  have hTf : Tendsto f (𝓝[{s : ℂ | 1 / 2 < s.re}] (1 / 2 : ℂ)) (𝓝 1) := by
    have := (hfcont.tendsto (1 / 2 : ℂ)).mono_left (nhdsWithin_le_nhds (s := {s : ℂ | 1 / 2 < s.re}))
    rwa [hf12] at this

  have hlim1 := hTf.mul (hK k hkf hka)
  have hlim2 := (hTf.sub_const 1).mul hT1lim
  rw [mul_zero] at hlim1
  rw [sub_self, zero_mul] at hlim2
  have hsum := hlim1.add hlim2
  rw [add_zero] at hsum
  refine hsum.congr (fun s => ?_)
  rw [hfb s]
  ring

end S_AutomorphicForm_tendsto_sub_one_half_mul_weylIntertwiningIntegral_sub_apply_one_nhds_zero_of_isArchKFinite_family
end P2MW
export P2MW.S_AutomorphicForm_tendsto_sub_one_half_mul_weylIntertwiningIntegral_sub_apply_one_nhds_zero_of_isArchKFinite_family (solution)
