-- Prove2me | solution 1 for CerednikDrinfeld.QM.IsFineModuli.isClosed_setOf_exists_smul_latt_eq_qmPeriodLattice_of_isProper_of_analytic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/52045e7b-f2fb-589b-98a5-0a233a7ece15

import Mathlib
import Theorems.Thm_AlgebraicGeometry_exists_tendsto_forall_eq_of_injOn_of_differentiableOn_appLE_of_tendsto_appLE
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Theorems.Thm_CerednikDrinfeld_QM_IsFineModuli_exists_isOpen_injOn_periodChart_of_analytic_of_isEichlerOrder
import Theorems.Thm_AlgebraicGeometry_exists_tendsto_appLE_of_isProper_of_smoothOfRelativeDimension_one_complex
import Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_exists_fuchsianGroup_smul_eq_of_smul_eq_qmPeriodLattice_of_forall_mem_imp_mem
import Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_exists_smul_eq_qmPeriodLattice_smul_and_forall_mem_imp_mem_of_mem_fuchsianGroup
import Theorems.Thm_UpperHalfPlane_eventually_nhdsNE_not_exists_smul_eq_of_discreteTopology_of_det_eq_one
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_submodule_forall_mem_iff_factorsThrough_lev_of_pointEquiv
import Theorems.Thm_CerednikDrinfeld_fuchsianGroup_discrete_neg_mem_and_exists_isCompact
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_IsFineModuli_isClosed_setOf_exists_smul_latt_eq_qmPeriodLattice_of_isProper_of_analytic
p2m_attr_erase "instance" "PresheafOfModules.ExteriorPower.instModulePresheafAb TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions GoodReductionJacobian.RelativeGroupLaw.isIso_endKerStr_schemeHomOverId AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.Scheme.Modules.exteriorPower_obj RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe"
p2m_attr_erase "simp" "NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst LocalGL2.swapUnit_val QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul NeronModelInfra.schemeHomOverNpow_succ NeronModelInfra.schemeHomOverNpow_zero AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false

p2m_open "CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve~H1 QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM"
open scoped Quaternion TensorProduct NumberField MatrixGroups Topology Pointwise
open Filter

theorem P2mWs2.exists_smul_eq_of_tendsto_of_forall_exists_smul_eq
    (Γ : Subgroup (GL (Fin 2) ℝ))
    (hdisc : ∀ τ τ' : UpperHalfPlane, ∀ᶠ z in 𝓝[≠] τ, ¬ ∃ γ ∈ Γ, γ • τ' = z)
    (hdet : ∀ γ ∈ Γ, Matrix.GeneralLinearGroup.det γ = 1)
    (x y : ℕ → UpperHalfPlane) (τ τs : UpperHalfPlane)
    (hx : Tendsto x atTop (𝓝 τ)) (hy : Tendsto y atTop (𝓝 τs))
    (hγ : ∀ n, ∃ γ ∈ Γ, γ • y n = x n) : ∃ γ ∈ Γ, γ • τs = τ := by
  classical
  choose γ hγΓ hγe using hγ

  have hlift : ∀ g ∈ Γ, ∃ s : Matrix.SpecialLinearGroup (Fin 2) ℝ, ∀ z : UpperHalfPlane, s • z = g • z := by
    intro g hg
    have hd : ((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
      have := congrArg Units.val (hdet g hg); simpa using this
    refine ⟨⟨(g : Matrix (Fin 2) (Fin 2) ℝ), hd⟩, fun z => ?_⟩
    rw [MulAction.compHom_smul_def]
    congr 1
    first
      | exact Units.ext rfl
      | (apply Units.ext; ext i j; simp [Matrix.SpecialLinearGroup.mapGL])

  set z : ℕ → UpperHalfPlane := fun n => (γ n)⁻¹ • τ with hz
  have hzy : Tendsto (fun n => dist (z n) (y n)) atTop (𝓝 0) := by
    have h1 : ∀ n, dist (z n) (y n) = dist τ (x n) := by
      intro n
      obtain ⟨s, hs⟩ := hlift (γ n)⁻¹ (Γ.inv_mem (hγΓ n))
      have hy' : y n = (γ n)⁻¹ • x n := by rw [← hγe n, inv_smul_smul]
      rw [hz, hy']
      show dist ((γ n)⁻¹ • τ) ((γ n)⁻¹ • x n) = dist τ (x n)
      rw [← hs τ, ← hs (x n), dist_smul]
    simp only [h1]
    have := (tendsto_const_nhds (x := τ)).dist hx
    rwa [dist_self] at this
  have hzlim : Tendsto z atTop (𝓝 τs) := by
    rw [Metric.tendsto_atTop] at hy ⊢
    intro ε hε
    obtain ⟨N₁, hN₁⟩ := hy (ε / 2) (half_pos hε)
    obtain ⟨N₂, hN₂⟩ := (Metric.tendsto_atTop.mp hzy) (ε / 2) (half_pos hε)
    refine ⟨max N₁ N₂, fun n hn => ?_⟩
    have h2 := hN₂ n (le_of_max_le_right hn)
    rw [Real.dist_0_eq_abs, abs_of_nonneg dist_nonneg] at h2
    calc dist (z n) τs ≤ dist (z n) (y n) + dist (y n) τs := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add h2 (hN₁ n (le_of_max_le_left hn))
      _ = ε := by ring
  by_cases h : ∃ n, z n = τs
  · obtain ⟨n, hn⟩ := h
    refine ⟨γ n, hγΓ n, ?_⟩
    rw [← hn, hz, smul_inv_smul]
  · push_neg at h
    have hw : Tendsto z atTop (𝓝[≠] τs) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within z hzlim (Eventually.of_forall fun n => h n)
    obtain ⟨n, hn⟩ := (hw.eventually (hdisc τs τ)).exists
    exact (hn ⟨(γ n)⁻¹, Γ.inv_mem (hγΓ n), rfl⟩).elim

theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι) (hqq' : q' ≠ q)
    {N : ℕ} [NeZero N] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N)
    (hN : Squarefree N) (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)

    (latt : FakeEllipticCurve Λ N ℂ → Submodule ℤ (Fin 2 → ℂ))
    (e : ∀ E : FakeEllipticCurve Λ N ℂ,
      SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f ≃ ((Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup))

    (hL1 : ∀ E : FakeEllipticCurve Λ N ℂ,
        (∃ b₀ : Module.Basis (Fin 4) ℝ (Fin 2 → ℂ), latt E = Submodule.span ℤ (Set.range b₀)) ∧
        (∀ x ∈ Λ, ∀ v ∈ latt E, ((ι x).map (algebraMap ℝ ℂ)).mulVec v ∈ latt E))

    (hE1 : ∀ (E : FakeEllipticCurve Λ N ℂ) (P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f),
        e E (E.L.mul (𝟙 (Spec (CommRingCat.of ℂ))) P Q) = e E P + e E Q)

    (hE2 : ∀ (E : FakeEllipticCurve Λ N ℂ) (x : ↥Λ) (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f) (v : Fin 2 → ℂ),
        e E P = (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) →
        e E (pushPt (E.act x) (E.act_over x) P) =
          ((((ι (x : ℍ[ℚ, a, b])).map (algebraMap ℝ ℂ)).mulVec v : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup))

    (hH1 : ∀ (E E' : FakeEllipticCurve Λ N ℂ) (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f),
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℂ)) (P Q : SchemeHomOver t E.f),
          mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) →
        (∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E'.act x) →
        ∃ c : ℂ, (∀ v ∈ latt E, c • v ∈ latt E') ∧
          ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f) (v : Fin 2 → ℂ),
            e E P = (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) →
            e E' (mapPt φ hφ P) = ((c • v : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt E').toAddSubgroup))

    (hH2 : ∀ (E E' : FakeEllipticCurve Λ N ℂ) (c : ℂ), (∀ v ∈ latt E, c • v ∈ latt E') →
        ∃ (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f),
          (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℂ)) (P Q : SchemeHomOver t E.f),
            mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) ∧
          (∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E'.act x) ∧
          ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f) (v : Fin 2 → ℂ),
            e E P = (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) →
            e E' (mapPt φ hφ P) = ((c • v : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt E').toAddSubgroup))

    (hH3 : ∀ (E E' : FakeEllipticCurve Λ N ℂ) (φ ψ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f) (hψ : ψ ≫ E'.f = E.f),
        (∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f, mapPt φ hφ P = mapPt ψ hψ P) → φ = ψ)

    (hAN : ∀ (E : FakeEllipticCurve Λ N ℂ) (U : E.A.Opens) (f : Γ(E.A, U)),
        IsOpen {v : Fin 2 → ℂ | ⊤ ≤ ((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1 ⁻¹ᵁ U} ∧
        ∃ F : (Fin 2 → ℂ) → ℂ,
          DifferentiableOn ℂ F {v : Fin 2 → ℂ | ⊤ ≤ ((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1 ⁻¹ᵁ U} ∧
          ∀ (v : Fin 2 → ℂ) (h : ⊤ ≤ ((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1 ⁻¹ᵁ U),
            F v = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
              ((((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1.appLE U ⊤ h) f))

    (hCOV : ∀ (E : FakeEllipticCurve Λ N ℂ) (v₀ : Fin 2 → ℂ),
        ∃ (U : E.A.Opens) (f₁ f₂ : Γ(E.A, U)) (ε : ℝ) (D : (Fin 2 → ℂ) ≃L[ℂ] (Fin 2 → ℂ))
          (F : (Fin 2 → ℂ) → (Fin 2 → ℂ)),
          0 < ε ∧
          (∀ v ∈ Metric.ball v₀ ε, ⊤ ≤ ((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1 ⁻¹ᵁ U) ∧
          (∀ (v : Fin 2 → ℂ) (h : ⊤ ≤ ((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1 ⁻¹ᵁ U),
            v ∈ Metric.ball v₀ ε →
            F v = ![(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
                      ((((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1.appLE U ⊤ h) f₁),
                    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
                      ((((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1.appLE U ⊤ h) f₂)]) ∧
          HasFDerivAt F (D : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)) v₀)

    (m : ℕ) (hm : 3 ≤ m) (hmc : m.Coprime (N * q * q'))
    (M : Scheme.{0}) (πM : M ⟶ Spec (CommRingCat.of ℂ))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of ℂ)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM)
    (hM : IsFineModuli Λ N m M πM ptF) (hsm : SmoothOfRelativeDimension 1 πM)
    (hprop : IsProper πM) :
    IsClosed {τ : UpperHalfPlane | ∃ (u : FakeEllipticCurve.WithFullLevel Λ N m ℂ) (c : ℂ), c ≠ 0 ∧
        c • latt u.1 = qmPeriodLattice ι Λ τ ∧

          ∀ (lam : ℍ[ℚ, a, b]), lam ∈ Λ → ∀ r ∈ R,
            (∃ v : Fin 2 → ℂ,
              (∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) u.1.f,
                FactorsThrough u.1.lev P ∧ e u.1 P = (v : (Fin 2 → ℂ) ⧸ (latt u.1).toAddSubgroup)) ∧
              c • v = ((N : ℂ)⁻¹) • qmPeriodMap ι τ lam) →
            (∃ v : Fin 2 → ℂ,
              (∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) u.1.f,
                FactorsThrough u.1.lev P ∧ e u.1 P = (v : (Fin 2 → ℂ) ⧸ (latt u.1).toAddSubgroup)) ∧
              c • v = ((N : ℂ)⁻¹) • qmPeriodMap ι τ (lam * r))} := by

  classical
  set I : Set UpperHalfPlane := {τ : UpperHalfPlane | ∃ (u : FakeEllipticCurve.WithFullLevel Λ N m ℂ) (c : ℂ), c ≠ 0 ∧
        c • latt u.1 = qmPeriodLattice ι Λ τ ∧

          ∀ (lam : ℍ[ℚ, a, b]), lam ∈ Λ → ∀ r ∈ R,
            (∃ v : Fin 2 → ℂ,
              (∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) u.1.f,
                FactorsThrough u.1.lev P ∧ e u.1 P = (v : (Fin 2 → ℂ) ⧸ (latt u.1).toAddSubgroup)) ∧
              c • v = ((N : ℂ)⁻¹) • qmPeriodMap ι τ lam) →
            (∃ v : Fin 2 → ℂ,
              (∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) u.1.f,
                FactorsThrough u.1.lev P ∧ e u.1 P = (v : (Fin 2 → ℂ) ⧸ (latt u.1).toAddSubgroup)) ∧
              c • v = ((N : ℂ)⁻¹) • qmPeriodMap ι τ (lam * r))} with hI
  let EvConv : (ℕ → SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) πM) → SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) πM → Prop :=
    fun σ Q => ∀ (U : M.Opens), IsAffineOpen U → ∀ (hQ : ⊤ ≤ Q.1 ⁻¹ᵁ U),
      ∃ n₀ : ℕ, ∃ hP : ∀ n, n₀ ≤ n → ⊤ ≤ (σ n).1 ⁻¹ᵁ U,
        ∀ f : Γ(M, U),
          Tendsto (fun n : ℕ => if h : n₀ ≤ n then
              (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((σ n).1.appLE U ⊤ (hP n h)) f) else 0)
            atTop (𝓝 ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((Q.1.appLE U ⊤ hQ) f)))
  let LEV : FakeEllipticCurve.WithFullLevel Λ N m ℂ → ℂ → UpperHalfPlane → Prop := fun u c τ =>
    ∀ (lam : ℍ[ℚ, a, b]), lam ∈ Λ → ∀ r ∈ R,
              (∃ v : Fin 2 → ℂ,
                (∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) u.1.f,
                  FactorsThrough u.1.lev P ∧ e u.1 P = (v : (Fin 2 → ℂ) ⧸ (latt u.1).toAddSubgroup)) ∧
                c • v = ((N : ℂ)⁻¹) • qmPeriodMap ι τ lam) →
              (∃ v : Fin 2 → ℂ,
                (∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) u.1.f,
                  FactorsThrough u.1.lev P ∧ e u.1 P = (v : (Fin 2 → ℂ) ⧸ (latt u.1).toAddSubgroup)) ∧
                c • v = ((N : ℂ)⁻¹) • qmPeriodMap ι τ (lam * r))

  have LEV_MODULE : ∀ u : FakeEllipticCurve.WithFullLevel Λ N m ℂ, ∃ Mu : Submodule ℤ (Fin 2 → ℂ),
      latt u.1 ≤ Mu ∧ (∀ v ∈ Mu, ((N : ℤ) • v) ∈ latt u.1) ∧
      (∀ x ∈ Λ, ∀ v ∈ Mu, ((ι x).map (algebraMap ℝ ℂ)).mulVec v ∈ Mu) ∧
      (latt u.1).toAddSubgroup.relIndex Mu.toAddSubgroup = N ^ 2 ∧
      ∀ (c : ℂ) (τ : UpperHalfPlane), c ≠ 0 → (LEV u c τ ↔
        (∀ (lam : ℍ[ℚ, a, b]), lam ∈ Λ → ∀ r ∈ R,
          ((N : ℂ)⁻¹) • qmPeriodMap ι τ lam ∈ c • Mu → ((N : ℂ)⁻¹) • qmPeriodMap ι τ (lam * r) ∈ c • Mu)) := by
    intro u
    obtain ⟨ME, hME, hLM, hst, hMN, hidx⟩ :=
      CerednikDrinfeld.QM.FakeEllipticCurve.exists_submodule_forall_mem_iff_factorsThrough_lev_of_pointEquiv
        hB Λ hΛ ι hι hqq' hqN hq'N latt e hL1 hE1 hE2 u.1
    refine ⟨ME, hLM, hMN, hst, hidx, fun c τ _ => ⟨fun h lam hlam r hr hw => ?_, fun h lam hlam r hr hw => ?_⟩⟩
    · obtain ⟨s, hs, hse⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hw
      obtain ⟨v, hv, hcv⟩ := h lam hlam r hr ⟨s, (hME s).1 hs, hse⟩
      exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨v, (hME v).2 hv, hcv⟩
    · obtain ⟨s, hs, hse⟩ := hw
      obtain ⟨v, hv, hcv⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1
        (h lam hlam r hr ((Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨s, (hME s).2 hs, hse⟩))
      exact ⟨v, (hME v).1 hv, hcv⟩

  have CHART_OPEN_EVAL : ∀ (W : Set UpperHalfPlane), IsOpen W →
      ∀ (h : UpperHalfPlane → SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) πM), Set.InjOn h W →
      (∀ (U : M.Opens) (s : Γ(M, U)),
              IsOpen {z : ℂ | 0 < z.im ∧ UpperHalfPlane.ofComplex z ∈ W ∧ ⊤ ≤ (h (UpperHalfPlane.ofComplex z)).1 ⁻¹ᵁ U} ∧
              ∃ F : ℂ → ℂ,
              DifferentiableOn ℂ F
                {z : ℂ | 0 < z.im ∧ UpperHalfPlane.ofComplex z ∈ W ∧ ⊤ ≤ (h (UpperHalfPlane.ofComplex z)).1 ⁻¹ᵁ U} ∧
              ∀ (z : ℂ), 0 < z.im → UpperHalfPlane.ofComplex z ∈ W →
                ∀ hU : ⊤ ≤ (h (UpperHalfPlane.ofComplex z)).1 ⁻¹ᵁ U,
                  F z = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((h (UpperHalfPlane.ofComplex z)).1.appLE U ⊤ hU) s)) →
      ∀ τs ∈ W, ∀ σ : ℕ → SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) πM, EvConv σ (h τs) →
        ∃ (τ' : ℕ → UpperHalfPlane) (n₀ : ℕ), (∀ n, n₀ ≤ n → τ' n ∈ W ∧ h (τ' n) = σ n) ∧
          Tendsto τ' atTop (𝓝 τs) := by
    intro W hW h hinj hHOL τs hτs σ hconv
    exact AlgebraicGeometry.exists_tendsto_forall_eq_of_injOn_of_differentiableOn_appLE_of_tendsto_appLE M πM hsm W hW h hinj hHOL τs hτs σ hconv

  have PERIOD_UNIQ : ∀ (u : FakeEllipticCurve.WithFullLevel Λ N m ℂ) (τ₁ τ₂ : UpperHalfPlane) (c₁ c₂ : ℂ),
      c₁ ≠ 0 → c₂ ≠ 0 →
      c₁ • latt u.1 = qmPeriodLattice ι Λ τ₁ → LEV u c₁ τ₁ →
      c₂ • latt u.1 = qmPeriodLattice ι Λ τ₂ → LEV u c₂ τ₂ →
      ∃ γ ∈ fuchsianGroup R ι, γ • τ₁ = τ₂ := by
    intro u τ₁ τ₂ c₁ c₂ hc₁ hc₂ hL₁ hlev₁ hL₂ hlev₂
    obtain ⟨Mu, hLM, hMN, hst, hidx, hiff⟩ := LEV_MODULE u
    exact QuaternionAlgebra.IsEichlerOrder.exists_fuchsianGroup_smul_eq_of_smul_eq_qmPeriodLattice_of_forall_mem_imp_mem
      hqN hq'N hqq' hB Λ hΛ hN R hR hRΛ ι hι (latt u.1) Mu hLM hMN hst hidx τ₁ τ₂ c₁ c₂ hc₁ hc₂ hL₁ hL₂
      ((hiff c₁ τ₁ hc₁).1 hlev₁) ((hiff c₂ τ₂ hc₂).1 hlev₂)
  have GAMMA_STAB : ∀ γ ∈ fuchsianGroup R ι, ∀ τ : UpperHalfPlane, τ ∈ I → γ • τ ∈ I := by
    intro γ hγ τ hτ
    rw [hI] at hτ ⊢
    obtain ⟨u, c, hc, hL, hlev⟩ := hτ
    obtain ⟨Mu, hLM, hMN, hst, hidx, hiff⟩ := LEV_MODULE u
    obtain ⟨c', hc', hL', hlev'⟩ :=
      QuaternionAlgebra.IsEichlerOrder.exists_smul_eq_qmPeriodLattice_smul_and_forall_mem_imp_mem_of_mem_fuchsianGroup
        hqN hq'N hqq' hB Λ hΛ hN R hR hRΛ ι hι (latt u.1) Mu τ c hc hL ((hiff c τ hc).1 hlev) γ hγ
    exact ⟨u, c', hc', hL', (hiff c' (γ • τ) hc').2 hlev'⟩
  obtain ⟨hdetΓ, -, hdiscΓ, -⟩ := CerednikDrinfeld.fuchsianGroup_discrete_neg_mem_and_exists_isCompact hB R hR.isOrder ι hι
  haveI := hdiscΓ
  have hORBIT : ∀ τ₁ τ₂ : UpperHalfPlane, ∀ᶠ z in 𝓝[≠] τ₁, ¬ ∃ γ ∈ fuchsianGroup R ι, γ • τ₂ = z := fun τ₁ τ₂ =>
    UpperHalfPlane.eventually_nhdsNE_not_exists_smul_eq_of_discreteTopology_of_det_eq_one (fuchsianGroup R ι) hdetΓ τ₁ τ₂
  have PROPER_DISC : ∀ (x y : ℕ → UpperHalfPlane) (τ τs : UpperHalfPlane),
      Tendsto x atTop (𝓝 τ) → Tendsto y atTop (𝓝 τs) →
      (∀ n, ∃ γ ∈ fuchsianGroup R ι, γ • y n = x n) → ∃ γ ∈ fuchsianGroup R ι, γ • τs = τ :=
    fun x y τ τs hx hy hγ => P2mWs2.exists_smul_eq_of_tendsto_of_forall_exists_smul_eq (fuchsianGroup R ι)
      (fun τ₁ τ₂ => hORBIT τ₁ τ₂) hdetΓ x y τ τs hx hy hγ

  rw [← closure_subset_iff_isClosed]
  intro τ hτ
  obtain ⟨x, hxI, hxτ⟩ := mem_closure_iff_seq_limit.mp hτ
  have hxI' : ∀ n, ∃ (u : FakeEllipticCurve.WithFullLevel Λ N m ℂ) (c : ℂ), c ≠ 0 ∧
      c • latt u.1 = qmPeriodLattice ι Λ (x n) ∧ LEV u c (x n) := fun n => by
    have := hxI n
    rw [hI] at this
    exact this
  choose u c hc using hxI'
  haveI : IsProper πM := hprop
  obtain ⟨Q, φ, hφ, hQ⟩ :=
    AlgebraicGeometry.exists_tendsto_appLE_of_isProper_of_smoothOfRelativeDimension_one_complex M πM hsm
      (fun n => ptF ℂ (𝟙 (Spec (CommRingCat.of ℂ))) (u n))
  obtain ⟨W, hW, h, hσ, hinj, hHOL, hFIB⟩ :=
    CerednikDrinfeld.QM.IsFineModuli.exists_isOpen_injOn_periodChart_of_analytic_of_isEichlerOrder
      hB Λ hΛ ι hι hqq' hqN hq'N hN R hR hRΛ latt e hL1 hE1 hE2 hH1 hH2 hH3 hAN hCOV m hm hmc M πM ptF hM hsm Q
  obtain ⟨τs, hτsW, hτsQ⟩ := hσ
  obtain ⟨τ', n₀, hτ', hτ'lim⟩ := CHART_OPEN_EVAL W hW h hinj hHOL τs hτsW
    (fun n => ptF ℂ (𝟙 (Spec (CommRingCat.of ℂ))) (u (φ n))) (by rw [hτsQ]; exact hQ)
  have hγ : ∀ n, ∃ γ ∈ fuchsianGroup R ι, γ • τ' (n + n₀) = x (φ (n + n₀)) := by
    intro n
    obtain ⟨hW', hh⟩ := hτ' (n + n₀) (Nat.le_add_left n₀ n)
    obtain ⟨c₂, hc₂, hL₂, hLEV₂⟩ := hFIB (τ' (n + n₀)) hW' (u (φ (n + n₀))) hh.symm
    obtain ⟨hc₁, hL₁, hLEV₁⟩ := hc (φ (n + n₀))
    exact PERIOD_UNIQ (u (φ (n + n₀))) _ _ c₂ (c (φ (n + n₀))) hc₂ hc₁ hL₂ hLEV₂ hL₁ hLEV₁
  have hx' : Tendsto (fun n => x (φ (n + n₀))) atTop (𝓝 τ) :=
    (hxτ.comp hφ.tendsto_atTop).comp (tendsto_add_atTop_nat n₀)
  have hy' : Tendsto (fun n => τ' (n + n₀)) atTop (𝓝 τs) := hτ'lim.comp (tendsto_add_atTop_nat n₀)
  obtain ⟨γ, hγΓ, hγτ⟩ := PROPER_DISC (fun n => x (φ (n + n₀))) (fun n => τ' (n + n₀)) τ τs hx' hy' hγ
  have hτsI : τs ∈ I := by
    obtain ⟨ustar, hustar⟩ := hM.ptF_surjective ℂ (𝟙 (Spec (CommRingCat.of ℂ))) Q
    obtain ⟨c₀, hc₀, hL₀, hLEV₀⟩ := hFIB τs hτsW ustar (by rw [hustar, hτsQ])
    rw [hI]
    exact ⟨ustar, c₀, hc₀, hL₀, hLEV₀⟩
  rw [← hγτ]
  exact GAMMA_STAB γ hγΓ τs hτsI

end S_CerednikDrinfeld_QM_IsFineModuli_isClosed_setOf_exists_smul_latt_eq_qmPeriodLattice_of_isProper_of_analytic
end P2MW
export P2MW.S_CerednikDrinfeld_QM_IsFineModuli_isClosed_setOf_exists_smul_latt_eq_qmPeriodLattice_of_isProper_of_analytic (solution)
