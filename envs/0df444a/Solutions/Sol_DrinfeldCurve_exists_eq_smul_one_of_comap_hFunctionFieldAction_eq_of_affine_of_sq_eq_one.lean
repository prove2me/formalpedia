-- Prove2me | solution 1 for DrinfeldCurve.exists_eq_smul_one_of_comap_hFunctionFieldAction_eq_of_affine_of_sq_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/a202eddf-267a-5544-966a-67b7c146c797

import Mathlib
import Definitions.Def_DrinfeldCurve_FunctionField
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Theorems.Thm_DrinfeldCurve_affinePlaces_census
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DrinfeldCurve_exists_eq_smul_one_of_comap_hFunctionFieldAction_eq_of_affine_of_sq_eq_one
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap"
p2m_attr_erase "instance" "AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen"
p2m_attr_erase "simp" "ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule"
p2m_attr_erase "simp" "AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false

namespace DrinfeldCurve
p2m_export "DrinfeldCurve" "drinfeldFunctionField hFunctionFieldAction hFunctionFieldAction_algebraMap CoordRing mk x y scalePoly_X ofZMod ofZMod_pow_card substPoly_X scalarOf hSubgroup hAction hAction_mk affinePlaces_census"
p2m_open "DrinfeldCurve"

namespace FreeDL

open MvPolynomial

variable (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [Algebra (GaloisField q 2) k]

theorem charP_k : CharP k q :=
  charP_of_injective_algebraMap (algebraMap (GaloisField q 2) k).injective q

theorem form_eq_zero_of_rational_line {α β a b : k} (hα : α ^ q = α) (hβ : β ^ q = β)
    (hne : α ≠ 0 ∨ β ≠ 0) (h : α * a + β * b = 0) : a * b ^ q - a ^ q * b = 0 := by
  haveI := charP_k q k
  have hq0 : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  by_cases hβ0 : β = 0
  · have hα0 : α ≠ 0 := hne.resolve_right (not_not.mpr hβ0)
    rw [hβ0, zero_mul, add_zero] at h
    have ha : a = 0 := (mul_eq_zero.mp h).resolve_left hα0
    rw [ha, zero_mul, zero_pow hq0, zero_mul, sub_self]
  ·
    have hb : b = -(α / β) * a := by field_simp; linear_combination h
    have hμ : (-(α / β)) ^ q = -(α / β) := by
      have e := (frobenius_def (R := k) q (-(α / β))).symm
      rw [map_neg, map_div₀, frobenius_def, frobenius_def, hα, hβ] at e
      exact e
    rw [hb, mul_pow, hμ]
    ring

theorem hAction_x (p : ↥(hSubgroup q)) :
    hAction q k p (x q k) =
      algebraMap k (CoordRing q k)
          (ofZMod q k ((p : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ).1 0 0) *
            scalarOf q k (p : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ).2) * x q k +
        algebraMap k (CoordRing q k)
          (ofZMod q k ((p : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ).1 1 0) *
            scalarOf q k (p : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ).2) * y q k := by
  show hAction q k p (mk q k (X 0)) = _
  rw [hAction_mk, substPoly_X]
  simp only [Fin.sum_univ_two, map_add, map_mul, scalePoly_X, MvPolynomial.algHom_C, AlgHom.commutes]
  simp only [x, y]
  ring

theorem hAction_y (p : ↥(hSubgroup q)) :
    hAction q k p (y q k) =
      algebraMap k (CoordRing q k)
          (ofZMod q k ((p : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ).1 0 1) *
            scalarOf q k (p : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ).2) * x q k +
        algebraMap k (CoordRing q k)
          (ofZMod q k ((p : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ).1 1 1) *
            scalarOf q k (p : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ).2) * y q k := by
  show hAction q k p (mk q k (X 1)) = _
  rw [hAction_mk, substPoly_X]
  simp only [Fin.sum_univ_two, map_add, map_mul, scalePoly_X, MvPolynomial.algHom_C, AlgHom.commutes]
  simp only [x, y]
  ring

end FreeDL

end DrinfeldCurve

open _root_.DrinfeldCurve _root_.P2MW.S_DrinfeldCurve_exists_eq_smul_one_of_comap_hFunctionFieldAction_eq_of_affine_of_sq_eq_one.DrinfeldCurve DrinfeldCurve.FreeDL in
theorem solution
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [Algebra (GaloisField q 2) k] [IsAlgClosed k] [IsDomain (CoordRing q k)]
    (p : ↥(hSubgroup q))
    (hc : (((p : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ).2 : (GaloisField q 2)ˣ) : GaloisField q 2) ^ 2 = 1)
    (w : AlgebraicCurve.Place k (drinfeldFunctionField q k))
    (hX : algebraMap (CoordRing q k) (drinfeldFunctionField q k) (x q k) ∈ w.toValuationSubring)
    (hY : algebraMap (CoordRing q k) (drinfeldFunctionField q k) (y q k) ∈ w.toValuationSubring)
    (hfix : w.toValuationSubring.comap (hFunctionFieldAction q k p).toAlgHom.toRingHom = w.toValuationSubring) :
    ∃ ε : ZMod q, ε ^ 2 = 1 ∧
      ((p : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ).1 : Matrix (Fin 2) (Fin 2) (ZMod q)) =
        ε • (1 : Matrix (Fin 2) (Fin 2) (ZMod q)) ∧
      (((p : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ).2 : (GaloisField q 2)ˣ) : GaloisField q 2) =
        algebraMap (ZMod q) (GaloisField q 2) ε := by
  classical
  haveI := FreeDL.charP_k q k
  set O := w.toValuationSubring with hO
  set σ := hFunctionFieldAction q k p with hσ
  set g : Matrix (Fin 2) (Fin 2) (ZMod q) :=
    ((p : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ).1 : Matrix (Fin 2) (Fin 2) (ZMod q)) with hg
  set u : (GaloisField q 2)ˣ := (p : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ).2 with hu
  set c : k := scalarOf q k u with hcdef

  obtain ⟨a, b, hab, hXa, hYb⟩ := (affinePlaces_census q k).2 w hX hY

  have hmem : ∀ f : drinfeldFunctionField q k, σ f ∈ O ↔ f ∈ O := fun f => by
    have e : f ∈ O.comap σ.toAlgHom.toRingHom ↔ f ∈ O := by rw [hfix]
    exact ValuationSubring.mem_comap.symm.trans e
  have hnu : ∀ f : drinfeldFunctionField q k, f ∈ O.nonunits ↔ f = 0 ∨ f⁻¹ ∉ O := by
    intro f
    rw [ValuationSubring.mem_nonunits_iff]
    rcases eq_or_ne f 0 with rfl | hf
    · simp
    · rw [← ValuationSubring.valuation_le_one_iff, map_inv₀, not_le,
        one_lt_inv₀ (zero_lt_iff.mpr ((map_ne_zero _).mpr hf))]
      simp [hf]
  have hσnu : ∀ f : drinfeldFunctionField q k, σ f ∈ O.nonunits ↔ f ∈ O.nonunits := fun f => by
    rw [hnu, hnu, map_eq_zero_iff _ σ.injective, ← map_inv₀, hmem]

  have hkO : ∀ t : k, algebraMap k (drinfeldFunctionField q k) t ∈ O := w.algebraMap_mem'
  have hconst : ∀ t : k, algebraMap k (drinfeldFunctionField q k) t ∈ O.nonunits → t = 0 := by
    intro t ht
    rcases (hnu _).mp ht with h0 | hinv
    · exact (map_eq_zero_iff _ (algebraMap k (drinfeldFunctionField q k)).injective).mp h0
    · exfalso; apply hinv; rw [← map_inv₀]; exact hkO _

  have hN_add : ∀ f₁ f₂ : drinfeldFunctionField q k, f₁ ∈ O.nonunits → f₂ ∈ O.nonunits → f₁ + f₂ ∈ O.nonunits := by
    intro f₁ f₂ h₁ h₂
    obtain ⟨h₁', hm₁⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp h₁
    obtain ⟨h₂', hm₂⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp h₂
    exact ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mpr ⟨O.add_mem _ _ h₁' h₂', Ideal.add_mem _ hm₁ hm₂⟩
  have hN_mul : ∀ f₁ f₂ : drinfeldFunctionField q k, f₁ ∈ O → f₂ ∈ O.nonunits → f₁ * f₂ ∈ O.nonunits := by
    intro f₁ f₂ h₁ h₂
    obtain ⟨h₂', hm₂⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp h₂
    exact ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mpr
      ⟨O.mul_mem _ _ h₁ h₂', Ideal.mul_mem_left _ ⟨f₁, h₁⟩ hm₂⟩
  have hN_neg : ∀ f : drinfeldFunctionField q k, f ∈ O.nonunits → -f ∈ O.nonunits := by
    intro f h
    obtain ⟨h', hm⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp h
    exact ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mpr ⟨O.neg_mem _ h', neg_mem hm⟩

  have htower : ∀ t : k, algebraMap (CoordRing q k) (drinfeldFunctionField q k) (algebraMap k (CoordRing q k) t) =
      algebraMap k (drinfeldFunctionField q k) t :=
    fun t => (IsScalarTower.algebraMap_apply k (CoordRing q k) (drinfeldFunctionField q k) t).symm
  have hσX : σ (algebraMap (CoordRing q k) (drinfeldFunctionField q k) (x q k)) =
      algebraMap k (drinfeldFunctionField q k) (ofZMod q k (g 0 0) * c) * algebraMap (CoordRing q k) (drinfeldFunctionField q k) (x q k) +
        algebraMap k (drinfeldFunctionField q k) (ofZMod q k (g 1 0) * c) * algebraMap (CoordRing q k) (drinfeldFunctionField q k) (y q k) := by
    rw [hσ, hFunctionFieldAction_algebraMap, FreeDL.hAction_x]
    simp only [map_add, map_mul, htower, hg, hcdef, hu]
  have hσY : σ (algebraMap (CoordRing q k) (drinfeldFunctionField q k) (y q k)) =
      algebraMap k (drinfeldFunctionField q k) (ofZMod q k (g 0 1) * c) * algebraMap (CoordRing q k) (drinfeldFunctionField q k) (x q k) +
        algebraMap k (drinfeldFunctionField q k) (ofZMod q k (g 1 1) * c) * algebraMap (CoordRing q k) (drinfeldFunctionField q k) (y q k) := by
    rw [hσ, hFunctionFieldAction_algebraMap, FreeDL.hAction_y]
    simp only [map_add, map_mul, htower, hg, hcdef, hu]

  have hE : ∀ (s t d : k) (Z : drinfeldFunctionField q k),
      Z = algebraMap k (drinfeldFunctionField q k) s * algebraMap (CoordRing q k) (drinfeldFunctionField q k) (x q k) +
            algebraMap k (drinfeldFunctionField q k) t * algebraMap (CoordRing q k) (drinfeldFunctionField q k) (y q k) →
      Z - algebraMap k (drinfeldFunctionField q k) d ∈ O.nonunits → s * a + t * b = d := by
    intro s t d Z hZ hZd
    have h1 : Z - algebraMap k (drinfeldFunctionField q k) (s * a + t * b) ∈ O.nonunits := by
      have e : Z - algebraMap k (drinfeldFunctionField q k) (s * a + t * b) =
          algebraMap k (drinfeldFunctionField q k) s *
              (algebraMap (CoordRing q k) (drinfeldFunctionField q k) (x q k) - algebraMap k (drinfeldFunctionField q k) a) +
            algebraMap k (drinfeldFunctionField q k) t *
              (algebraMap (CoordRing q k) (drinfeldFunctionField q k) (y q k) - algebraMap k (drinfeldFunctionField q k) b) := by
        rw [hZ, map_add, map_mul, map_mul]; ring
      rw [e]
      exact hN_add _ _ (hN_mul _ _ (hkO s) hXa) (hN_mul _ _ (hkO t) hYb)
    have h2 : algebraMap k (drinfeldFunctionField q k) (s * a + t * b - d) ∈ O.nonunits := by
      have e : algebraMap k (drinfeldFunctionField q k) (s * a + t * b - d) =
          (Z - algebraMap k (drinfeldFunctionField q k) d) +
            -(Z - algebraMap k (drinfeldFunctionField q k) (s * a + t * b)) := by
        rw [map_sub]; ring
      rw [e]; exact hN_add _ _ hZd (hN_neg _ h1)
    exact sub_eq_zero.mp (hconst _ h2)
  have hσXa : σ (algebraMap (CoordRing q k) (drinfeldFunctionField q k) (x q k)) - algebraMap k (drinfeldFunctionField q k) a ∈ O.nonunits := by
    have e : σ (algebraMap (CoordRing q k) (drinfeldFunctionField q k) (x q k)) - algebraMap k (drinfeldFunctionField q k) a =
        σ (algebraMap (CoordRing q k) (drinfeldFunctionField q k) (x q k) - algebraMap k (drinfeldFunctionField q k) a) := by
      rw [map_sub, AlgEquiv.commutes]
    rw [e, hσnu]; exact hXa
  have hσYb : σ (algebraMap (CoordRing q k) (drinfeldFunctionField q k) (y q k)) - algebraMap k (drinfeldFunctionField q k) b ∈ O.nonunits := by
    have e : σ (algebraMap (CoordRing q k) (drinfeldFunctionField q k) (y q k)) - algebraMap k (drinfeldFunctionField q k) b =
        σ (algebraMap (CoordRing q k) (drinfeldFunctionField q k) (y q k) - algebraMap k (drinfeldFunctionField q k) b) := by
      rw [map_sub, AlgEquiv.commutes]
    rw [e, hσnu]; exact hYb
  have E0 : ofZMod q k (g 0 0) * c * a + ofZMod q k (g 1 0) * c * b = a := hE _ _ _ _ hσX hσXa
  have E1 : ofZMod q k (g 0 1) * c * a + ofZMod q k (g 1 1) * c * b = b := hE _ _ _ _ hσY hσYb

  obtain ⟨ε, hε2, hεu⟩ : ∃ ε : ZMod q, ε ^ 2 = 1 ∧ ((u : (GaloisField q 2)ˣ) : GaloisField q 2) =
      algebraMap (ZMod q) (GaloisField q 2) ε := by
    rcases sq_eq_one_iff.mp hc with h1 | h1
    · exact ⟨1, one_pow 2, by rw [h1, map_one]⟩
    · exact ⟨-1, by ring, by rw [h1, map_neg, map_one]⟩
  have hcε : c = ofZMod q k ε := by
    rw [hcdef, scalarOf, hεu]; rfl
  have hc2 : c * c = 1 := by rw [hcε, ← map_mul, ← sq, hε2, map_one]

  have hcol0 : ofZMod q k (g 0 0 - ε) * a + ofZMod q k (g 1 0) * b = 0 := by
    rw [map_sub, ← hcε]
    linear_combination c * E0 - (ofZMod q k (g 0 0) * a + ofZMod q k (g 1 0) * b) * hc2
  have hcol1 : ofZMod q k (g 0 1) * a + ofZMod q k (g 1 1 - ε) * b = 0 := by
    rw [map_sub, ← hcε]
    linear_combination c * E1 - (ofZMod q k (g 0 1) * a + ofZMod q k (g 1 1) * b) * hc2

  have hzero : ∀ α' β' : ZMod q, ofZMod q k α' * a + ofZMod q k β' * b = 0 → α' = 0 ∧ β' = 0 := by
    intro α' β' h
    by_contra hne
    rw [not_and_or] at hne
    have hne' : ofZMod q k α' ≠ 0 ∨ ofZMod q k β' ≠ 0 := by
      rcases hne with h1 | h1
      · exact Or.inl ((map_ne_zero _).mpr h1)
      · exact Or.inr ((map_ne_zero _).mpr h1)
    have h0 := FreeDL.form_eq_zero_of_rational_line q k (ofZMod_pow_card q k α') (ofZMod_pow_card q k β') hne' h
    rw [hab] at h0
    exact one_ne_zero h0
  obtain ⟨h00, h10⟩ := hzero _ _ hcol0
  obtain ⟨h01, h11⟩ := hzero _ _ hcol1
  refine ⟨ε, hε2, ?_, hεu⟩
  have e00 : g 0 0 = ε := sub_eq_zero.mp h00
  have e11 : g 1 1 = ε := sub_eq_zero.mp h11
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e00, e11, h10, h01, Matrix.smul_apply]

#print axioms solution

end S_DrinfeldCurve_exists_eq_smul_one_of_comap_hFunctionFieldAction_eq_of_affine_of_sq_eq_one
end P2MW
export P2MW.S_DrinfeldCurve_exists_eq_smul_one_of_comap_hFunctionFieldAction_eq_of_affine_of_sq_eq_one (solution)
