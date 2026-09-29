-- Prove2me | solution 1 for CuspForm.finiteDimensional_and_finrank_tensorProduct_intTwoCuspForms_eq_finrank_cuspForm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/9f60f618-e141-5596-8166-4bbd65eb7985

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Theorems.Thm_CuspForm_exists_linearIndependent_forall_twoCuspLattice_eq_span
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_finiteDimensional_and_finrank_tensorProduct_intTwoCuspForms_eq_finrank_cuspForm
p2m_attr_erase "instance" "CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree HeckeEis.instFiniteIndexHeckeUpper ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion CohCarrier.GammaHLower_finiteIndex Ihara.instGroupIharaAmalgam"
p2m_attr_erase "simp" "ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.LevelN.coe_jGen PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂"
p2m_attr_erase "simp" "PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01"
p2m_attr_erase "simp" "CohCarrier.uMat_apply_00 CohCarrier.coe_uElt Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped TensorProduct MatrixGroups

namespace CuspForm
p2m_export "CuspForm" "mk ext intIdeal IntTwoCuspForms IntTwoCuspForms.equivTwoCuspForms twoCuspLattice exists_linearIndependent_forall_twoCuspLattice_eq_span"
namespace SrcRank
p2m_open "CuspForm"

noncomputable def intEquivBot : ℤ ≃+* (⊥ : Subring ℂ) :=
  RingEquiv.ofBijective ((Int.castRingHom ℂ).codRestrict (⊥ : Subring ℂ) fun z => Subring.mem_bot.mpr ⟨z, rfl⟩)
    ⟨fun a b h => by
      have := congrArg Subtype.val h
      exact Int.cast_injective (α := ℂ) this,
     fun ⟨x, hx⟩ => by
      obtain ⟨z, rfl⟩ := Subring.mem_bot.mp hx
      exact ⟨z, rfl⟩⟩

@[scoped simp] theorem intEquivBot_apply_coe (z : ℤ) : ((intEquivBot z : (⊥ : Subring ℂ)) : ℂ) = z := rfl

theorem intEquivBot_natCast (p : ℕ) : intEquivBot (p : ℤ) = (p : (⊥ : Subring ℂ)) := by
  apply Subtype.ext; simp

noncomputable def botQuotEquivZMod (p : ℕ) : ((⊥ : Subring ℂ) ⧸ CuspForm.intIdeal p) ≃+* ZMod p :=
  (Ideal.quotientEquiv (Ideal.span {(p : ℤ)}) (CuspForm.intIdeal p) intEquivBot (by
      rw [Ideal.map_span, Set.image_singleton]
      show CuspForm.intIdeal p = Ideal.span {intEquivBot (p : ℤ)}
      rw [intEquivBot_natCast])).symm.trans (Int.quotientSpanNatEquivZMod p)

section FreeQuot

variable {A : Type*} [CommRing A] (I : Ideal A) {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem smul_top_eq_pi : (I • ⊤ : Submodule A (ι → A)) = Submodule.pi Set.univ fun _ : ι => (I : Submodule A A) := by
  apply le_antisymm
  · refine Submodule.smul_le.mpr fun a ha f _ => ?_
    rw [Submodule.mem_pi]
    intro i _
    exact I.mul_mem_right _ ha
  · intro f hf
    rw [Submodule.mem_pi] at hf
    have : f = ∑ i, f i • (Pi.single i 1 : ι → A) := by
      ext j; simp [Finset.sum_apply, Pi.single_apply]
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hf i (Set.mem_univ i)) Submodule.mem_top

theorem map_smul_top_equivFun {L : Type*} [AddCommGroup L] [Module A L] (b : Module.Basis ι A L) :
    Submodule.map (b.equivFun : L →ₗ[A] (ι → A)) (I • ⊤ : Submodule A L) = (I • ⊤ : Submodule A (ι → A)) := by
  rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]

noncomputable def quotSMulTopEquivPi {L : Type*} [AddCommGroup L] [Module A L] (b : Module.Basis ι A L) :
    (L ⧸ (I • ⊤ : Submodule A L)) ≃ₗ[A] (ι → A ⧸ I) :=
  (Submodule.Quotient.equiv (I • ⊤ : Submodule A L) (I • ⊤ : Submodule A (ι → A)) b.equivFun
      (map_smul_top_equivFun I b)).trans
    ((Submodule.quotEquivOfEq _ _ (smul_top_eq_pi I)).trans (Submodule.quotientPi _))

end FreeQuot

section Main

variable (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
  (H : Subgroup (ZMod M)ˣ)
  (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)

local notation "A" => (⊥ : Subring ℂ)
local notation "L" => CuspForm.twoCuspLattice M H 2 p (⊥ : Subring ℂ)
local notation "V" => CuspForm.IntTwoCuspForms M H p

include hpM2 hHp in

theorem exists_linearEquiv_fin :
    ∃ n : ℕ, Module.finrank ℂ (CuspForm (CohCarrier.GammaH M H) 2) = n ∧ Nonempty (V ≃ₗ[ZMod p] (Fin n → ZMod p)) := by
  classical
  obtain ⟨n, b, hli, hspan, hlat⟩ :=
    CuspForm.exists_linearIndependent_forall_twoCuspLattice_eq_span p M hpM hpM2 H hHp
  refine ⟨n, ?_, ?_⟩
  · rw [Module.finrank_eq_card_basis (Module.Basis.mk hli (by rw [hspan])), Fintype.card_fin]

  have hliA : LinearIndependent A b :=
    hli.restrict_scalars (by
      intro x y hxy
      apply Subtype.ext
      simpa [Algebra.smul_def] using hxy)
  let bS : Module.Basis (Fin n) A ↥(Submodule.span A (Set.range b)) := Module.Basis.span hliA
  let bL : Module.Basis (Fin n) A ↥L := bS.map (LinearEquiv.ofEq _ _ (hlat A).symm)

  let e1 : V ≃+ (Fin n → A ⧸ CuspForm.intIdeal p) :=
    ((CuspForm.IntTwoCuspForms.equivTwoCuspForms M H p).trans
      (quotSMulTopEquivPi (CuspForm.intIdeal p) bL).toAddEquiv)
  let e2 : V ≃+ (Fin n → ZMod p) := e1.trans (AddEquiv.piCongrRight fun _ => (botQuotEquivZMod p).toAddEquiv)
  exact ⟨{ e2.toAddMonoidHom.toZModLinearMap p with
      invFun := e2.symm, left_inv := e2.left_inv, right_inv := e2.right_inv }⟩

include hpM2 hHp in
theorem main (K : Type*) [Field K] [Algebra (ZMod p) K] :
    FiniteDimensional K (K ⊗[ZMod p] V) ∧
      Module.finrank K (K ⊗[ZMod p] V) = Module.finrank ℂ (CuspForm (CohCarrier.GammaH M H) 2) := by
  obtain ⟨n, hn, ⟨e⟩⟩ := exists_linearEquiv_fin p M hpM hpM2 H hHp
  haveI : Module.Free (ZMod p) V := Module.Free.of_equiv e.symm
  haveI : Module.Finite (ZMod p) V := Module.Finite.equiv e.symm
  have hV : Module.finrank (ZMod p) V = n := by rw [e.finrank_eq, Module.finrank_fin_fun]
  refine ⟨inferInstance, ?_⟩
  rw [Module.finrank_baseChange, hV, hn]

end Main

end CuspForm.SrcRank
p2m_reactivate "P2MW.S_CuspForm_finiteDimensional_and_finrank_tensorProduct_intTwoCuspForms_eq_finrank_cuspForm.CuspForm P2MW.S_CuspForm_finiteDimensional_and_finrank_tensorProduct_intTwoCuspForms_eq_finrank_cuspForm.CuspForm.SrcRank"
p2m_reactivate "P2MW.S_CuspForm_finiteDimensional_and_finrank_tensorProduct_intTwoCuspForms_eq_finrank_cuspForm.CuspForm"

open _root_.CuspForm _root_.P2MW.S_CuspForm_finiteDimensional_and_finrank_tensorProduct_intTwoCuspForms_eq_finrank_cuspForm.CuspForm CuspForm.SrcRank in

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (K : Type*) [Field K] [Algebra (ZMod p) K] :
    FiniteDimensional K (K ⊗[ZMod p] CuspForm.IntTwoCuspForms M H p) ∧
      Module.finrank K (K ⊗[ZMod p] CuspForm.IntTwoCuspForms M H p) = Module.finrank ℂ (CuspForm (CohCarrier.GammaH M H) 2) :=
  CuspForm.SrcRank.main p M hpM hpM2 H hHp K

end S_CuspForm_finiteDimensional_and_finrank_tensorProduct_intTwoCuspForms_eq_finrank_cuspForm
end P2MW
export P2MW.S_CuspForm_finiteDimensional_and_finrank_tensorProduct_intTwoCuspForms_eq_finrank_cuspForm (solution)
