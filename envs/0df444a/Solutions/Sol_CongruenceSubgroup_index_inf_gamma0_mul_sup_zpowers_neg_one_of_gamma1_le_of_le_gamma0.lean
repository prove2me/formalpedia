-- Prove2me | solution 1 for CongruenceSubgroup.index_inf_gamma0_mul_sup_zpowers_neg_one_of_gamma1_le_of_le_gamma0
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/855234fd-e273-5c29-9dd6-8645c07f333a

import Mathlib
import Theorems.Thm_CongruenceSubgroup_relIndex_gamma0_mul_of_prime_of_not_dvd
import Theorems.Thm_CongruenceSubgroup_relIndex_gamma1_inf_gamma0_mul_of_dvd
import Theorems.Thm_ModularCurve_surjective_specialLinearGroup_map_zmod
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CongruenceSubgroup_index_inf_gamma0_mul_sup_zpowers_neg_one_of_gamma1_le_of_le_gamma0
p2m_attr_erase "instance" "ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.Affine.Point.instFinite instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.intSeriesC_one ModularCurve.JOne.torsionGaloisRep_apply ModularCurve.coe_restrictForm ModularCurve.intSeriesC_zero ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring ModularCurve.jqNModC_one ModularCurve.qExpandAlgHomC_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero"
p2m_attr_erase "simp" "ModularForm.val_upperTriangularGL FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false

open scoped MatrixGroups

namespace SignIndex

open CongruenceSubgroup

theorem relIndex_eq_of_transitive {G : Type*} [Group G] {K G' G₀ H : Subgroup G}
    (hKG' : K ≤ G') (hG'G : G' ≤ G₀)
    (htrans : ∀ g ∈ G₀, ∃ k ∈ K, k⁻¹ * g ∈ H) (hfin : H.relIndex G₀ ≠ 0) :
    H.relIndex G' = H.relIndex G₀ := by
  apply le_antisymm (Subgroup.relIndex_le_of_le_right hG'G hfin)

  have hKG : K ≤ G₀ := hKG'.trans hG'G
  have hfinG' : H.relIndex G' ≠ 0 := fun h => hfin (Subgroup.relIndex_eq_zero_of_le_right hG'G h)
  have hfinK : H.relIndex K ≠ 0 := fun h => hfin (Subgroup.relIndex_eq_zero_of_le_right hKG h)
  have hsurj : Function.Surjective (Subgroup.quotientSubgroupOfEmbeddingOfLE H hKG) := by
    rintro ⟨g⟩
    obtain ⟨k, hk, hkg⟩ := htrans g g.2
    refine ⟨(QuotientGroup.mk ⟨k, hk⟩ : K ⧸ H.subgroupOf K), ?_⟩
    rw [Subgroup.quotientSubgroupOfEmbeddingOfLE_apply_mk]
    show (QuotientGroup.mk (Subgroup.inclusion hKG ⟨k, hk⟩) : G₀ ⧸ H.subgroupOf G₀) = QuotientGroup.mk g
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    exact hkg
  haveI : Finite (K ⧸ H.subgroupOf K) := Nat.finite_of_card_ne_zero hfinK
  calc H.relIndex G₀ = Nat.card (G₀ ⧸ H.subgroupOf G₀) := rfl
    _ ≤ Nat.card (K ⧸ H.subgroupOf K) := Finite.card_le_of_surjective' hsurj (fun h => absurd h hfinK)
    _ = H.relIndex K := rfl
    _ ≤ H.relIndex G' := Subgroup.relIndex_le_of_le_right hKG' hfinG'

theorem intCast_eq_zero_mul_iff_of_coprime {L ℓ : ℕ} (h : L.Coprime ℓ) (z : ℤ) :
    ((z : ℤ) : ZMod (L * ℓ)) = 0 ↔ ((z : ℤ) : ZMod L) = 0 ∧ ((z : ℤ) : ZMod ℓ) = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, ZMod.intCast_zmod_eq_zero_iff_dvd, ZMod.intCast_zmod_eq_zero_iff_dvd,
    Nat.cast_mul]
  constructor
  · intro hd; exact ⟨dvd_trans (dvd_mul_right _ _) hd, dvd_trans (dvd_mul_left _ _) hd⟩
  · rintro ⟨h1, h2⟩; exact (Nat.isCoprime_iff_coprime.mpr h).mul_dvd h1 h2

theorem mem_gamma0_mul_of_coprime {L ℓ : ℕ} (h : L.Coprime ℓ) {g : SL(2, ℤ)}
    (hL : g ∈ Gamma0 L) (hℓ : g ∈ Gamma0 ℓ) : g ∈ Gamma0 (L * ℓ) := by
  rw [Gamma0_mem] at hL hℓ ⊢
  exact (intCast_eq_zero_mul_iff_of_coprime h _).mpr ⟨hL, hℓ⟩

theorem transitive_of_not_dvd (L ℓ : ℕ) [NeZero L] (hℓ : ℓ.Prime) (hℓL : ¬ ℓ ∣ L)
    (g : SL(2, ℤ)) (hg : g ∈ Gamma0 L) : ∃ γ ∈ Gamma1 L, γ⁻¹ * g ∈ Gamma0 (L * ℓ) := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  haveI : NeZero (L * ℓ) := ⟨mul_ne_zero (NeZero.ne L) hℓ.ne_zero⟩
  have hcop : L.Coprime ℓ := (Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓL |>.symm

  let e : ZMod (L * ℓ) ≃+* ZMod L × ZMod ℓ := ZMod.chineseRemainder hcop
  let gℓ : SL(2, ZMod ℓ) := Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod ℓ)) g
  let P : Matrix (Fin 2) (Fin 2) (ZMod L × ZMod ℓ) :=
    Matrix.of fun i j => ((1 : Matrix (Fin 2) (Fin 2) (ZMod L)) i j, (gℓ : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) i j)
  have hPfst : P.map (RingHom.fst (ZMod L) (ZMod ℓ)) = 1 := by
    ext i j; rfl
  have hPsnd : P.map (RingHom.snd (ZMod L) (ZMod ℓ)) = (gℓ : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) := by
    ext i j; rfl
  have hPdet : P.det = 1 := by
    apply Prod.ext
    · have := RingHom.map_det (RingHom.fst (ZMod L) (ZMod ℓ)) P
      rw [RingHom.mapMatrix_apply, hPfst, Matrix.det_one] at this
      exact this
    · have := RingHom.map_det (RingHom.snd (ZMod L) (ZMod ℓ)) P
      rw [RingHom.mapMatrix_apply, hPsnd, Matrix.SpecialLinearGroup.det_coe] at this
      exact this
  let t : SL(2, ZMod (L * ℓ)) := Matrix.SpecialLinearGroup.map e.symm.toRingHom ⟨P, hPdet⟩
  obtain ⟨γ, hγ⟩ := ModularCurve.surjective_specialLinearGroup_map_zmod (L * ℓ) t
  have hfst : (RingHom.fst (ZMod L) (ZMod ℓ)).comp e.toRingHom = ZMod.castHom (dvd_mul_right L ℓ) (ZMod L) :=
    Subsingleton.elim _ _
  have hsnd : (RingHom.snd (ZMod L) (ZMod ℓ)).comp e.toRingHom = ZMod.castHom (dvd_mul_left ℓ L) (ZMod ℓ) :=
    Subsingleton.elim _ _

  have ht : ∀ i j, e ((t : Matrix (Fin 2) (Fin 2) (ZMod (L * ℓ))) i j) =
      ((1 : Matrix (Fin 2) (Fin 2) (ZMod L)) i j, (gℓ : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) i j) := by
    intro i j
    show e (e.symm.toRingHom (P i j)) = _
    rw [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.apply_symm_apply]
    rfl
  have hγL : ∀ i j, (((γ : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod L) = (1 : Matrix (Fin 2) (Fin 2) (ZMod L)) i j := by
    intro i j
    have h1 : (((γ : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod (L * ℓ)) = (t : Matrix (Fin 2) (Fin 2) (ZMod (L * ℓ))) i j := by
      have := congrArg (fun s : SL(2, ZMod (L * ℓ)) => (s : Matrix (Fin 2) (Fin 2) (ZMod (L * ℓ))) i j) hγ
      simpa using this
    have h2 := congrArg Prod.fst (ht i j)
    rw [← h1] at h2

    have h3 : (e ((((γ : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod (L * ℓ)))).1 =
        ZMod.castHom (dvd_mul_right L ℓ) (ZMod L) ((((γ : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod (L * ℓ))) :=
      RingHom.congr_fun hfst _
    rw [h3, map_intCast] at h2
    exact h2
  have hγℓ : ∀ i j, (((γ : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod ℓ) = (gℓ : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) i j := by
    intro i j
    have h1 : (((γ : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod (L * ℓ)) = (t : Matrix (Fin 2) (Fin 2) (ZMod (L * ℓ))) i j := by
      have := congrArg (fun s : SL(2, ZMod (L * ℓ)) => (s : Matrix (Fin 2) (Fin 2) (ZMod (L * ℓ))) i j) hγ
      simpa using this
    have h2 := congrArg Prod.snd (ht i j)
    rw [← h1] at h2
    have h3 : (e ((((γ : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod (L * ℓ)))).2 =
        ZMod.castHom (dvd_mul_left ℓ L) (ZMod ℓ) ((((γ : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod (L * ℓ))) :=
      RingHom.congr_fun hsnd _
    rw [h3, map_intCast] at h2
    exact h2

  have hγΓ : γ ∈ Gamma L := by
    rw [Gamma_mem]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hγL]; simp
    · rw [hγL]; simp
    · rw [hγL]; simp
    · rw [hγL]; simp
  have hγ1 : γ ∈ Gamma1 L := by
    rw [Gamma_mem] at hγΓ
    rw [Gamma1_mem]
    exact ⟨hγΓ.1, hγΓ.2.2.2, hγΓ.2.2.1⟩
  refine ⟨γ, hγ1, ?_⟩

  have hmodℓ : Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod ℓ)) γ = gℓ := by
    ext i j
    exact hγℓ i j
  have hker : γ⁻¹ * g ∈ Gamma ℓ := by
    show γ⁻¹ * g ∈ (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod ℓ))).ker
    rw [MonoidHom.mem_ker, map_mul, map_inv, hmodℓ, inv_mul_cancel]
  have h0ℓ : γ⁻¹ * g ∈ Gamma0 ℓ := by
    rw [Gamma_mem] at hker
    rw [Gamma0_mem]
    exact hker.2.2.1
  have h0L : γ⁻¹ * g ∈ Gamma0 L :=
    (Gamma0 L).mul_mem ((Gamma0 L).inv_mem (Gamma1_in_Gamma0 L hγ1)) hg
  exact mem_gamma0_mul_of_coprime hcop h0L h0ℓ

theorem transitive_of_dvd (L ℓ : ℕ) [NeZero L] (hℓ : ℓ.Prime) (hℓL : ℓ ∣ L)
    (g : SL(2, ℤ)) (hg : g ∈ Gamma0 L) : ∃ γ ∈ Gamma1 L, γ⁻¹ * g ∈ Gamma0 (L * ℓ) := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hg
  obtain ⟨c', hc'⟩ := hg

  have hdet := Matrix.SpecialLinearGroup.det_coe g
  rw [Matrix.det_fin_two] at hdet
  have ha : ((g 0 0 : ℤ) : ZMod ℓ) ≠ 0 := by
    intro ha
    have h := congrArg (fun z : ℤ => (z : ZMod ℓ)) hdet
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_one, ha, zero_mul, zero_sub] at h
    rw [hc', Int.cast_mul, Int.cast_natCast, (ZMod.natCast_eq_zero_iff L ℓ).mpr hℓL, zero_mul, mul_zero, neg_zero] at h
    exact zero_ne_one h
  let j : ℤ := (((c' : ZMod ℓ) * ((g 0 0 : ℤ) : ZMod ℓ)⁻¹).val : ℤ)
  have hj : ((c' - j * g 0 0 : ℤ) : ZMod ℓ) = 0 := by
    simp only [j, Int.cast_sub, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
    rw [inv_mul_cancel_right₀ ha, sub_self]

  let γ : SL(2, ℤ) := ⟨!![1, 0; (L : ℤ) * j, 1], by rw [Matrix.det_fin_two_of]; ring⟩
  have hh_det : Matrix.det !![g 0 0, g 0 1; g 1 0 - (L : ℤ) * j * g 0 0, g 1 1 - (L : ℤ) * j * g 0 1] = 1 := by
    rw [Matrix.det_fin_two_of]; linear_combination hdet
  let h : SL(2, ℤ) := ⟨_, hh_det⟩
  have hγh : γ * h = g := by
    ext i j'
    fin_cases i <;> fin_cases j' <;>
      simp [γ, h, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  refine ⟨γ, ?_, ?_⟩
  · rw [Gamma1_mem]
    refine ⟨?_, ?_, ?_⟩ <;> simp [γ]
  · rw [show γ⁻¹ * g = h by rw [← hγh, inv_mul_cancel_left], Gamma0_mem]
    show (((g 1 0 - (L : ℤ) * j * g 0 0 : ℤ)) : ZMod (L * ℓ)) = 0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, hc', show (L : ℤ) * c' - (L : ℤ) * j * g 0 0 = (L : ℤ) * (c' - j * g 0 0) by ring,
      Nat.cast_mul]
    exact mul_dvd_mul_left _ ((ZMod.intCast_zmod_eq_zero_iff_dvd _ ℓ).mp hj)

theorem transitive (L ℓ : ℕ) [NeZero L] (hℓ : ℓ.Prime) (g : SL(2, ℤ)) (hg : g ∈ Gamma0 L) :
    ∃ γ ∈ Gamma1 L, γ⁻¹ * g ∈ Gamma0 (L * ℓ) := by
  by_cases hd : ℓ ∣ L
  · exact transitive_of_dvd L ℓ hℓ hd g hg
  · exact transitive_of_not_dvd L ℓ hℓ hd g hg

theorem neg_one_mem_gamma0 (N : ℕ) : (-1 : SL(2, ℤ)) ∈ Gamma0 N := by
  rw [Gamma0_mem]; simp [Matrix.SpecialLinearGroup.coe_neg]

theorem relIndex_gamma0_mul_eq (L ℓ : ℕ) [NeZero L] (hℓ : ℓ.Prime) (G' : Subgroup SL(2, ℤ))
    (h1 : Gamma1 L ≤ G') (h0 : G' ≤ Gamma0 L) :
    (Gamma0 (L * ℓ)).relIndex G' = if ℓ ∣ L then ℓ else ℓ + 1 := by
  haveI : NeZero (L * ℓ) := ⟨mul_ne_zero (NeZero.ne L) hℓ.ne_zero⟩
  have hle : Gamma0 (L * ℓ) ≤ Gamma0 L := fun g hg => by
    rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hg ⊢
    exact dvd_trans (by rw [Nat.cast_mul]; exact dvd_mul_right _ _) hg
  have hfin : (Gamma0 (L * ℓ)).relIndex (Gamma0 L) ≠ 0 := by
    intro h
    have := Subgroup.relIndex_mul_index hle
    rw [h, zero_mul] at this
    exact Subgroup.FiniteIndex.index_ne_zero this.symm
  have key := relIndex_eq_of_transitive h1 h0 (transitive L ℓ hℓ) hfin
  rw [key]
  split_ifs with hd
  · have k1 := relIndex_eq_of_transitive (le_refl (Gamma1 L)) (Gamma1_in_Gamma0 L) (transitive L ℓ hℓ) hfin
    rw [← k1, ← Subgroup.inf_relIndex_left]
    exact relIndex_gamma1_inf_gamma0_mul_of_dvd L ℓ hd
  · exact relIndex_gamma0_mul_of_prime_of_not_dvd L ℓ hℓ hd

theorem mem_or_neg_mem_of_mem_sup (X : Subgroup SL(2, ℤ)) {γ : SL(2, ℤ)}
    (hγ : γ ∈ X ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) : γ ∈ X ∨ -γ ∈ X := by
  rw [Subgroup.sup_eq_closure] at hγ
  induction hγ using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact Or.inl hx
    · have hx1 : x = 1 ∨ x = -1 := by
        have hx' : x ∈ Subgroup.closure {(-1 : SL(2, ℤ))} := by
          rw [← Subgroup.zpowers_eq_closure]; exact hx
        clear hx
        induction hx' using Subgroup.closure_induction with
        | mem y hy => exact Or.inr hy
        | one => exact Or.inl rfl
        | mul y z _ _ hy hz =>
          rcases hy with rfl | rfl <;> rcases hz with rfl | rfl
          · exact Or.inl (one_mul 1)
          · exact Or.inr (one_mul _)
          · exact Or.inr (mul_one _)
          · left; rw [neg_mul_neg, one_mul]
        | inv y _ hy =>
          rcases hy with rfl | rfl
          · exact Or.inl inv_one
          · right; rw [← neg_inv, inv_one]
      rcases hx1 with rfl | rfl
      · exact Or.inl X.one_mem
      · right; rw [neg_neg]; exact X.one_mem
  | one => exact Or.inl X.one_mem
  | mul x y _ _ hx hy =>
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact Or.inl (X.mul_mem hx hy)
    · right; rw [← mul_neg]; exact X.mul_mem hx hy
    · right; rw [← neg_mul]; exact X.mul_mem hx hy
    · left; rw [← neg_mul_neg]; exact X.mul_mem hx hy
  | inv x _ hx =>
    rcases hx with hx | hx
    · exact Or.inl (X.inv_mem hx)
    · right; rw [neg_inv]; exact X.inv_mem hx

theorem inf_sup_zpowers_neg_one (Γ H : Subgroup SL(2, ℤ)) (hH : (-1 : SL(2, ℤ)) ∈ H) :
    (Γ ⊓ H) ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) = (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) ⊓ H := by
  apply le_antisymm
  · exact sup_le (inf_le_inf_right H le_sup_left) (le_inf le_sup_right ((Subgroup.zpowers_le).mpr hH))
  · rintro x ⟨hx, hxH⟩
    rcases mem_or_neg_mem_of_mem_sup Γ hx with h | h
    · exact Subgroup.mem_sup_left ⟨h, hxH⟩
    · have hnegH : -x ∈ H := by
        have := H.mul_mem hH hxH
        rwa [neg_one_mul] at this
      have : x = (-x) * (-1) := by rw [mul_neg_one, neg_neg]
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨h, hnegH⟩) (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))

end SignIndex

open SignIndex CongruenceSubgroup in
theorem solution
    (L : ℕ) [NeZero L] (Γ : Subgroup SL(2, ℤ))
    (hΓ₁ : CongruenceSubgroup.Gamma1 L ≤ Γ) (hΓ₀ : Γ ≤ CongruenceSubgroup.Gamma0 L)
    (ℓ : ℕ) (hℓ : ℓ.Prime) :
    ((Γ ⊓ CongruenceSubgroup.Gamma0 (L * ℓ)) ⊔ Subgroup.zpowers (-1)).index =
      (Γ ⊔ Subgroup.zpowers (-1)).index * (if ℓ ∣ L then ℓ else ℓ + 1) := by
  rw [inf_sup_zpowers_neg_one Γ _ (neg_one_mem_gamma0 _),
    ← Subgroup.relIndex_mul_index (inf_le_left : (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) ⊓ Gamma0 (L * ℓ) ≤ _),
    Subgroup.inf_relIndex_left, mul_comm]
  congr 1
  exact relIndex_gamma0_mul_eq L ℓ hℓ _ (hΓ₁.trans le_sup_left)
    (sup_le hΓ₀ ((Subgroup.zpowers_le).mpr (neg_one_mem_gamma0 L)))

end S_CongruenceSubgroup_index_inf_gamma0_mul_sup_zpowers_neg_one_of_gamma1_le_of_le_gamma0
end P2MW
export P2MW.S_CongruenceSubgroup_index_inf_gamma0_mul_sup_zpowers_neg_one_of_gamma1_le_of_le_gamma0 (solution)
