-- Prove2me | solution 1 for CerednikDrinfeld.HeckeTower.correspondence_eq_of_support_eq_of_finrankAlong_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/5badb0bd-b760-5e47-96a0-051afb9968ec

import Definitions.Def_CerednikDrinfeld_HeckeTower
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_separableAlong_of_charZero
import Theorems.Thm_AlgebraicCurve_finrankAlong_comp
import Theorems.Thm_AlgebraicCurve_Divisor_correspondence_eq_finrankAlong_smul_correspondence_of_comp_eq
import Theorems.Thm_AlgebraicCurve_exists_ringEquiv_closure_of_support_correspondence_single_eq_of_essFiniteType
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_HeckeTower_correspondence_eq_of_support_eq_of_finrankAlong_eq
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false

open CerednikDrinfeld AlgebraicCurve

theorem solution
    {q q' : ℕ} (F₀ : Type) [Field F₀] [Algebra (AlgebraicClosure ℚ) F₀] [IsCurveOver (AlgebraicClosure ℚ) F₀]
    (𝕋 𝕋' : HeckeTower.TowerData q q' F₀)

    (hsupp : ∀ (ℓ : HeckeTower.AwayPrime q q') (P : Place (AlgebraicClosure ℚ) F₀),
      (Divisor.correspondence (𝕋.φ (ℓ, 0)) (𝕋.φ (ℓ, 1)) (𝕋.integral (ℓ, 0)) (𝕋.integral (ℓ, 1)) (Finsupp.single P 1)).support =
        (Divisor.correspondence (𝕋'.φ (ℓ, 0)) (𝕋'.φ (ℓ, 1)) (𝕋'.integral (ℓ, 0)) (𝕋'.integral (ℓ, 1)) (Finsupp.single P 1)).support)

    (hdeg : ∀ α : HeckeTower.Arr q q', finrankAlong (AlgebraicClosure ℚ) (𝕋.φ α) = finrankAlong (AlgebraicClosure ℚ) (𝕋'.φ α))

    (hgen : ∀ ℓ : HeckeTower.AwayPrime q q',
      Subfield.closure (Set.range (𝕋'.φ (ℓ, 0)) ∪ Set.range (𝕋'.φ (ℓ, 1))) = ⊤) :
    ∀ (ℓ : HeckeTower.AwayPrime q q') (D : Divisor (AlgebraicClosure ℚ) F₀),
      Divisor.correspondence (𝕋.φ (ℓ, 0)) (𝕋.φ (ℓ, 1)) (𝕋.integral (ℓ, 0)) (𝕋.integral (ℓ, 1)) D =
        Divisor.correspondence (𝕋'.φ (ℓ, 0)) (𝕋'.φ (ℓ, 1)) (𝕋'.integral (ℓ, 0)) (𝕋'.integral (ℓ, 1)) D := by
  intro ℓ D

  set E := Subfield.closure (Set.range (𝕋.φ (ℓ, 0)) ∪ Set.range (𝕋.φ (ℓ, 1))) with hE
  set E' := Subfield.closure (Set.range (𝕋'.φ (ℓ, 0)) ∪ Set.range (𝕋'.φ (ℓ, 1))) with hE'

  obtain ⟨θ, hθ₀, hθ₁⟩ := AlgebraicCurve.exists_ringEquiv_closure_of_support_correspondence_single_eq_of_essFiniteType
    (AlgebraicClosure ℚ) F₀ (𝕋.F ℓ) (𝕋'.F ℓ) (𝕋.φ (ℓ, 0)) (𝕋.φ (ℓ, 1)) (𝕋.integral (ℓ, 0)) (𝕋.integral (ℓ, 1))
    (𝕋.finite (ℓ, 0)) (𝕋.finite (ℓ, 1))
    (𝕋'.φ (ℓ, 0)) (𝕋'.φ (ℓ, 1)) (𝕋'.integral (ℓ, 0)) (𝕋'.integral (ℓ, 1)) (𝕋'.finite (ℓ, 0)) (𝕋'.finite (ℓ, 1)) (hsupp ℓ)

  have hmem : ∀ y : 𝕋'.F ℓ, y ∈ E' := fun y => by rw [hE', hgen ℓ]; exact Subfield.mem_top y
  have hιθ : ∀ e : ↥E, ((θ.symm ⟨(θ e : 𝕋'.F ℓ), hmem _⟩ : ↥E) : 𝕋.F ℓ) = (e : 𝕋.F ℓ) := fun e => by
    have : (⟨(θ e : 𝕋'.F ℓ), hmem _⟩ : ↥E') = θ e := Subtype.ext rfl
    rw [this, RingEquiv.symm_apply_apply]
  let ιr : 𝕋'.F ℓ →+* 𝕋.F ℓ :=
    { toFun := fun y => ((θ.symm ⟨y, hmem y⟩ : ↥E) : 𝕋.F ℓ)
      map_one' := by
        have : (⟨1, hmem 1⟩ : ↥E') = 1 := rfl
        simp only [this, map_one]; rfl
      map_mul' := fun y z => by
        have : (⟨y * z, hmem (y * z)⟩ : ↥E') = ⟨y, hmem y⟩ * ⟨z, hmem z⟩ := rfl
        simp only [this, map_mul]; rfl
      map_zero' := by
        have : (⟨0, hmem 0⟩ : ↥E') = 0 := rfl
        simp only [this, map_zero]; rfl
      map_add' := fun y z => by
        have : (⟨y + z, hmem (y + z)⟩ : ↥E') = ⟨y, hmem y⟩ + ⟨z, hmem z⟩ := rfl
        simp only [this, map_add]; rfl }
  have hιr : ∀ y, ιr y = ((θ.symm ⟨y, hmem y⟩ : ↥E) : 𝕋.F ℓ) := fun y => rfl
  have hι₀ : ∀ x : F₀, ιr (𝕋'.φ (ℓ, 0) x) = 𝕋.φ (ℓ, 0) x := fun x => by
    rw [hιr]
    have hx : (⟨𝕋'.φ (ℓ, 0) x, hmem _⟩ : ↥E') =
        θ ⟨𝕋.φ (ℓ, 0) x, Subfield.subset_closure (Set.mem_union_left _ (Set.mem_range_self x))⟩ := Subtype.ext (hθ₀ x).symm
    rw [hx, RingEquiv.symm_apply_apply]
  have hι₁ : ∀ x : F₀, ιr (𝕋'.φ (ℓ, 1) x) = 𝕋.φ (ℓ, 1) x := fun x => by
    rw [hιr]
    have hx : (⟨𝕋'.φ (ℓ, 1) x, hmem _⟩ : ↥E') =
        θ ⟨𝕋.φ (ℓ, 1) x, Subfield.subset_closure (Set.mem_union_right _ (Set.mem_range_self x))⟩ := Subtype.ext (hθ₁ x).symm
    rw [hx, RingEquiv.symm_apply_apply]
  let ι : 𝕋'.F ℓ →ₐ[AlgebraicClosure ℚ] 𝕋.F ℓ :=
    { toRingHom := ιr
      commutes' := fun a => by
        show ιr (algebraMap (AlgebraicClosure ℚ) (𝕋'.F ℓ) a) = algebraMap (AlgebraicClosure ℚ) (𝕋.F ℓ) a
        rw [← (𝕋'.φ (ℓ, 0)).commutes a, hι₀, (𝕋.φ (ℓ, 0)).commutes a] }
  have h₀ : ι.comp (𝕋'.φ (ℓ, 0)) = 𝕋.φ (ℓ, 0) := AlgHom.ext (fun x => hι₀ x)
  have h₁ : ι.comp (𝕋'.φ (ℓ, 1)) = 𝕋.φ (ℓ, 1) := AlgHom.ext (fun x => hι₁ x)

  have hfinι : FiniteAlong (AlgebraicClosure ℚ) ι := by
    letI iψ : Algebra F₀ (𝕋'.F ℓ) := algebraAlong (𝕋'.φ (ℓ, 0))
    letI iι : Algebra (𝕋'.F ℓ) (𝕋.F ℓ) := algebraAlong ι
    letI iφ : Algebra F₀ (𝕋.F ℓ) := algebraAlong (𝕋.φ (ℓ, 0))
    haveI : IsScalarTower F₀ (𝕋'.F ℓ) (𝕋.F ℓ) := IsScalarTower.of_algebraMap_eq (fun x => (hι₀ x).symm)
    haveI : Module.Finite F₀ (𝕋.F ℓ) := 𝕋.finite (ℓ, 0)
    exact Module.Finite.of_restrictScalars_finite F₀ (𝕋'.F ℓ) (𝕋.F ℓ)
  have hintι : ι.toRingHom.IsIntegral := by
    have hc : (ι.toRingHom.comp (𝕋'.φ (ℓ, 0)).toRingHom).IsIntegral := by
      have : ι.toRingHom.comp (𝕋'.φ (ℓ, 0)).toRingHom = (𝕋.φ (ℓ, 0)).toRingHom := by rw [← h₀]; rfl
      rw [this]; exact 𝕋.integral (ℓ, 0)
    exact RingHom.IsIntegral.tower_top (𝕋'.φ (ℓ, 0)).toRingHom ι.toRingHom hc
  haveI : CharZero (𝕋'.F ℓ) := charZero_of_injective_algebraMap (algebraMap (AlgebraicClosure ℚ) (𝕋'.F ℓ)).injective
  have hsepι : SeparableAlong (AlgebraicClosure ℚ) ι := AlgebraicCurve.separableAlong_of_charZero ι hintι

  have hmult := AlgebraicCurve.Divisor.correspondence_eq_finrankAlong_smul_correspondence_of_comp_eq
    (𝕋.φ (ℓ, 0)) (𝕋.φ (ℓ, 1)) (𝕋.integral (ℓ, 0)) (𝕋.integral (ℓ, 1))
    (𝕋'.φ (ℓ, 0)) (𝕋'.φ (ℓ, 1)) (𝕋'.integral (ℓ, 0)) (𝕋'.integral (ℓ, 1)) ι hintι hfinι hsepι h₀ h₁ D

  have hd : finrankAlong (AlgebraicClosure ℚ) (𝕋.φ (ℓ, 0)) =
      finrankAlong (AlgebraicClosure ℚ) (𝕋'.φ (ℓ, 0)) * finrankAlong (AlgebraicClosure ℚ) ι := by
    rw [← h₀]; exact AlgebraicCurve.finrankAlong_comp (𝕋'.φ (ℓ, 0)) ι
  have hpos : 0 < finrankAlong (AlgebraicClosure ℚ) (𝕋'.φ (ℓ, 0)) := by
    letI := algebraAlong (𝕋'.φ (ℓ, 0))
    haveI : Module.Finite F₀ (𝕋'.F ℓ) := 𝕋'.finite (ℓ, 0)
    show 0 < Module.finrank F₀ (𝕋'.F ℓ)
    exact Module.finrank_pos
  have hm : finrankAlong (AlgebraicClosure ℚ) ι = 1 := by
    have h := hdeg (ℓ, 0)
    rw [hd] at h
    exact Nat.eq_of_mul_eq_mul_left hpos (h.trans (mul_one _).symm)
  rw [hmult, hm, one_smul]

end S_CerednikDrinfeld_HeckeTower_correspondence_eq_of_support_eq_of_finrankAlong_eq
end P2MW
export P2MW.S_CerednikDrinfeld_HeckeTower_correspondence_eq_of_support_eq_of_finrankAlong_eq (solution)
