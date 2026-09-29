-- Prove2me | solution 1 for CerednikDrinfeld.HeckeTower.exists_algEquiv_forall_comp_phi_eq_of_correspondence_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/afddeeea-c4cc-5b0a-8adb-74a4773eae2a

import Definitions.Def_CerednikDrinfeld_HeckeTower
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_exists_ringEquiv_closure_of_support_correspondence_single_eq_of_essFiniteType
import Theorems.Thm_AlgebraicCurve_Divisor_correspondence_eq_finrankAlong_smul_correspondence_of_comp_eq
import Theorems.Thm_AlgebraicCurve_fundamentalIdentityAlong
import Theorems.Thm_AlgebraicCurve_nonempty_place_of_transcendental_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_isCurveOver_iff_exists_transcendental_finiteDimensional
import Theorems.Thm_AlgebraicCurve_one_le_deg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_HeckeTower_exists_algEquiv_forall_comp_phi_eq_of_correspondence_eq
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum"
p2m_attr_erase "simp" "ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false
set_option maxHeartbeats 16000000

p2m_open "CerednikDrinfeld P2MW.S_CerednikDrinfeld_HeckeTower_exists_algEquiv_forall_comp_phi_eq_of_correspondence_eq.CerednikDrinfeld AlgebraicCurve"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "HeckeTower.AwayPrime HeckeTower.Arr HeckeTower.TowerData"
namespace TowerRider
p2m_open "CerednikDrinfeld"

theorem closure_range_union_eq_top_of_equiv {F₀ F F' : Type} [Field F] [Field F']
    (φ₀ φ₁ : F₀ → F) (φ'₀ φ'₁ : F₀ → F') (θ : F ≃+* F')
    (hθ₀ : ∀ x : F₀, θ (φ₀ x) = φ'₀ x) (hθ₁ : ∀ x : F₀, θ (φ₁ x) = φ'₁ x)
    (hgen' : Subfield.closure (Set.range φ'₀ ∪ Set.range φ'₁) = ⊤) :
    Subfield.closure (Set.range φ₀ ∪ Set.range φ₁) = ⊤ := by
  have himg : θ.toRingHom '' (Set.range φ₀ ∪ Set.range φ₁) = Set.range φ'₀ ∪ Set.range φ'₁ := by
    ext y; constructor
    · rintro ⟨x, (⟨z, rfl⟩ | ⟨z, rfl⟩), rfl⟩
      · exact Or.inl ⟨z, (hθ₀ z).symm⟩
      · exact Or.inr ⟨z, (hθ₁ z).symm⟩
    · rintro (⟨z, rfl⟩ | ⟨z, rfl⟩)
      · exact ⟨φ₀ z, Or.inl ⟨z, rfl⟩, hθ₀ z⟩
      · exact ⟨φ₁ z, Or.inr ⟨z, rfl⟩, hθ₁ z⟩
  rw [eq_top_iff]
  intro y _
  have hy : θ y ∈ (Subfield.closure (Set.range φ₀ ∪ Set.range φ₁)).map θ.toRingHom := by
    rw [RingHom.map_field_closure, himg, hgen']; trivial
  obtain ⟨y', hy', hyy⟩ := hy
  rwa [← θ.injective hyy]

theorem equiv_comp_eq_comp_equiv {F₀ F F' : Type} [Field F] [Field F']
    (φ₀ φ₁ : F₀ → F) (φ'₀ φ'₁ : F₀ → F') (θ : F ≃+* F')
    (hθ₀ : ∀ x : F₀, θ (φ₀ x) = φ'₀ x) (hθ₁ : ∀ x : F₀, θ (φ₁ x) = φ'₁ x)
    (hgen' : Subfield.closure (Set.range φ'₀ ∪ Set.range φ'₁) = ⊤)
    (g₀ : F₀ → F₀) (g : F →+* F) (g' : F' →+* F')
    (hg₀ : ∀ x : F₀, g (φ₀ x) = φ₀ (g₀ x)) (hg₁ : ∀ x : F₀, g (φ₁ x) = φ₁ (g₀ x))
    (hg'₀ : ∀ x : F₀, g' (φ'₀ x) = φ'₀ (g₀ x)) (hg'₁ : ∀ x : F₀, g' (φ'₁ x) = φ'₁ (g₀ x)) :
    ∀ y : F, θ (g y) = g' (θ y) := by
  have hgen := closure_range_union_eq_top_of_equiv φ₀ φ₁ φ'₀ φ'₁ θ hθ₀ hθ₁ hgen'
  have hagree : (Set.range φ₀ ∪ Set.range φ₁).EqOn (θ.toRingHom.comp g) (g'.comp θ.toRingHom) := by
    rintro y (⟨x, rfl⟩ | ⟨x, rfl⟩)
    · show θ (g (φ₀ x)) = g' (θ (φ₀ x))
      rw [hg₀, hθ₀, hθ₀, hg'₀]
    · show θ (g (φ₁ x)) = g' (θ (φ₁ x))
      rw [hg₁, hθ₁, hθ₁, hg'₁]
  have heq := RingHom.eq_of_eqOn_of_field_closure_eq_top hgen hagree
  intro y
  exact congrArg (fun h : F →+* F' => h y) heq

end CerednikDrinfeld.TowerRider

namespace HeckeR2
open AlgebraicCurve

variable {K : Type} [Field K]

theorem nonempty_place (F : Type) [Field F] [Algebra K F] [PerfectField K] [IsCurveOver K F] [Algebra.EssFiniteType K F] :
    Nonempty (Place K F) := by
  obtain ⟨t, ht, hfin, hsep⟩ := (AlgebraicCurve.isCurveOver_iff_exists_transcendental_finiteDimensional (K := K) (F := F)).1 inferInstance
  haveI := hsep
  exact AlgebraicCurve.nonempty_place_of_transcendental_of_finiteDimensional K t ht hfin

end HeckeR2

theorem solution
    {q q' : ℕ} (F₀ : Type) [Field F₀] [Algebra (AlgebraicClosure ℚ) F₀] [IsCurveOver (AlgebraicClosure ℚ) F₀]
    (𝕋 𝕋' : HeckeTower.TowerData q q' F₀)

    (hcorr : ∀ (ℓ : HeckeTower.AwayPrime q q') (D : Divisor (AlgebraicClosure ℚ) F₀),
      Divisor.correspondence (𝕋.φ (ℓ, 0)) (𝕋.φ (ℓ, 1)) (𝕋.integral (ℓ, 0)) (𝕋.integral (ℓ, 1)) D =
        Divisor.correspondence (𝕋'.φ (ℓ, 0)) (𝕋'.φ (ℓ, 1)) (𝕋'.integral (ℓ, 0)) (𝕋'.integral (ℓ, 1)) D)

    (hgen : ∀ ℓ : HeckeTower.AwayPrime q q',
      Subfield.closure (Set.range (𝕋'.φ (ℓ, 0)) ∪ Set.range (𝕋'.φ (ℓ, 1))) = ⊤) :
    ∃ θ : ∀ ℓ : HeckeTower.AwayPrime q q', 𝕋.F ℓ ≃ₐ[AlgebraicClosure ℚ] 𝕋'.F ℓ,
      (∀ (α : HeckeTower.Arr q q') (x : F₀), θ α.1 (𝕋.φ α x) = 𝕋'.φ α x) ∧
      (∀ (S : Type) (g₀ : S → SemilinearAut (AlgebraicClosure ℚ) F₀)
         (g : ∀ ℓ : HeckeTower.AwayPrime q q', S → SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))
         (g' : ∀ ℓ : HeckeTower.AwayPrime q q', S → SemilinearAut (AlgebraicClosure ℚ) (𝕋'.F ℓ)),
         (∀ (α : HeckeTower.Arr q q') (σ : S) (x : F₀), g α.1 σ • 𝕋.φ α x = 𝕋.φ α (g₀ σ • x)) →
         (∀ (α : HeckeTower.Arr q q') (σ : S) (x : F₀), g' α.1 σ • 𝕋'.φ α x = 𝕋'.φ α (g₀ σ • x)) →
         ∀ (ℓ : HeckeTower.AwayPrime q q') (σ : S) (y : 𝕋.F ℓ), θ ℓ (g ℓ σ • y) = g' ℓ σ • θ ℓ y) := by
  classical

  have main : ∀ ℓ : HeckeTower.AwayPrime q q', ∃ θ : 𝕋.F ℓ ≃ₐ[AlgebraicClosure ℚ] 𝕋'.F ℓ,
      ∀ (i : Fin 2) (x : F₀), θ (𝕋.φ (ℓ, i) x) = 𝕋'.φ (ℓ, i) x := by
    intro ℓ

    obtain ⟨θ₀, hθ₀₀, hθ₀₁⟩ := AlgebraicCurve.exists_ringEquiv_closure_of_support_correspondence_single_eq_of_essFiniteType
      (AlgebraicClosure ℚ) F₀ (𝕋.F ℓ) (𝕋'.F ℓ) (𝕋.φ (ℓ, 0)) (𝕋.φ (ℓ, 1)) (𝕋.integral (ℓ, 0)) (𝕋.integral (ℓ, 1))
      (𝕋.finite (ℓ, 0)) (𝕋.finite (ℓ, 1)) (𝕋'.φ (ℓ, 0)) (𝕋'.φ (ℓ, 1)) (𝕋'.integral (ℓ, 0)) (𝕋'.integral (ℓ, 1))
      (𝕋'.finite (ℓ, 0)) (𝕋'.finite (ℓ, 1)) (fun P => by rw [hcorr ℓ])

    have hmem' : ∀ y : 𝕋'.F ℓ, y ∈ Subfield.closure (Set.range (𝕋'.φ (ℓ, 0)) ∪ Set.range (𝕋'.φ (ℓ, 1))) := by
      intro y; rw [hgen ℓ]; trivial
    let ιr : 𝕋'.F ℓ →+* 𝕋.F ℓ :=
      ((Subfield.closure (Set.range (𝕋.φ (ℓ, 0)) ∪ Set.range (𝕋.φ (ℓ, 1)))).subtype).comp
        (θ₀.symm.toRingHom.comp
          { toFun := fun y => ⟨y, hmem' y⟩, map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl, map_add' := fun _ _ => rfl })
    have hι₀ : ∀ x : F₀, ιr (𝕋'.φ (ℓ, 0) x) = 𝕋.φ (ℓ, 0) x := by
      intro x
      show ((θ₀.symm ⟨𝕋'.φ (ℓ, 0) x, hmem' _⟩ : ↥(Subfield.closure _)) : 𝕋.F ℓ) = 𝕋.φ (ℓ, 0) x
      have := hθ₀₀ x
      have e : θ₀.symm ⟨𝕋'.φ (ℓ, 0) x, hmem' _⟩ = ⟨𝕋.φ (ℓ, 0) x, Subfield.subset_closure (Set.mem_union_left _ (Set.mem_range_self x))⟩ := by
        apply θ₀.injective; rw [RingEquiv.apply_symm_apply]; exact Subtype.ext this.symm
      rw [e]
    have hι₁ : ∀ x : F₀, ιr (𝕋'.φ (ℓ, 1) x) = 𝕋.φ (ℓ, 1) x := by
      intro x
      show ((θ₀.symm ⟨𝕋'.φ (ℓ, 1) x, hmem' _⟩ : ↥(Subfield.closure _)) : 𝕋.F ℓ) = 𝕋.φ (ℓ, 1) x
      have := hθ₀₁ x
      have e : θ₀.symm ⟨𝕋'.φ (ℓ, 1) x, hmem' _⟩ = ⟨𝕋.φ (ℓ, 1) x, Subfield.subset_closure (Set.mem_union_right _ (Set.mem_range_self x))⟩ := by
        apply θ₀.injective; rw [RingEquiv.apply_symm_apply]; exact Subtype.ext this.symm
      rw [e]

    let ι : 𝕋'.F ℓ →ₐ[AlgebraicClosure ℚ] 𝕋.F ℓ :=
      { toRingHom := ιr
        commutes' := fun c => by
          show ιr (algebraMap (AlgebraicClosure ℚ) (𝕋'.F ℓ) c) = algebraMap (AlgebraicClosure ℚ) (𝕋.F ℓ) c
          rw [← (𝕋'.φ (ℓ, 0)).commutes c, hι₀, (𝕋.φ (ℓ, 0)).commutes] }
    have hιφ₀ : ι.comp (𝕋'.φ (ℓ, 0)) = 𝕋.φ (ℓ, 0) := AlgHom.ext (hι₀)
    have hιφ₁ : ι.comp (𝕋'.φ (ℓ, 1)) = 𝕋.φ (ℓ, 1) := AlgHom.ext (hι₁)

    have hfinι : FiniteAlong (AlgebraicClosure ℚ) ι := by
      letI i1 : Algebra (𝕋'.F ℓ) (𝕋.F ℓ) := algebraAlong ι
      letI i0 : Algebra F₀ (𝕋'.F ℓ) := algebraAlong (𝕋'.φ (ℓ, 0))
      letI i2 : Algebra F₀ (𝕋.F ℓ) := algebraAlong (𝕋.φ (ℓ, 0))
      haveI : IsScalarTower F₀ (𝕋'.F ℓ) (𝕋.F ℓ) := IsScalarTower.of_algebraMap_eq (fun x => (hι₀ x).symm)
      haveI : Module.Finite F₀ (𝕋.F ℓ) := 𝕋.finite (ℓ, 0)
      exact Module.Finite.of_restrictScalars_finite F₀ (𝕋'.F ℓ) (𝕋.F ℓ)
    have hintι : ι.toRingHom.IsIntegral := by
      letI : Algebra (𝕋'.F ℓ) (𝕋.F ℓ) := algebraAlong ι
      haveI : Module.Finite (𝕋'.F ℓ) (𝕋.F ℓ) := hfinι
      have : Algebra.IsIntegral (𝕋'.F ℓ) (𝕋.F ℓ) := Algebra.IsIntegral.of_finite _ _
      exact fun x => this.isIntegral x
    haveI hcz : CharZero (𝕋'.F ℓ) := charZero_of_injective_algebraMap (algebraMap (AlgebraicClosure ℚ) (𝕋'.F ℓ)).injective
    have hsepι : SeparableAlong (AlgebraicClosure ℚ) ι := by
      letI : Algebra (𝕋'.F ℓ) (𝕋.F ℓ) := algebraAlong ι
      haveI : Module.Finite (𝕋'.F ℓ) (𝕋.F ℓ) := hfinι
      haveI : Algebra.IsIntegral (𝕋'.F ℓ) (𝕋.F ℓ) := Algebra.IsIntegral.of_finite _ _
      exact Algebra.IsSeparable.of_integral _ _

    have hmult : ∀ D, Divisor.correspondence (𝕋.φ (ℓ, 0)) (𝕋.φ (ℓ, 1)) (𝕋.integral (ℓ, 0)) (𝕋.integral (ℓ, 1)) D =
        finrankAlong (AlgebraicClosure ℚ) ι • Divisor.correspondence (𝕋'.φ (ℓ, 0)) (𝕋'.φ (ℓ, 1)) (𝕋'.integral (ℓ, 0)) (𝕋'.integral (ℓ, 1)) D :=
      fun D => AlgebraicCurve.Divisor.correspondence_eq_finrankAlong_smul_correspondence_of_comp_eq
        (𝕋.φ (ℓ, 0)) (𝕋.φ (ℓ, 1)) (𝕋.integral (ℓ, 0)) (𝕋.integral (ℓ, 1)) (𝕋'.φ (ℓ, 0)) (𝕋'.φ (ℓ, 1))
        (𝕋'.integral (ℓ, 0)) (𝕋'.integral (ℓ, 1)) ι hintι hfinι hsepι hιφ₀ hιφ₁ D

    have hm : finrankAlong (AlgebraicClosure ℚ) ι = 1 := by
      obtain ⟨w⟩ := HeckeR2.nonempty_place (K := AlgebraicClosure ℚ) (𝕋'.F ℓ)
      let P : Place (AlgebraicClosure ℚ) F₀ := w.restrictAlong (𝕋'.φ (ℓ, 0)) (𝕋'.integral (ℓ, 0))
      have hFI : FundamentalIdentityAlong (AlgebraicClosure ℚ) (𝕋'.φ (ℓ, 0)) (𝕋'.integral (ℓ, 0)) := by
        haveI : CharZero F₀ := charZero_of_injective_algebraMap (algebraMap (AlgebraicClosure ℚ) F₀).injective
        refine AlgebraicCurve.fundamentalIdentityAlong _ _ (𝕋'.finite (ℓ, 0)) ?_
        letI : Algebra F₀ (𝕋'.F ℓ) := algebraAlong (𝕋'.φ (ℓ, 0))
        haveI : Module.Finite F₀ (𝕋'.F ℓ) := 𝕋'.finite (ℓ, 0)
        haveI : Algebra.IsIntegral F₀ (𝕋'.F ℓ) := Algebra.IsIntegral.of_finite _ _
        exact Algebra.IsSeparable.of_integral _ _
      have hdeg := Divisor.degree_correspondence (𝕋'.φ (ℓ, 0)) (𝕋'.φ (ℓ, 1)) (𝕋'.integral (ℓ, 0)) (𝕋'.integral (ℓ, 1)) hFI
        (Finsupp.single P 1)
      have h1 := congrArg Divisor.degree ((hcorr ℓ (Finsupp.single P 1)).symm.trans (hmult (Finsupp.single P 1)))
      rw [map_nsmul, hdeg, Divisor.degree_single, one_mul, nsmul_eq_mul] at h1

      have hpos : ((finrankAlong (AlgebraicClosure ℚ) (𝕋'.φ (ℓ, 0)) : ℤ) * (P.deg : ℤ)) ≠ 0 := by
        apply mul_ne_zero
        · letI : Algebra F₀ (𝕋'.F ℓ) := algebraAlong (𝕋'.φ (ℓ, 0))
          haveI : Module.Finite F₀ (𝕋'.F ℓ) := 𝕋'.finite (ℓ, 0)
          have : 0 < finrankAlong (AlgebraicClosure ℚ) (𝕋'.φ (ℓ, 0)) := Module.finrank_pos
          exact_mod_cast this.ne'
        · exact_mod_cast Nat.one_le_iff_ne_zero.mp (AlgebraicCurve.one_le_deg P)
      have h2 : ((finrankAlong (AlgebraicClosure ℚ) ι : ℕ) : ℤ) = 1 :=
        Int.eq_one_of_mul_eq_self_left hpos h1.symm
      exact_mod_cast h2

    have hsurj : Function.Surjective ι := by
      letI : Algebra (𝕋'.F ℓ) (𝕋.F ℓ) := algebraAlong ι
      haveI : Module.Finite (𝕋'.F ℓ) (𝕋.F ℓ) := hfinι
      have hbt : (⊥ : Subalgebra (𝕋'.F ℓ) (𝕋.F ℓ)) = ⊤ := Subalgebra.bot_eq_top_of_finrank_eq_one hm
      intro y
      have hy : y ∈ (⊥ : Subalgebra (𝕋'.F ℓ) (𝕋.F ℓ)) := by rw [hbt]; trivial
      obtain ⟨x, hx⟩ := Algebra.mem_bot.1 hy
      exact ⟨x, hx⟩
    let θ : 𝕋.F ℓ ≃ₐ[AlgebraicClosure ℚ] 𝕋'.F ℓ := (AlgEquiv.ofBijective ι ⟨ι.toRingHom.injective, hsurj⟩).symm
    refine ⟨θ, fun i x => ?_⟩
    fin_cases i
    · show θ (𝕋.φ (ℓ, 0) x) = 𝕋'.φ (ℓ, 0) x
      rw [← hι₀ x]; exact (AlgEquiv.ofBijective ι ⟨ι.toRingHom.injective, hsurj⟩).symm_apply_apply (𝕋'.φ (ℓ, 0) x)
    · show θ (𝕋.φ (ℓ, 1) x) = 𝕋'.φ (ℓ, 1) x
      rw [← hι₁ x]; exact (AlgEquiv.ofBijective ι ⟨ι.toRingHom.injective, hsurj⟩).symm_apply_apply (𝕋'.φ (ℓ, 1) x)
  choose θ hθ using main
  refine ⟨θ, fun α x => hθ α.1 α.2 x, ?_⟩
  intro S g₀ g g' hg hg' ℓ σ y
  exact CerednikDrinfeld.TowerRider.equiv_comp_eq_comp_equiv (⇑(𝕋.φ (ℓ, 0))) (⇑(𝕋.φ (ℓ, 1))) (⇑(𝕋'.φ (ℓ, 0))) (⇑(𝕋'.φ (ℓ, 1)))
    (θ ℓ).toRingEquiv (hθ ℓ 0) (hθ ℓ 1) (hgen ℓ) (fun x => g₀ σ • x)
    (SemilinearAut.toRingAut (g ℓ σ)).toRingHom (SemilinearAut.toRingAut (g' ℓ σ)).toRingHom
    (fun x => hg (ℓ, 0) σ x) (fun x => hg (ℓ, 1) σ x) (fun x => hg' (ℓ, 0) σ x) (fun x => hg' (ℓ, 1) σ x) y

end S_CerednikDrinfeld_HeckeTower_exists_algEquiv_forall_comp_phi_eq_of_correspondence_eq
end P2MW
export P2MW.S_CerednikDrinfeld_HeckeTower_exists_algEquiv_forall_comp_phi_eq_of_correspondence_eq (solution)
