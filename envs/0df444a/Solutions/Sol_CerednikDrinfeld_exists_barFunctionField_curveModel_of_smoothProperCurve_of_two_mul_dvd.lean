-- Prove2me | solution 1 for CerednikDrinfeld.exists_barFunctionField_curveModel_of_smoothProperCurve_of_two_mul_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/d4e6341b-5a9d-507a-afcb-0625201510a1

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_AlgebraicCurve_CurveModel
import Mathlib
import Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_exists_curveModel_iso_pullback_germToFunctionField_eq_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_geometricallyIntegral_of_forall_isAlgClosed_isIntegral_pullback
import Theorems.Thm_AlgebraicGeometry_genericPoint_mem_preimage_comp_pullback_fst_of_injective_algebraMap
import Theorems.Thm_AlgebraicGeometry_exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk_of_germ_snd
import Theorems.Thm_AlgebraicCurve_CurveModel_exists_semilinearAut_baseAut_eq_and_pointEquivPlace_eq_smul
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
import Theorems.Thm_AlgebraicCurve_essFiniteType_functionField
import Theorems.Thm_AlgebraicGeometry_exists_algEquiv_tensorProduct_functionField_pullback_of_isAlgebraic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_exists_barFunctionField_curveModel_of_smoothProperCurve_of_two_mul_dvd
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec"
p2m_attr_erase "simp" "TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM

open scoped Quaternion TensorProduct NumberField

noncomputable section

namespace C3FFPkg

universe u v

namespace FunctionFieldPull

variable {X Y Z : Scheme.{u}}

def pull [IrreducibleSpace X] [IrreducibleSpace Y] (f : X ⟶ Y)
    (h : f.base (genericPoint X) ⤳ genericPoint Y) : Y.functionField ⟶ X.functionField :=
  Y.presheaf.stalkSpecializes h ≫ f.stalkMap (genericPoint X)

section

variable [IrreducibleSpace X] [IrreducibleSpace Y] [IrreducibleSpace Z]

theorem pull_germ (f : X ⟶ Y) (h : f.base (genericPoint X) ⤳ genericPoint Y)
    (U : Y.Opens) (hU : genericPoint Y ∈ U) (s : Γ(Y, U)) :
    pull f h (Y.presheaf.germ U (genericPoint Y) hU s) =
      X.presheaf.germ (f ⁻¹ᵁ U) (genericPoint X) (h.mem_open U.isOpen hU) (f.app U s) := by
  simp only [pull, CommRingCat.comp_apply]
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply, Scheme.Hom.germ_stalkMap_apply]

theorem pull_algebraMap (f : X ⟶ Y) (h : f.base (genericPoint X) ⤳ genericPoint Y) (x : X)
    (a : Y.presheaf.stalk (f.base x)) :
    pull f h (algebraMap (Y.presheaf.stalk (f.base x)) Y.functionField a) =
      algebraMap (X.presheaf.stalk x) X.functionField (f.stalkMap x a) := by
  simp only [pull, RingHom.algebraMap_toAlgebra, CommRingCat.comp_apply]
  rw [TopCat.Presheaf.stalkSpecializes_comp_apply (Y.presheaf)]
  have := Scheme.Hom.stalkSpecializes_stalkMap_apply f (genericPoint X) x
    ((genericPoint_spec X).specializes trivial) a
  convert this using 2

theorem pull_id : pull (𝟙 X) (specializes_refl _) = 𝟙 _ := by
  simp [pull]

theorem pull_comp (f : X ⟶ Y) (g : Y ⟶ Z) (hf : f.base (genericPoint X) ⤳ genericPoint Y)
    (hg : g.base (genericPoint Y) ⤳ genericPoint Z) :
    pull (f ≫ g) ((g.base.hom.map_specializes hf).trans hg) = pull g hg ≫ pull f hf := by
  simp only [pull, Scheme.Hom.stalkMap_comp, Category.assoc]
  rw [← Scheme.Hom.stalkSpecializes_stalkMap_assoc g (f.base (genericPoint X)) (genericPoint Y) hf]
  rw [← Category.assoc, TopCat.Presheaf.stalkSpecializes_comp]
  rfl

end

variable [IsIntegral X] [IsIntegral Y]

theorem specializes_of_iso (e : X ≅ Y) : e.hom.base (genericPoint X) ⤳ genericPoint Y :=
  (genericPoint_eq_of_isOpenImmersion e.hom).symm ▸ specializes_refl _

theorem specializes_of_iso_inv (e : X ≅ Y) : e.inv.base (genericPoint Y) ⤳ genericPoint X :=
  specializes_of_iso e.symm

def equivOfIso (e : X ≅ Y) : Y.functionField ≃+* X.functionField :=
  (({ hom := pull e.hom (specializes_of_iso e)
      inv := pull e.inv (specializes_of_iso_inv e)
      hom_inv_id := by
        have h := (pull_comp e.inv e.hom (specializes_of_iso_inv e) (specializes_of_iso e)).symm
        rw [h]
        have : ∀ (k : (e.inv ≫ e.hom).base (genericPoint Y) ⤳ genericPoint Y),
            pull (e.inv ≫ e.hom) k = 𝟙 _ := by
          rw [e.inv_hom_id]; intro k; exact pull_id
        exact this _
      inv_hom_id := by
        have h := (pull_comp e.hom e.inv (specializes_of_iso e) (specializes_of_iso_inv e)).symm
        rw [h]
        have : ∀ (k : (e.hom ≫ e.inv).base (genericPoint X) ⤳ genericPoint X),
            pull (e.hom ≫ e.inv) k = 𝟙 _ := by
          rw [e.hom_inv_id]; intro k; exact pull_id
        exact this _ } : Y.functionField ≅ X.functionField)).commRingCatIsoToRingEquiv

theorem equivOfIso_apply (e : X ≅ Y) (a : Y.functionField) :
    equivOfIso e a = pull e.hom (specializes_of_iso e) a := rfl

theorem equivOfIso_symm_apply (e : X ≅ Y) (a : X.functionField) :
    (equivOfIso e).symm a = pull e.inv (specializes_of_iso_inv e) a := rfl

theorem map_equivOfIso_range_stalk (e : X ≅ Y) (x : X) :
    (algebraMap (Y.presheaf.stalk (e.hom.base x)) Y.functionField).range.map
        (equivOfIso e).toRingHom =
      (algebraMap (X.presheaf.stalk x) X.functionField).range := by
  haveI : IsIso (e.hom.stalkMap x) := inferInstance
  ext b
  simp only [Subring.mem_map, RingHom.mem_range, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨e.hom.stalkMap x a, (pull_algebraMap e.hom (specializes_of_iso e) x a).symm⟩
  · rintro ⟨a, rfl⟩
    obtain ⟨a', rfl⟩ : ∃ a', e.hom.stalkMap x a' = a :=
      ⟨inv (e.hom.stalkMap x) a, by
        rw [← CommRingCat.comp_apply, IsIso.inv_hom_id]; rfl⟩
    exact ⟨_, ⟨a', rfl⟩, pull_algebraMap e.hom (specializes_of_iso e) x a'⟩

theorem image_equivOfIso_range_stalk (e : X ≅ Y) (x : X) :
    (equivOfIso e) ''
        ((algebraMap (Y.presheaf.stalk (e.hom.base x)) Y.functionField).range : Set _) =
      ((algebraMap (X.presheaf.stalk x) X.functionField).range : Set _) := by
  have h := congrArg (fun S : Subring X.functionField => (S : Set X.functionField))
    (map_equivOfIso_range_stalk e x)
  simpa [Subring.coe_map] using h

theorem image_equivOfIso_symm_range_stalk (e : X ≅ Y) (x : X) :
    (equivOfIso e).symm '' ((algebraMap (X.presheaf.stalk x) X.functionField).range : Set _) =
      ((algebraMap (Y.presheaf.stalk (e.hom.base x)) Y.functionField).range : Set _) := by
  rw [← image_equivOfIso_range_stalk e x, ← Set.image_comp]
  simp

theorem pull_baseToFunctionField {K : Type u} [Field K] (f : X ⟶ Y)
    (h : f.base (genericPoint X) ⤳ genericPoint Y)
    (cX : X ⟶ Spec (CommRingCat.of K)) (cY : Y ⟶ Spec (CommRingCat.of K)) (hf : f ≫ cY = cX)
    (a : K) :
    pull f h (baseToFunctionField cY a) = baseToFunctionField cX a := by
  subst hf
  simp only [baseToFunctionField, RingHom.coe_comp, Function.comp_apply]
  change pull f h (Y.presheaf.germ ⊤ (genericPoint Y) trivial _) =
    X.presheaf.germ ⊤ (genericPoint X) trivial _
  rw [pull_germ]
  rfl

theorem equivOfIso_baseToFunctionField {K : Type u} [Field K] (e : X ≅ Y)
    (cX : X ⟶ Spec (CommRingCat.of K)) (cY : Y ⟶ Spec (CommRingCat.of K))
    (hf : e.hom ≫ cY = cX) (a : K) :
    equivOfIso e (baseToFunctionField cY a) = baseToFunctionField cX a :=
  pull_baseToFunctionField e.hom _ cX cY hf a

end FunctionFieldPull

open FunctionFieldPull

section PullExtras
variable {X Y : Scheme.{u}} [IrreducibleSpace ↥X] [IrreducibleSpace ↥Y]

theorem pull_baseToFunctionField_twist [IsIntegral X] [IsIntegral Y] {K : Type u} [Field K] (f : X ⟶ Y)
    (h : f.base (genericPoint X) ⤳ genericPoint Y)
    (cX : X ⟶ Spec (CommRingCat.of K)) (cY : Y ⟶ Spec (CommRingCat.of K)) (τ : K ≃+* K)
    (hf : f ≫ cY = cX ≫ Spec.map (CommRingCat.ofHom (τ : K →+* K))) (a : K) :
    pull f h (baseToFunctionField cY a) = baseToFunctionField cX (τ a) := by
  simp only [baseToFunctionField, RingHom.coe_comp, Function.comp_apply]
  change pull f h (Y.presheaf.germ ⊤ (genericPoint Y) trivial _) = X.presheaf.germ ⊤ (genericPoint X) trivial _
  rw [pull_germ]
  have key : (f.app ⊤).hom (cY.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a)) =
      cX.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (τ a)) := by
    have h1 : (f.app ⊤).hom (cY.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a)) =
        cX.appTop.hom ((Spec.map (CommRingCat.ofHom (τ : K →+* K))).appTop.hom
          ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a)) :=
      congrArg (fun φ => (Scheme.Hom.appTop φ).hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a)) hf
    rw [h1]
    congr 1
    have h2 := congrArg (fun φ => φ.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (τ : K →+* K)))
    exact h2.symm
  exact congrArg _ key

theorem pull_germToFunctionField [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) (h : f.base (genericPoint X) ⤳ genericPoint Y)
    (U : Y.Opens) [hU : Nonempty (Scheme.Opens.toScheme U)] [hU' : Nonempty (Scheme.Opens.toScheme (f ⁻¹ᵁ U))] (t : Γ(Y, U)) :
    pull f h (Y.germToFunctionField U t) = X.germToFunctionField (f ⁻¹ᵁ U) ((f.app U).hom t) := by
  obtain ⟨⟨y, hy⟩⟩ := hU
  exact pull_germ f h U (((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr ⟨y, trivial, hy⟩) t

theorem semilinearAut_ext {K F : Type} [Field K] [Field F] [Algebra K F] (g g' : SemilinearAut K F)
    (h1 : ∀ z : F, g • z = g' • z) (h2 : SemilinearAut.baseAut g = SemilinearAut.baseAut g') : g = g' :=
  Subtype.ext (Prod.ext (RingEquiv.ext h1) h2)

theorem pull_congr' (f g : X ⟶ Y) (hfg : f = g) (hf : f.base (genericPoint X) ⤳ genericPoint Y)
    (hg : g.base (genericPoint X) ⤳ genericPoint Y) : pull f hf = pull g hg := by
  subst hfg; rfl

end PullExtras

end C3FFPkg

namespace RatFF

theorem rat_smul_tmul {R₀ : Type} [CommRing R₀] [Algebra R₀ ℚ]
    {A B : Type} [CommRing A] [CommRing B] [Algebra R₀ A] [Algebra R₀ B] [Algebra ℚ A] [Algebra ℚ B]
    [IsScalarTower R₀ ℚ A] [IsScalarTower R₀ ℚ B] (q : ℚ) (a : A) (b : B) :
    ((q • a) ⊗ₜ[R₀] b : A ⊗[R₀] B) = a ⊗ₜ[R₀] (q • b) := by
  have hd : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hq : ((q.den : ℤ) : ℚ) * q = (q.num : ℚ) := by
    have := Rat.mul_den_eq_num q
    push_cast
    linarith [this, mul_comm q (q.den : ℚ)]

  have hb : b = (q.den : ℤ) • (((q.den : ℚ))⁻¹ • b) := by
    rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul]
    push_cast
    rw [mul_inv_cancel₀ hd, one_smul]
  have hA : (q.den : ℤ) • (q • a) = (q.num : ℤ) • a := by
    rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul, hq, Int.cast_smul_eq_zsmul]
  have hB : (q.num : ℤ) • (((q.den : ℚ))⁻¹ • b) = q • b := by
    rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul, ← hq]
    push_cast
    rw [mul_comm ((q.den : ℚ)) q, mul_assoc, mul_inv_cancel₀ hd, mul_one]
  conv_lhs => rw [hb]
  rw [← TensorProduct.smul_tmul, hA, TensorProduct.smul_tmul, hB]

theorem exists_finsupp_sum_tmul {R₀ : Type} [CommRing R₀] [Algebra R₀ ℚ]
    {A B : Type} [CommRing A] [CommRing B] [Algebra R₀ A] [Algebra R₀ B] [Algebra ℚ A] [Algebra ℚ B]
    [IsScalarTower R₀ ℚ A] [IsScalarTower R₀ ℚ B]
    {F : Type} [AddCommGroup F] [Module ℚ F] {ι : Type} (bs : Module.Basis ι ℚ F) (eF : F →ₗ[ℚ] A)
    (heF : Function.Surjective eF) (t : A ⊗[R₀] B) :
    ∃ c : ι →₀ B, c.sum (fun i k => (eF (bs i)) ⊗ₜ[R₀] k) = t := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul s k =>
    obtain ⟨x, rfl⟩ := heF s
    refine ⟨(bs.repr x).mapRange (fun r => r • k) (by simp), ?_⟩
    rw [Finsupp.sum_mapRange_index (fun i => by simp)]
    conv_rhs => rw [← bs.linearCombination_repr x]
    rw [Finsupp.linearCombination_apply, map_finsuppSum]
    simp only [Finsupp.sum, TensorProduct.sum_tmul, map_smul, rat_smul_tmul]
  | add t₁ t₂ h₁ h₂ =>
    obtain ⟨c₁, rfl⟩ := h₁
    obtain ⟨c₂, rfl⟩ := h₂
    refine ⟨c₁ + c₂, ?_⟩
    rw [Finsupp.sum_add_index' (fun i => by simp) (fun i b₁ b₂ => by simp [TensorProduct.tmul_add])]

theorem fst_base_genericPoint {R₀ : Type} [CommRing R₀] [Algebra R₀ ℚ]
    {X : Scheme.{0}} (πX : X ⟶ Spec (CommRingCat.of R₀)) [AlgebraicGeometry.IsIntegral X]
    [AlgebraicGeometry.IsIntegral ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ))))]
    (hinj : Function.Injective (algebraMap R₀ ℚ)) :
    genericPoint X = (pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ))))) := by
  set Y := pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))
  set z := (pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))).base (genericPoint ↑Y) with hz
  have hmem : ∀ U : X.Opens, (U : Set X).Nonempty → z ∈ U := by
    intro U hU
    have := genericPoint_mem_preimage_comp_pullback_fst_of_injective_algebraMap hinj πX (Y := Y) (𝟙 _) U hU
    simpa using this
  have hgen : IsGenericPoint z (Set.univ : Set X) := by
    rw [isGenericPoint_iff_specializes]
    intro y
    simp only [Set.mem_univ, iff_true]
    rw [specializes_iff_forall_open]
    intro s hs hys
    exact hmem ⟨s, hs⟩ ⟨y, hys⟩
  exact (genericPoint_spec X).eq hgen

theorem core {R₀ : Type} [CommRing R₀] [Algebra R₀ ℚ]
    {X : Scheme.{0}} (πX : X ⟶ Spec (CommRingCat.of R₀)) [AlgebraicGeometry.IsIntegral X]
    [AlgebraicGeometry.IsIntegral ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ))))]
    (hinj : Function.Injective (algebraMap R₀ ℚ))
    (z : X) (hx : ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))))) = z)
    {F : Type} [Field F] [Algebra ℚ F] (eF : F ≃+* X.presheaf.stalk z)
    {Fbar : Type} [Field Fbar] [Algebra ℚ Fbar] (toBar : F →+* Fbar)
    (toBar_algebraMap : ∀ r : ℚ, toBar (algebraMap ℚ F r) = algebraMap ℚ Fbar (algebraMap ℚ ℚ r))
    (closure_toBar : Subfield.closure (Set.range (algebraMap ℚ Fbar) ∪ Set.range toBar) = ⊤)
    (linearIndependent_toBar : ∀ s : Finset F,
      LinearIndependent ℚ (fun x : s => (x : F)) → LinearIndependent ℚ (fun x : s => toBar (x : F)))
    (eF_symm_germ : ∀ r : R₀, eF.symm ((X.presheaf.germ ⊤ z trivial).hom
        (πX.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R₀)).inv.hom r))) = algebraMap ℚ F (algebraMap R₀ ℚ r)) :
    letI : Algebra R₀ (X.presheaf.stalk ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ))))))) :=
      ((X.presheaf.germ ⊤ ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))))) trivial).hom.comp (πX.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R₀)).inv.hom)).toAlgebra
    ∀ (𝔮 : Ideal ((X.presheaf.stalk ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ))))))) ⊗[R₀] ℚ)) (_ : 𝔮.IsPrime)
      (e : (pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))).presheaf.stalk (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ))))) ≃+* Localization.AtPrime 𝔮),
      (∀ s : X.presheaf.stalk ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))))),
        e (((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))).stalkMap (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))))).hom s) =
          algebraMap ((X.presheaf.stalk ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ))))))) ⊗[R₀] ℚ) (Localization.AtPrime 𝔮) (s ⊗ₜ[R₀] 1)) →
      (∀ c : ℚ,
        e ((pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))).presheaf.germ ⊤ (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ))))) trivial
            ((pullback.snd πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))).appTop ((Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv c))) =
          algebraMap ((X.presheaf.stalk ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ))))))) ⊗[R₀] ℚ) (Localization.AtPrime 𝔮) (1 ⊗ₜ[R₀] c)) →
    ∃ eFbar : Fbar ≃+* ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))).functionField,
      (∀ c : ℚ, eFbar (algebraMap ℚ Fbar c) = baseToFunctionField (pullback.snd πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))) c) ∧
      ∀ (U : X.Opens) (hzU : z ∈ U) (t : Γ(X, U)),
        eFbar (toBar (eF.symm ((X.presheaf.germ U z hzU).hom t))) =
          ((pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))).presheaf.germ ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))) ⁻¹ᵁ U) (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ))))) (show (pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ))))) ∈ U by rw [hx]; exact hzU)).hom
            (((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))).app U).hom t) := by
  subst hx
  intro 𝔮 h𝔮 e he1 he2
  letI algR : Algebra R₀ (X.presheaf.stalk ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ))))))) := ((X.presheaf.germ ⊤ ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))))) trivial).hom.comp (πX.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R₀)).inv.hom)).toAlgebra

  letI algQ : Algebra ℚ (X.presheaf.stalk ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ))))))) := (eF.toRingHom.comp (algebraMap ℚ F)).toAlgebra
  have algQ_def : ∀ q : ℚ, algebraMap ℚ (X.presheaf.stalk ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ))))))) q = eF (algebraMap ℚ F q) := fun _ => rfl
  have algR_def : ∀ r : R₀, algebraMap R₀ (X.presheaf.stalk ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ))))))) r =
      (X.presheaf.germ ⊤ ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))))) trivial).hom (πX.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R₀)).inv.hom r)) := fun _ => rfl
  haveI towQ : IsScalarTower R₀ ℚ (X.presheaf.stalk ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ))))))) := by
    refine IsScalarTower.of_algebraMap_eq (fun r => ?_)
    rw [algQ_def, ← eF_symm_germ, RingEquiv.apply_symm_apply, algR_def]

  letI algRF : Algebra R₀ Fbar := ((algebraMap ℚ Fbar).comp (algebraMap R₀ ℚ)).toAlgebra
  haveI towF : IsScalarTower R₀ ℚ Fbar := IsScalarTower.of_algebraMap_eq (fun _ => rfl)

  let f : (X.presheaf.stalk ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ))))))) →ₐ[R₀] Fbar :=
    { toRingHom := toBar.comp eF.symm.toRingHom
      commutes' := fun r => by
        show toBar (eF.symm (algebraMap R₀ (X.presheaf.stalk ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ))))))) r)) = algebraMap ℚ Fbar (algebraMap R₀ ℚ r)
        rw [algR_def, eF_symm_germ, toBar_algebraMap, ← IsScalarTower.algebraMap_apply R₀ ℚ ℚ] }
  let g : ℚ →ₐ[R₀] Fbar := IsScalarTower.toAlgHom R₀ ℚ Fbar
  let Ψ : (X.presheaf.stalk ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ))))))) ⊗[R₀] ℚ →ₐ[R₀] Fbar := Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)
  have Ψ_tmul : ∀ (s : (X.presheaf.stalk ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))))))) (c : ℚ), Ψ (s ⊗ₜ[R₀] c) = toBar (eF.symm s) * algebraMap ℚ Fbar c := by
    intro s c
    show Algebra.TensorProduct.lift f g _ (s ⊗ₜ[R₀] c) = _
    rw [Algebra.TensorProduct.lift_tmul]
    rfl

  have Ψ_surj : Function.Surjective Ψ := by
    classical
    letI algF : Algebra F Fbar := toBar.toAlgebra
    have algF_def : ∀ x : F, algebraMap F Fbar x = toBar x := fun _ => rfl
    let A₁ : Subalgebra F Fbar := Algebra.adjoin F (Set.range (algebraMap ℚ Fbar))
    have hA₁ : A₁ ≤ integralClosure F Fbar := by
      apply Algebra.adjoin_le
      rintro x ⟨c, rfl⟩
      rw [SetLike.mem_coe, mem_integralClosure_iff]
      obtain ⟨p, hp, hpc⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) c).isIntegral
      refine ⟨p.map (algebraMap ℚ F), hp.map _, ?_⟩
      have h2 := congrArg (algebraMap ℚ Fbar) hpc
      rw [map_zero, Polynomial.hom_eval₂] at h2
      rw [Polynomial.eval₂_map, Subsingleton.elim ((algebraMap F Fbar).comp (algebraMap ℚ F))
        ((algebraMap ℚ Fbar).comp (algebraMap ℚ ℚ))]
      exact h2
    let K₁ : Subfield Fbar :=
      { toSubring := A₁.toSubring
        inv_mem' := fun x hx => by
          have hint : IsIntegral F x := (mem_integralClosure_iff F Fbar).mp (hA₁ hx)
          exact Subalgebra.inv_mem_of_algebraic A₁ (x := ⟨x, hx⟩) hint.isAlgebraic }
    have htop : (⊤ : Subfield Fbar) ≤ K₁ := by
      rw [← closure_toBar, Subfield.closure_le]
      rintro y (⟨c, rfl⟩ | ⟨x, rfl⟩)
      · exact Algebra.subset_adjoin ⟨c, rfl⟩
      · rw [← algF_def]; exact Subalgebra.algebraMap_mem A₁ x
    let S₂ : Subalgebra F Fbar :=
      { carrier := Set.range Ψ
        mul_mem' := by rintro _ _ ⟨u, rfl⟩ ⟨v, rfl⟩; exact ⟨u * v, map_mul Ψ u v⟩
        one_mem' := ⟨1, map_one Ψ⟩
        add_mem' := by rintro _ _ ⟨u, rfl⟩ ⟨v, rfl⟩; exact ⟨u + v, map_add Ψ u v⟩
        zero_mem' := ⟨0, map_zero Ψ⟩
        algebraMap_mem' := fun x => ⟨eF x ⊗ₜ[R₀] 1, by rw [Ψ_tmul, RingEquiv.symm_apply_apply, map_one, mul_one]; rfl⟩ }
    have hA₁S : A₁ ≤ S₂ := by
      apply Algebra.adjoin_le
      rintro y ⟨c, rfl⟩
      exact ⟨1 ⊗ₜ[R₀] c, by rw [Ψ_tmul, map_one, map_one, one_mul]⟩
    intro y
    have hy : y ∈ S₂ := hA₁S (htop (Subfield.mem_top y))
    exact hy

  have Ψ_inj : Function.Injective Ψ := by
    classical
    let eFl : F →ₗ[ℚ] (X.presheaf.stalk ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ))))))) :=
      { toFun := eF
        map_add' := fun x y => map_add eF x y
        map_smul' := fun q x => by
          show eF (q • x) = q • eF x
          rw [Algebra.smul_def, Algebra.smul_def, map_mul, algQ_def] }
    have eFl_apply : ∀ x, eFl x = eF x := fun _ => rfl
    let bs := Module.Basis.ofVectorSpace ℚ F
    have key : ∀ c : ↑(Module.Basis.ofVectorSpaceIndex ℚ F) →₀ ℚ,
        Ψ (c.sum fun i k => eF (bs i) ⊗ₜ[R₀] k) = 0 → c = 0 := by
      intro c hc
      rw [map_finsuppSum] at hc
      simp only [Ψ_tmul, RingEquiv.symm_apply_apply] at hc

      have hli : LinearIndependent ℚ (fun i : ↥c.support => toBar (bs (i : ↑(Module.Basis.ofVectorSpaceIndex ℚ F)))) := by
        let s : Finset F := c.support.image bs
        have hsub : ((s : Set F)) ⊆ Set.range bs := by
          intro x hx
          simp only [s, Finset.coe_image] at hx
          obtain ⟨i, -, rfl⟩ := hx
          exact ⟨i, rfl⟩
        have hs : LinearIndependent ℚ (fun x : (s : Set F) => (x : F)) :=
          (bs.linearIndependent.linearIndepOn_id.mono hsub).linearIndependent
        have hs' := linearIndependent_toBar s hs
        let φ : ↥c.support → ↥s := fun i => ⟨bs i, Finset.mem_image_of_mem bs i.2⟩
        have hφ : Function.Injective φ := fun i j h => Subtype.ext (bs.injective (Subtype.ext_iff.mp h))
        exact hs'.comp φ hφ
      rw [Fintype.linearIndependent_iff] at hli
      have hsum : ∑ i : ↥c.support, c i • toBar (bs i) = 0 := by
        rw [Finset.sum_coe_sort c.support (fun i => c i • toBar (bs i))]
        rw [Finsupp.sum] at hc
        refine (Finset.sum_congr rfl fun i _ => ?_).trans hc
        rw [Algebra.smul_def, mul_comm]
      have h0 := hli (fun i => c i) hsum
      ext i
      by_cases hi : i ∈ c.support
      · exact h0 ⟨i, hi⟩
      · exact Finsupp.notMem_support_iff.mp hi
    rw [injective_iff_map_eq_zero]
    intro t ht
    obtain ⟨c, rfl⟩ := exists_finsupp_sum_tmul (R₀ := R₀) bs eFl eF.surjective t
    simp only [eFl_apply] at ht ⊢
    rw [key c ht, Finsupp.sum_zero_index]
  let ΨE : (X.presheaf.stalk ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ))))))) ⊗[R₀] ℚ ≃+* Fbar := RingEquiv.ofBijective Ψ.toRingHom ⟨Ψ_inj, Ψ_surj⟩
  have ΨE_apply : ∀ t, ΨE t = Ψ t := fun _ => rfl

  have hT : IsField ((X.presheaf.stalk ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ))))))) ⊗[R₀] ℚ) := MulEquiv.isField (Field.toIsField Fbar) ΨE.toMulEquiv
  have hbij : Function.Bijective (algebraMap ((X.presheaf.stalk ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ))))))) ⊗[R₀] ℚ) (Localization.AtPrime 𝔮)) :=
    by convert IsField.localization_map_bijective (Rₘ := Localization.AtPrime 𝔮) (M := 𝔮.primeCompl) (fun h => h 𝔮.zero_mem) hT
  let lam : (X.presheaf.stalk ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ))))))) ⊗[R₀] ℚ ≃+* Localization.AtPrime 𝔮 := RingEquiv.ofBijective (algebraMap _ (Localization.AtPrime 𝔮)) hbij
  have lam_apply : ∀ t, lam t = algebraMap _ (Localization.AtPrime 𝔮) t := fun _ => rfl

  refine ⟨ΨE.symm.trans (lam.trans e.symm), ?_, ?_⟩
  · intro c
    have h1 : ΨE.symm (algebraMap ℚ Fbar c) = (1 : (X.presheaf.stalk ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))))))) ⊗ₜ[R₀] c := by
      rw [RingEquiv.symm_apply_eq, ΨE_apply, Ψ_tmul, map_one, map_one, one_mul]
    rw [RingEquiv.trans_apply, RingEquiv.trans_apply, h1, RingEquiv.symm_apply_eq]
    exact (he2 c).symm
  · intro U hzU t
    rw [RingEquiv.trans_apply, RingEquiv.trans_apply, RingEquiv.symm_apply_eq]
    have h1 : ΨE.symm (toBar (eF.symm ((X.presheaf.germ U ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))))) hzU).hom t))) =
        ((X.presheaf.germ U ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))))) hzU).hom t) ⊗ₜ[R₀] (1 : ℚ) := by
      rw [RingEquiv.symm_apply_eq, ΨE_apply, Ψ_tmul, map_one, mul_one]
    calc lam (ΨE.symm (toBar (eF.symm ((X.presheaf.germ U ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))))) hzU).hom t))))
        = lam (((X.presheaf.germ U ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))))) hzU).hom t) ⊗ₜ[R₀] (1 : ℚ)) := congrArg lam h1
      _ = e (((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))).stalkMap (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))))).hom ((X.presheaf.germ U ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))))) hzU).hom t)) := (he1 _).symm
      _ = _ := congrArg e (Scheme.Hom.germ_stalkMap_apply (pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))) U (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ))))) hzU t)

end RatFF

theorem RatFF.ratFibreEquiv
    {R₀ : Type} [CommRing R₀] [Algebra R₀ ℚ]
    {X : Scheme.{0}} (πX : X ⟶ Spec (CommRingCat.of R₀)) [AlgebraicGeometry.IsIntegral X]
    [AlgebraicGeometry.IsIntegral ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ))))]
    [CharZero X.functionField]
    (hinj : Function.Injective (algebraMap R₀ ℚ))
    (hgerm : ∀ r : R₀, (X.presheaf.germ ⊤ (genericPoint X) trivial).hom
        (πX.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R₀)).inv.hom r)) = algebraMap ℚ X.functionField (algebraMap R₀ ℚ r)) :
    ∃ φ : X.functionField ≃+* ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))).functionField,
      (∀ z : ℚ, φ (algebraMap ℚ X.functionField z) =
        baseToFunctionField (pullback.snd πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))) z) ∧
      ∀ (U : X.Opens) [Nonempty (U : Scheme.{0})]
        [Nonempty (((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))) ⁻¹ᵁ U :
          (pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))).Opens) : Scheme.{0})]
        (t : Γ(X, U)),
        φ (X.germToFunctionField U t) =
          (pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))).germToFunctionField
            ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))) ⁻¹ᵁ U)
            ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))).app U t) := by
  have hz : genericPoint X = (pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))).base
      (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ))))) := RatFF.fst_base_genericPoint πX hinj
  obtain ⟨𝔮, h𝔮, e, -, he1, he2⟩ :=
    AlgebraicGeometry.exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk_of_germ_snd X πX ℚ
      (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))))
  have hcl : Subfield.closure (Set.range (algebraMap ℚ X.functionField) ∪ Set.range (RingHom.id X.functionField)) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    exact Subfield.subset_closure (Or.inr ⟨x, rfl⟩)
  obtain ⟨φ, h1, h2⟩ := RatFF.core πX hinj (genericPoint X) hz.symm (RingEquiv.refl X.functionField) (RingHom.id _)
    (fun r => by simp) hcl (fun s hs => hs) (fun r => by simpa using hgerm r) 𝔮 h𝔮 e he1 he2
  refine ⟨φ, h1, fun U hU _ t => ?_⟩
  have hmem : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by obtain ⟨x⟩ := hU; exact ⟨x.1, trivial, x.2⟩)
  exact h2 U hmem t

namespace C3FFPkg
open FunctionFieldPull

theorem injective_of_localizationAway {n : ℤ} {K : Type} [Field K] [CharZero K]
    (φ : Localization.Away n →+* K) : Function.Injective φ := by
  rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
  intro x hx
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers n) x
  have hcast : ∀ b : ℤ, φ (algebraMap ℤ (Localization.Away n) b) = (b : K) := fun b =>
    eq_intCast (φ.comp (algebraMap ℤ (Localization.Away n))) b
  have ha : (a : K) = 0 := by
    have h1 := congrArg φ (IsLocalization.mk'_spec (Localization.Away n) a s)
    rw [map_mul, hcast a] at h1
    rw [show φ (IsLocalization.mk' (Localization.Away n) a s) = 0 from hx, zero_mul] at h1
    exact h1.symm
  have ha0 : a = 0 := by exact_mod_cast ha
  show IsLocalization.mk' (Localization.Away n) a s = 0
  rw [ha0, IsLocalization.mk'_zero]

theorem ringHom_ext_localizationAway {n : ℤ} {K : Type} [CommRing K] (φ ψ : Localization.Away n →+* K) : φ = ψ :=
  IsLocalization.ringHom_ext (Submonoid.powers n) (RingHom.ext_int _ _)

section Geometric

variable {R₀ : Type} [CommRing R₀] {X : Scheme.{0}} (πX : X ⟶ Spec (CommRingCat.of R₀)) [IsIntegral X]
  {k : Type} [Field k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R₀)) [IsIntegral ↑(pullback πX s)]

theorem fst_genericPoint_specializes (hinj : Function.Injective (Spec.preimage s).hom) :
    (pullback.fst πX s).base (genericPoint ↑(pullback πX s)) ⤳ genericPoint X := by
  letI : Algebra R₀ k := (Spec.preimage s).hom.toAlgebra
  have hs : s = Spec.map (CommRingCat.ofHom (algebraMap R₀ k)) := by
    show s = Spec.map (Spec.preimage s); rw [Spec.map_preimage]
  have key : ∀ (s' : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R₀))
      (hs' : s' = Spec.map (CommRingCat.ofHom (algebraMap R₀ k))) [IsIntegral ↑(pullback πX s')]
      (U : X.Opens) (hU : (U : Set X).Nonempty), genericPoint ↑(pullback πX s') ∈ (pullback.fst πX s') ⁻¹ᵁ U := by
    intro s' hs' _ U hU; subst hs'
    simpa using genericPoint_mem_preimage_comp_pullback_fst_of_injective_algebraMap hinj πX (𝟙 _) U hU
  rw [specializes_iff_forall_open]
  intro U hU hmem
  exact key s hs ⟨U, hU⟩ ⟨_, hmem⟩

def toBarMap (hinj : Function.Injective (Spec.preimage s).hom) : X.functionField →+* ↥(pullback πX s).functionField :=
  (pull (pullback.fst πX s) (fst_genericPoint_specializes πX s hinj)).hom

theorem toBarMap_apply (hinj : Function.Injective (Spec.preimage s).hom) (z : X.functionField) :
    toBarMap πX s hinj z = pull (pullback.fst πX s) (fst_genericPoint_specializes πX s hinj) z := rfl

theorem toBarMap_germ (hinj : Function.Injective (Spec.preimage s).hom) (U : X.Opens) [hU : Nonempty (Scheme.Opens.toScheme U)]
    [hU' : Nonempty (Scheme.Opens.toScheme ((pullback.fst πX s) ⁻¹ᵁ U))] (t : Γ(X, U)) :
    toBarMap πX s hinj (X.germToFunctionField U t) =
      (pullback πX s).germToFunctionField ((pullback.fst πX s) ⁻¹ᵁ U) (((pullback.fst πX s).app U).hom t) :=
  pull_germ _ _ U _ t

def twist (σ : k ≃+* k) (hσ : Spec.map (CommRingCat.ofHom (σ : k →+* k)) ≫ s = s) : pullback πX s ⟶ pullback πX s :=
  pullback.lift (pullback.fst πX s) (pullback.snd πX s ≫ Spec.map (CommRingCat.ofHom (σ : k →+* k)))
    (by rw [Category.assoc, hσ, pullback.condition])

@[scoped simp] theorem twist_fst (σ : k ≃+* k) (hσ : Spec.map (CommRingCat.ofHom (σ : k →+* k)) ≫ s = s) :
    twist πX s σ hσ ≫ pullback.fst πX s = pullback.fst πX s := pullback.lift_fst _ _ _

@[scoped simp] theorem twist_snd (σ : k ≃+* k) (hσ : Spec.map (CommRingCat.ofHom (σ : k →+* k)) ≫ s = s) :
    twist πX s σ hσ ≫ pullback.snd πX s = pullback.snd πX s ≫ Spec.map (CommRingCat.ofHom (σ : k →+* k)) :=
  pullback.lift_snd _ _ _

theorem twist_comp (σ τ : k ≃+* k) (hσ : Spec.map (CommRingCat.ofHom (σ : k →+* k)) ≫ s = s)
    (hτ : Spec.map (CommRingCat.ofHom (τ : k →+* k)) ≫ s = s)
    (hστ : Spec.map (CommRingCat.ofHom ((τ.trans σ : k ≃+* k) : k →+* k)) ≫ s = s) :
    twist πX s σ hσ ≫ twist πX s τ hτ = twist πX s (τ.trans σ) hστ := by
  apply pullback.hom_ext
  · rw [twist_fst, Category.assoc, twist_fst, twist_fst]
  · rw [twist_snd, Category.assoc, twist_snd, ← Category.assoc, twist_snd, Category.assoc, ← Spec.map_comp]
    rfl

theorem twist_symm_comp (σ : k ≃+* k) (hσ : Spec.map (CommRingCat.ofHom (σ : k →+* k)) ≫ s = s)
    (hσ' : Spec.map (CommRingCat.ofHom (σ.symm : k →+* k)) ≫ s = s) :
    twist πX s σ.symm hσ' ≫ twist πX s σ hσ = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, twist_fst, twist_fst, Category.id_comp]
  · rw [Category.assoc, twist_snd, ← Category.assoc, twist_snd, Category.assoc, ← Spec.map_comp, Category.id_comp]
    have : CommRingCat.ofHom (σ : k →+* k) ≫ CommRingCat.ofHom (σ.symm : k →+* k) = 𝟙 _ := by
      ext a; exact σ.symm_apply_apply a
    rw [this, Spec.map_id, Category.comp_id]

theorem twist_comp_symm (σ : k ≃+* k) (hσ : Spec.map (CommRingCat.ofHom (σ : k →+* k)) ≫ s = s)
    (hσ' : Spec.map (CommRingCat.ofHom (σ.symm : k →+* k)) ≫ s = s) :
    twist πX s σ hσ ≫ twist πX s σ.symm hσ' = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, twist_fst, twist_fst, Category.id_comp]
  · rw [Category.assoc, twist_snd, ← Category.assoc, twist_snd, Category.assoc, ← Spec.map_comp, Category.id_comp]
    have : CommRingCat.ofHom (σ.symm : k →+* k) ≫ CommRingCat.ofHom (σ : k →+* k) = 𝟙 _ := by
      ext a; exact σ.apply_symm_apply a
    rw [this, Spec.map_id, Category.comp_id]

def twistIso (σ : k ≃+* k) (hσ : Spec.map (CommRingCat.ofHom (σ : k →+* k)) ≫ s = s)
    (hσ' : Spec.map (CommRingCat.ofHom (σ.symm : k →+* k)) ≫ s = s) : pullback πX s ≅ pullback πX s :=
  ⟨twist πX s σ hσ, twist πX s σ.symm hσ', twist_comp_symm πX s σ hσ hσ', twist_symm_comp πX s σ hσ hσ'⟩

def galAut (σ : k ≃+* k) (hσ : Spec.map (CommRingCat.ofHom (σ : k →+* k)) ≫ s = s)
    (hσ' : Spec.map (CommRingCat.ofHom (σ.symm : k →+* k)) ≫ s = s) :
    letI := (baseToFunctionField (pullback.snd πX s)).toAlgebra
    SemilinearAut k ↥(pullback πX s).functionField :=
  letI := (baseToFunctionField (pullback.snd πX s)).toAlgebra
  ⟨(equivOfIso (twistIso πX s σ hσ hσ'), σ), fun a =>
    pull_baseToFunctionField_twist (twist πX s σ hσ) (specializes_of_iso (twistIso πX s σ hσ hσ'))
      (pullback.snd πX s) (pullback.snd πX s) σ (twist_snd πX s σ hσ) a⟩

theorem galAut_smul (σ : k ≃+* k) (hσ : Spec.map (CommRingCat.ofHom (σ : k →+* k)) ≫ s = s)
    (hσ' : Spec.map (CommRingCat.ofHom (σ.symm : k →+* k)) ≫ s = s) (z : ↥(pullback πX s).functionField) :
    letI := (baseToFunctionField (pullback.snd πX s)).toAlgebra
    galAut πX s σ hσ hσ' • z = pull (twist πX s σ hσ) (specializes_of_iso (twistIso πX s σ hσ hσ')) z := rfl

theorem baseAut_galAut (σ : k ≃+* k) (hσ : Spec.map (CommRingCat.ofHom (σ : k →+* k)) ≫ s = s)
    (hσ' : Spec.map (CommRingCat.ofHom (σ.symm : k →+* k)) ≫ s = s) :
    letI := (baseToFunctionField (pullback.snd πX s)).toAlgebra
    SemilinearAut.baseAut (galAut πX s σ hσ hσ') = σ := rfl

omit [IsIntegral X] [IsIntegral ↑(pullback πX s)] in
theorem pull_congr {Z : Scheme.{0}} [IrreducibleSpace ↥Z] [IrreducibleSpace ↥(pullback πX s)]
    (f g : Z ⟶ pullback πX s) (h : f = g)
    (hf : f.base (genericPoint Z) ⤳ genericPoint ↑(pullback πX s)) (hg : g.base (genericPoint Z) ⤳ genericPoint ↑(pullback πX s))
    (z : ↥(pullback πX s).functionField) : pull f hf z = pull g hg z := by
  subst h; rfl

theorem galAut_smul_toBarMap (hinj : Function.Injective (Spec.preimage s).hom) (σ : k ≃+* k)
    (hσ : Spec.map (CommRingCat.ofHom (σ : k →+* k)) ≫ s = s)
    (hσ' : Spec.map (CommRingCat.ofHom (σ.symm : k →+* k)) ≫ s = s) (x : X.functionField) :
    letI := (baseToFunctionField (pullback.snd πX s)).toAlgebra
    galAut πX s σ hσ hσ' • toBarMap πX s hinj x = toBarMap πX s hinj x := by
  show pull (twist πX s σ hσ) (specializes_of_iso (twistIso πX s σ hσ hσ'))
      (pull (pullback.fst πX s) (fst_genericPoint_specializes πX s hinj) x) = _
  rw [← CommRingCat.comp_apply, ← pull_comp,
    pull_congr' _ _ (twist_fst πX s σ hσ) _ (fst_genericPoint_specializes πX s hinj)]
  rfl

theorem nonempty_preimage_fst (hinj : Function.Injective (Spec.preimage s).hom) (U : X.Opens)
    [hU : Nonempty (Scheme.Opens.toScheme U)] : Nonempty (Scheme.Opens.toScheme ((pullback.fst πX s) ⁻¹ᵁ U)) := by
  obtain ⟨⟨x, hx⟩⟩ := hU
  have hη : genericPoint X ∈ U := ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr ⟨x, trivial, hx⟩
  exact ⟨⟨_, (fst_genericPoint_specializes πX s hinj).mem_open U.isOpen hη⟩⟩

end Geometric

section GalHom

variable {D : ℕ} {X : Scheme.{0}} (πX : X ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))) [IsIntegral X]
  (s : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))) [IsIntegral ↑(pullback πX s)]

omit [IsIntegral ↑(pullback πX s)] in
theorem specMap_comp_eq (τ : (AlgebraicClosure ℚ) →+* (AlgebraicClosure ℚ)) : Spec.map (CommRingCat.ofHom τ) ≫ s = s := by
  conv_rhs => rw [← Spec.map_preimage s]
  conv_lhs => rw [← Spec.map_preimage s, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (ringHom_ext_localizationAway _ _)

def twistG (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) : pullback πX s ⟶ pullback πX s :=
  twist πX s (σ : (AlgebraicClosure ℚ) ≃+* (AlgebraicClosure ℚ)) (specMap_comp_eq s _)

def twistGIso (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) : pullback πX s ≅ pullback πX s :=
  twistIso πX s (σ : (AlgebraicClosure ℚ) ≃+* (AlgebraicClosure ℚ)) (specMap_comp_eq s _) (specMap_comp_eq s _)

theorem twistGIso_hom (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) : (twistGIso πX s σ).hom = twistG πX s σ := rfl

@[scoped simp] theorem twistG_fst (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) : twistG πX s σ ≫ pullback.fst πX s = pullback.fst πX s :=
  twist_fst πX s _ _

@[scoped simp] theorem twistG_snd (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) :
    twistG πX s σ ≫ pullback.snd πX s = pullback.snd πX s ≫ Spec.map (CommRingCat.ofHom (σ : (AlgebraicClosure ℚ) →+* (AlgebraicClosure ℚ))) :=
  twist_snd πX s _ _

theorem twistG_mul (σ τ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) : twistG πX s (σ * τ) = twistG πX s σ ≫ twistG πX s τ := by
  apply pullback.hom_ext
  · rw [twistG_fst, Category.assoc, twistG_fst, twistG_fst]
  · rw [twistG_snd, Category.assoc, twistG_snd, ← Category.assoc, twistG_snd, Category.assoc, ← Spec.map_comp]
    rfl

theorem specializes_twistG (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) :
    (twistG πX s σ).base (genericPoint ↑(pullback πX s)) ⤳ genericPoint ↑(pullback πX s) :=
  specializes_of_iso (twistGIso πX s σ)

def galElt (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) :
    letI := (baseToFunctionField (pullback.snd πX s)).toAlgebra
    SemilinearAut (AlgebraicClosure ℚ) ↥(pullback πX s).functionField :=
  galAut πX s (σ : (AlgebraicClosure ℚ) ≃+* (AlgebraicClosure ℚ)) (specMap_comp_eq s _) (specMap_comp_eq s _)

theorem galElt_smul (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) (z : ↥(pullback πX s).functionField) :
    letI := (baseToFunctionField (pullback.snd πX s)).toAlgebra
    galElt πX s σ • z = pull (twistG πX s σ) (specializes_twistG πX s σ) z := rfl

theorem galElt_toRingAut_apply (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) (z : ↥(pullback πX s).functionField) :
    letI := (baseToFunctionField (pullback.snd πX s)).toAlgebra
    (galElt πX s σ).1.1 z = pull (twistG πX s σ) (specializes_twistG πX s σ) z := rfl

theorem galElt_mul (σ τ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) :
    letI := (baseToFunctionField (pullback.snd πX s)).toAlgebra
    galElt πX s (σ * τ) = galElt πX s σ * galElt πX s τ := by
  letI := (baseToFunctionField (pullback.snd πX s)).toAlgebra
  apply Subtype.ext; apply Prod.ext
  · apply RingEquiv.ext; intro z
    show pull (twistG πX s (σ * τ)) (specializes_twistG πX s (σ * τ)) z =
      pull (twistG πX s σ) (specializes_twistG πX s σ) (pull (twistG πX s τ) (specializes_twistG πX s τ) z)
    rw [← CommRingCat.comp_apply, ← pull_comp, pull_congr' _ _ (twistG_mul πX s σ τ).symm]
  · apply RingEquiv.ext; intro a; rfl

def galHom : letI := (baseToFunctionField (pullback.snd πX s)).toAlgebra
    ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) →* SemilinearAut (AlgebraicClosure ℚ) ↥(pullback πX s).functionField :=
  letI := (baseToFunctionField (pullback.snd πX s)).toAlgebra
  MonoidHom.mk' (galElt πX s) (galElt_mul πX s)

theorem galHom_apply (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) :
    letI := (baseToFunctionField (pullback.snd πX s)).toAlgebra
    galHom πX s σ = galElt πX s σ := rfl

theorem baseAut_galHom (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) :
    letI := (baseToFunctionField (pullback.snd πX s)).toAlgebra
    SemilinearAut.baseAut (galHom πX s σ) = (σ : (AlgebraicClosure ℚ) ≃+* (AlgebraicClosure ℚ)) := rfl

theorem galHom_smul_toBarMap (hinj : Function.Injective (Spec.preimage s).hom) (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) (x : X.functionField) :
    letI := (baseToFunctionField (pullback.snd πX s)).toAlgebra
    galHom πX s σ • toBarMap πX s hinj x = toBarMap πX s hinj x :=
  galAut_smul_toBarMap πX s hinj _ _ _ x

end GalHom

section Pts

variable {D : ℕ} {X : Scheme.{0}} (πX : X ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))) [IsIntegral X]
  (s : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))) [IsIntegral ↑(pullback πX s)]

omit [IsIntegral X] [IsIntegral ↑(pullback πX s)] in

theorem nonempty_preimage_of_isIso {Z W : Scheme.{0}} (f : Z ⟶ W) [IsIso f] (U : W.Opens)
    [h : Nonempty (Scheme.Opens.toScheme U)] : Nonempty (Scheme.Opens.toScheme (f ⁻¹ᵁ U)) := by
  obtain ⟨⟨y, hy⟩⟩ := h
  refine ⟨⟨(inv f).base y, ?_⟩⟩
  show f.base ((inv f).base y) ∈ (U : Set W)
  have h1 : (inv f ≫ f).base y = y := by simp
  have h2 : (inv f ≫ f).base y = f.base ((inv f).base y) := Scheme.Hom.comp_apply _ _ _
  rw [← h2, h1]
  exact hy

omit [IsIntegral X] [IsIntegral ↑(pullback πX s)] in

theorem germ_key {Z W : Scheme.{0}} [IrreducibleSpace ↥Z] (U : W.Opens) (t : Γ(W, U)) (E₁ E₂ : Z ⟶ W) (hEE : E₁ = E₂)
    [Nonempty (Scheme.Opens.toScheme (E₁ ⁻¹ᵁ U))] [Nonempty (Scheme.Opens.toScheme (E₂ ⁻¹ᵁ U))] :
    Z.germToFunctionField (E₁ ⁻¹ᵁ U) ((E₁.app U).hom t) = Z.germToFunctionField (E₂ ⁻¹ᵁ U) ((E₂.app U).hom t) := by
  subst hEE; rfl

end Pts

section Closure

variable {R₀ : Type} [CommRing R₀] [Algebra R₀ ℚ] {X : Scheme.{0}} (πX : X ⟶ Spec (CommRingCat.of R₀)) [IsIntegral X]
  [CharZero X.functionField]
  [IsIntegral ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ))))]

theorem closure_and_linearIndependent
    (φ : X.functionField ≃+* ↥(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))).functionField)
    (hφc : ∀ z : ℚ, φ (algebraMap ℚ X.functionField z) = baseToFunctionField (pullback.snd πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))) z)
    (hφg : ∀ (U : X.Opens) [Nonempty (U : Scheme.{0})]
        [Nonempty (((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))) ⁻¹ᵁ U : (pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))).Opens) : Scheme.{0})] (t : Γ(X, U)),
        φ (X.germToFunctionField U t) = (pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))).germToFunctionField ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))) ⁻¹ᵁ U) ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))).app U t))
    (s' : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of R₀)) (hs' : s' = (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ))))
    [IsIntegral ↑(pullback πX s')] (hinj' : Function.Injective (Spec.preimage s').hom)
    (hinjQ : Function.Injective (Spec.preimage (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))).hom) :
    letI := (baseToFunctionField (pullback.snd πX s')).toAlgebra
    Subfield.closure (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(pullback πX s').functionField) ∪ Set.range (toBarMap πX s' hinj')) = ⊤ ∧
    ∀ fs : Finset X.functionField, LinearIndependent ℚ (fun x : fs => (x : X.functionField)) →
      LinearIndependent (AlgebraicClosure ℚ) (fun x : fs => toBarMap πX s' hinj' (x : X.functionField)) := by
  subst hs'
  letI algY := (baseToFunctionField (pullback.snd πX ((Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))))).toAlgebra
  letI algXQ : Algebra ℚ ↥(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))).functionField := (baseToFunctionField (pullback.snd πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ))))).toAlgebra

  let ι0 := pullbackLeftPullbackSndIso πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ))) (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))
  haveI : IsIntegral ↑(pullback (pullback.snd πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))) (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))) := IsIntegral.of_isIso ι0.inv
  letI algXQK : Algebra (AlgebraicClosure ℚ) ↥(pullback (pullback.snd πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))) (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))).functionField :=
    (baseToFunctionField (pullback.snd (pullback.snd πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))) (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))))).toAlgebra
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  obtain ⟨Φ, hΦ⟩ := exists_algEquiv_tensorProduct_functionField_pullback_of_isAlgebraic (AlgebraicClosure ℚ) (pullback.snd πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ))))

  let Ψ : (AlgebraicClosure ℚ) ⊗[ℚ] ↥(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))).functionField ≃+* ↥(pullback πX ((Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ))))).functionField :=
    Φ.toRingEquiv.trans (equivOfIso ι0.symm)
  have hΨ : ∀ τ, Ψ τ = pull ι0.inv (specializes_of_iso ι0.symm) (Φ τ) := fun _ => rfl

  have hΨc : ∀ c : (AlgebraicClosure ℚ), Ψ (c ⊗ₜ[ℚ] 1) = algebraMap (AlgebraicClosure ℚ) _ c := by
    intro c
    rw [hΨ]
    have h1 : Φ (c ⊗ₜ[ℚ] (1 : ↥(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))).functionField)) = algebraMap (AlgebraicClosure ℚ) _ c := by
      rw [show c ⊗ₜ[ℚ] (1 : ↥(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))).functionField) = c • (1 : (AlgebraicClosure ℚ) ⊗[ℚ] ↥(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))).functionField) by
        rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul, map_one,
        Algebra.smul_def, mul_one]
    rw [h1]
    exact pull_baseToFunctionField ι0.inv _ (pullback.snd πX ((Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ))))) (pullback.snd (pullback.snd πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))) (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))))
      (pullbackLeftPullbackSndIso_inv_snd_snd _ _ _) c

  have hΨf : ∀ f : X.functionField, Ψ (1 ⊗ₜ[ℚ] φ f) = toBarMap πX ((Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))) hinj' f := by
    intro f
    obtain ⟨U, hηU, r, hr⟩ := TopCat.Presheaf.germ_exist X.presheaf (x := genericPoint X) f
    haveI : Nonempty (Scheme.Opens.toScheme U) := ⟨⟨_, hηU⟩⟩
    haveI : Nonempty (Scheme.Opens.toScheme ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))) ⁻¹ᵁ U)) := nonempty_preimage_fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ))) hinjQ U
    haveI : Nonempty (Scheme.Opens.toScheme ((pullback.fst πX ((Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ))))) ⁻¹ᵁ U)) := nonempty_preimage_fst πX _ hinj' U
    haveI : Nonempty (Scheme.Opens.toScheme ((pullback.fst (pullback.snd πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))) (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))) ⁻¹ᵁ ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))) ⁻¹ᵁ U))) := by
      have h0 := nonempty_preimage_of_isIso ι0.hom ((pullback.fst πX ((Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ))))) ⁻¹ᵁ U)
      have h1 : ι0.hom ⁻¹ᵁ ((pullback.fst πX ((Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ))))) ⁻¹ᵁ U) =
          (pullback.fst (pullback.snd πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))) (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))) ⁻¹ᵁ ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))) ⁻¹ᵁ U) := by
        show (ι0.hom ≫ pullback.fst πX ((Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ))))) ⁻¹ᵁ U =
          (pullback.fst (pullback.snd πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))) (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))) ≫ pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))) ⁻¹ᵁ U
        rw [pullbackLeftPullbackSndIso_hom_fst]
      rw [h1] at h0; exact h0
    haveI : Nonempty (Scheme.Opens.toScheme (ι0.inv ⁻¹ᵁ ((pullback.fst (pullback.snd πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))) (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))) ⁻¹ᵁ ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))) ⁻¹ᵁ U)))) :=
      nonempty_preimage_of_isIso ι0.inv _
    haveI : Nonempty (Scheme.Opens.toScheme ((ι0.inv ≫ pullback.fst (pullback.snd πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))) (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))) ≫ pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))) ⁻¹ᵁ U)) := by
      rw [pullbackLeftPullbackSndIso_inv_fst]; infer_instance
    have hf : X.germToFunctionField U r = f := hr
    rw [← hf, hφg U r, hΨ, hΦ ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))) ⁻¹ᵁ U) ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))).app U r),
      pull_germToFunctionField ι0.inv (specializes_of_iso ι0.symm) _ _, toBarMap_germ]
    exact germ_key U r (ι0.inv ≫ pullback.fst (pullback.snd πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))) (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))) ≫ pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))) _
      (pullbackLeftPullbackSndIso_inv_fst _ _ _)
  refine ⟨?_, ?_⟩
  · rw [eq_top_iff]
    intro w _
    have hall : ∀ τ : (AlgebraicClosure ℚ) ⊗[ℚ] ↥(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))).functionField, Ψ τ ∈
        Subfield.closure (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(pullback πX ((Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ))))).functionField) ∪
          Set.range (toBarMap πX ((Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))) hinj')) := by
      intro τ
      induction τ using TensorProduct.induction_on with
      | zero => rw [map_zero]; exact Subfield.zero_mem _
      | tmul c g =>
        have hcg : c ⊗ₜ[ℚ] g = (c ⊗ₜ[ℚ] (1 : ↥(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ ℚ)))).functionField)) * ((1 : (AlgebraicClosure ℚ)) ⊗ₜ[ℚ] g) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        rw [hcg, map_mul, hΨc, ← φ.apply_symm_apply g, hΨf]
        exact Subfield.mul_mem _ (Subfield.subset_closure (Or.inl ⟨c, rfl⟩)) (Subfield.subset_closure (Or.inr ⟨_, rfl⟩))
      | add a b ha hb => rw [map_add]; exact Subfield.add_mem _ ha hb
    rw [← Ψ.apply_symm_apply w]
    exact hall _
  · intro fs hli
    have h1 : LinearIndependent ℚ (fun x : fs => φ (x : X.functionField)) := by
      refine LinearIndependent.map_of_injective_injective (R' := ℚ) hli id φ.toAddMonoidHom (fun r hr => hr)
        (fun m hm => φ.injective (by rw [map_zero]; exact hm)) (fun r m => ?_)
      show φ (r • m) = r • φ m
      rw [Algebra.smul_def, map_mul, hφc, Algebra.smul_def]; rfl
    have h2 : LinearIndependent (AlgebraicClosure ℚ) (fun x : fs => (1 : (AlgebraicClosure ℚ)) ⊗ₜ[ℚ] φ (x : X.functionField)) :=
      Module.Flat.linearIndependent_one_tmul h1
    have h3 := LinearIndependent.map_of_injective_injective (R' := (AlgebraicClosure ℚ)) h2 id Ψ.toAddMonoidHom (fun r hr => hr)
      (fun m hm => Ψ.injective (by rw [map_zero]; exact hm)) (fun c τ => by
        show Ψ (c • τ) = c • Ψ τ
        rw [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, map_mul, hΨc,
          Algebra.smul_def])
    convert h3 using 1 <;> try with_reducible_and_instances rfl
    funext x
    exact (hΨf (x : X.functionField)).symm

end Closure

section Stalk

theorem coe_toValuationSubring_pointEquivPlace {K : Type} [Field K] {L : Type} [Field L] [Algebra K L]
    [IsAlgClosed K] (M : CurveModel K L)
    (x : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _}) :
    ((M.pointEquivPlace x).toValuationSubring : Set L) =
      M.ffEquiv.symm '' ((algebraMap (M.C.presheaf.stalk (x.1.base (IsLocalRing.closedPoint K)))
        M.C.functionField).range : Set M.C.functionField) := by
  rw [CurveModel.pointEquivPlace_apply]
  have h := M.range_stalk_eq (pointEquivClosedPoint M.toBase x)
  rw [← RingHom.map_range] at h
  have h' := congrArg (fun S : Subring L => (S : Set L)) h
  simp only [Subring.coe_map] at h'
  exact h'.symm

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]

theorem pull_mem_range_algebraMap_stalk_iff (f : Y ⟶ X) [Flat f] (h : f.base (genericPoint Y) ⤳ genericPoint X)
    (y : Y) (z : X.functionField) :
    pull f h z ∈ (algebraMap (Y.presheaf.stalk y) Y.functionField).range ↔
      z ∈ (algebraMap (X.presheaf.stalk (f.base y)) X.functionField).range := by
  constructor
  · rintro ⟨b, hb⟩
    letI alg : Algebra (X.presheaf.stalk (f.base y)) (Y.presheaf.stalk y) := (f.stalkMap y).hom.toAlgebra
    haveI : Module.Flat (X.presheaf.stalk (f.base y)) (Y.presheaf.stalk y) := Flat.stalkMap f y
    haveI : IsLocalHom (algebraMap (X.presheaf.stalk (f.base y)) (Y.presheaf.stalk y)) :=
      inferInstanceAs (IsLocalHom (f.stalkMap y).hom)
    haveI : Module.FaithfullyFlat (X.presheaf.stalk (f.base y)) (Y.presheaf.stalk y) :=
      Module.FaithfullyFlat.of_flat_of_isLocalHom
    obtain ⟨a₁, a₂, ha₂, rfl⟩ := IsFractionRing.div_surjective (A := X.presheaf.stalk (f.base y)) z
    have ha₂' : algebraMap (X.presheaf.stalk (f.base y)) X.functionField a₂ ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ha₂

    have key : (f.stalkMap y).hom a₁ = b * (f.stalkMap y).hom a₂ := by
      apply IsFractionRing.injective (Y.presheaf.stalk y) Y.functionField
      rw [map_mul, ← pull_algebraMap f h y a₁, ← pull_algebraMap f h y a₂, hb, ← map_mul,
        div_mul_cancel₀ _ ha₂']
    have hmem : a₁ ∈ Ideal.span {a₂} := by
      rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := Y.presheaf.stalk y) (Ideal.span {a₂}), Ideal.mem_comap,
        Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton']
      exact ⟨b, key.symm⟩
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
    refine ⟨c, ?_⟩
    rw [eq_div_iff ha₂', ← map_mul, hc]
  · rintro ⟨a, rfl⟩
    exact ⟨(f.stalkMap y).hom a, (pull_algebraMap f h y a).symm⟩

end Stalk

end C3FFPkg
p2m_reactivate "P2MW.S_CerednikDrinfeld_exists_barFunctionField_curveModel_of_smoothProperCurve_of_two_mul_dvd.C3FFPkg"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_exists_barFunctionField_curveModel_of_smoothProperCurve_of_two_mul_dvd.C3FFPkg"

open C3FFPkg C3FFPkg.FunctionFieldPull in
set_option maxHeartbeats 8000000 in

theorem solution
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime]
    (D : ℕ) [NeZero D] (hD : 2 * N * q * q' ∣ D)
    (X : Scheme.{0}) [hXint : IsIntegral X]
    (πX : X ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
    (hproper : IsProper πX) (hsmooth : SmoothOfRelativeDimension 1 πX)
    (hgeom : ∀ (k : Type) [Field k] [IsAlgClosed k]
      (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))),
      IsIntegral (CategoryTheory.Limits.pullback πX s))
    [hchar : CharZero X.functionField]
    (halg : ∀ x : X.functionField, IsAlgebraic ℚ x → x ∈ Set.range (algebraMap ℚ X.functionField))
    (sbar : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
    (sbar_over : sbar ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ (Localization.Away ((D : ℕ) : ℤ)))) =
      Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) :
    ∃ (_ : IsCurveOver ℚ X.functionField) (_ : Algebra.EssFiniteType ℚ X.functionField)
      (Fbar : Type) (_ : Field Fbar) (_ : Algebra (AlgebraicClosure ℚ) Fbar)
      (_ : IsCurveOver (AlgebraicClosure ℚ) Fbar) (_ : Algebra.EssFiniteType (AlgebraicClosure ℚ) Fbar)
      (toBar : X.functionField →+* Fbar)
      (gal : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* SemilinearAut (AlgebraicClosure ℚ) Fbar)
      (𝔐 : AlgebraicCurve.CurveModel (AlgebraicClosure ℚ) Fbar)
      (e𝔐 : 𝔐.C ⟶ CategoryTheory.Limits.pullback πX sbar) (_ : IsIso e𝔐),

      (∀ r : ℚ, toBar (algebraMap ℚ X.functionField r) =
        algebraMap (AlgebraicClosure ℚ) Fbar (algebraMap ℚ (AlgebraicClosure ℚ) r)) ∧
      Subfield.closure (Set.range (algebraMap (AlgebraicClosure ℚ) Fbar) ∪ Set.range toBar) = ⊤ ∧
      (∀ s : Finset X.functionField, LinearIndependent ℚ (fun x : s => (x : X.functionField)) →
        LinearIndependent (AlgebraicClosure ℚ) (fun x : s => toBar (x : X.functionField))) ∧

      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        SemilinearAut.baseAut (gal σ) = (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ)) ∧
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : X.functionField), gal σ • toBar x = toBar x) ∧

      e𝔐 ≫ CategoryTheory.Limits.pullback.snd πX sbar = 𝔐.toBase ∧
      (∀ (U : X.Opens) [Nonempty (Scheme.Opens.toScheme U)]
        [Nonempty (Scheme.Opens.toScheme
          ((TopologicalSpace.Opens.map (e𝔐 ≫ CategoryTheory.Limits.pullback.fst πX sbar).base).obj U))]
        (t : X.presheaf.obj (Opposite.op U)),
        𝔐.ffEquiv.symm (𝔐.C.germToFunctionField
          ((TopologicalSpace.Opens.map (e𝔐 ≫ CategoryTheory.Limits.pullback.fst πX sbar).base).obj U)
          (((e𝔐 ≫ CategoryTheory.Limits.pullback.fst πX sbar).app U).hom t)) =
        toBar (X.germToFunctionField U t)) ∧

      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (P : Place (AlgebraicClosure ℚ) Fbar),
        (𝔐.pointEquivPlace.symm (gal σ • P)).1 ≫ e𝔐 ≫ CategoryTheory.Limits.pullback.fst πX sbar =
          Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
            ((𝔐.pointEquivPlace.symm P).1 ≫ e𝔐 ≫ CategoryTheory.Limits.pullback.fst πX sbar)) ∧

      (∀ (P : Place (AlgebraicClosure ℚ) Fbar) (x : X.functionField),
        toBar x ∈ P.toValuationSubring ↔
          x ∈ (algebraMap (X.presheaf.stalk
            (((𝔐.pointEquivPlace.symm P).1 ≫ e𝔐 ≫ CategoryTheory.Limits.pullback.fst πX sbar).base default))
            X.functionField).range) := by
  classical

  have hn0 : ((D : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne D)
  let ψQ : (Localization.Away ((D : ℕ) : ℤ)) →+* ℚ := IsLocalization.Away.lift ((D : ℕ) : ℤ) (g := algebraMap ℤ ℚ)
    (by rw [isUnit_iff_ne_zero, eq_intCast, Int.cast_natCast]; exact hn0)
  letI algQ : Algebra (Localization.Away ((D : ℕ) : ℤ)) ℚ := ψQ.toAlgebra
  have hinjQ : Function.Injective (algebraMap (Localization.Away ((D : ℕ) : ℤ)) ℚ) := injective_of_localizationAway _

  have hsb : sbar = Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))) ≫ Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away ((D : ℕ) : ℤ)) ℚ)) := by
    rw [← Spec.map_comp, ← Spec.map_preimage sbar]
    congr 1
    exact CommRingCat.hom_ext (ringHom_ext_localizationAway _ _)
  have hinj : Function.Injective (Spec.preimage sbar).hom := injective_of_localizationAway _
  haveI : IsProper πX := hproper
  haveI : SmoothOfRelativeDimension 1 πX := hsmooth
  haveI hGI : GeometricallyIntegral πX := geometricallyIntegral_of_forall_isAlgClosed_isIntegral_pullback πX hgeom
  haveI : IsIntegral ↑(pullback πX sbar) := hgeom _ _

  haveI : IsIntegral ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away ((D : ℕ) : ℤ)) ℚ)))) := by
    have h := hGI; rw [GeometricallyIntegral.eq_geometrically] at h
    exact h (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away ((D : ℕ) : ℤ)) ℚ))) (pullback.fst _ _) (pullback.snd _ _)
      (IsPullback.of_hasPullback _ _)

  have hgerm : ∀ r : (Localization.Away ((D : ℕ) : ℤ)), (X.presheaf.germ ⊤ (genericPoint X) trivial).hom
      (πX.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))).inv.hom r)) = algebraMap ℚ X.functionField (algebraMap (Localization.Away ((D : ℕ) : ℤ)) ℚ r) := by
    intro r
    have := ringHom_ext_localizationAway
      ((X.presheaf.germ ⊤ (genericPoint X) trivial).hom.comp (πX.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))).inv.hom))
      ((algebraMap ℚ X.functionField).comp (algebraMap (Localization.Away ((D : ℕ) : ℤ)) ℚ))
    exact RingHom.congr_fun this r
  obtain ⟨φ, hφc, hφg⟩ := RatFF.ratFibreEquiv πX hinjQ hgerm
  letI algY : Algebra (AlgebraicClosure ℚ) ↥(pullback πX sbar).functionField := (baseToFunctionField (pullback.snd πX sbar)).toAlgebra

  obtain ⟨hcurveY, hessY, M, e, he, hgermY⟩ :=
    SmoothProperCurve.exists_curveModel_iso_pullback_germToFunctionField_eq_of_isAlgClosed (Localization.Away ((D : ℕ) : ℤ)) πX (AlgebraicClosure ℚ) sbar

  have hcurveX : IsCurveOver ℚ X.functionField :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
      (pullback.snd πX (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away ((D : ℕ) : ℤ)) ℚ)))) φ hφc
  have hessX : Algebra.EssFiniteType ℚ X.functionField := by
    letI algXQ : Algebra ℚ ↥(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away ((D : ℕ) : ℤ)) ℚ)))).functionField :=
      (baseToFunctionField (pullback.snd πX (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away ((D : ℕ) : ℤ)) ℚ))))).toAlgebra
    haveI : Algebra.EssFiniteType ℚ ↥(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away ((D : ℕ) : ℤ)) ℚ)))).functionField :=
      essFiniteType_functionField (pullback.snd πX (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away ((D : ℕ) : ℤ)) ℚ))))
    let f : ↥(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away ((D : ℕ) : ℤ)) ℚ)))).functionField →ₐ[ℚ] X.functionField :=
      { toRingHom := φ.symm.toRingHom
        commutes' := fun z => by
          show φ.symm (algebraMap ℚ _ z) = algebraMap ℚ X.functionField z
          rw [RingEquiv.symm_apply_eq]
          exact (hφc z).symm }
    exact Algebra.EssFiniteType.of_surjective f φ.symm.surjective
  refine ⟨hcurveX, hessX, ↥(pullback πX sbar).functionField, inferInstance, algY, hcurveY, hessY,
    toBarMap πX sbar hinj, galHom πX sbar, M, e.hom, inferInstance, ?_, ?_, ?_, fun σ => rfl, ?_, he, ?_, ?_, ?_⟩
  ·
    intro r
    rw [eq_ratCast, map_ratCast, eq_ratCast, map_ratCast]
  ·
    exact (closure_and_linearIndependent πX φ hφc hφg sbar hsb hinj (injective_of_localizationAway _)).1
  ·
    exact (closure_and_linearIndependent πX φ hφc hφg sbar hsb hinj (injective_of_localizationAway _)).2
  ·
    intro σ x
    exact galHom_smul_toBarMap πX sbar hinj σ x
  ·
    intro U hU hU' t
    haveI := nonempty_preimage_fst πX sbar hinj U
    haveI : Nonempty (Scheme.Opens.toScheme (e.hom ⁻¹ᵁ ((pullback.fst πX sbar) ⁻¹ᵁ U))) := hU'
    rw [toBarMap_germ]
    exact hgermY ((pullback.fst πX sbar) ⁻¹ᵁ U) (((pullback.fst πX sbar).app U).hom t)
  ·
    intro σ P
    haveI : IsIso (twistG πX sbar σ) := (twistGIso πX sbar σ).isIso_hom
    obtain ⟨h, hdef⟩ : ∃ h : M.C ⟶ M.C, h = e.hom ≫ twistG πX sbar σ ≫ e.inv := ⟨_, rfl⟩
    haveI : IsIso h := by rw [hdef]; infer_instance
    have heinv : e.inv ≫ M.toBase = pullback.snd πX sbar := by
      rw [← he, Iso.inv_hom_id_assoc]
    have hh : h ≫ M.toBase = M.toBase ≫ Spec.map (CommRingCat.ofHom (σ : (AlgebraicClosure ℚ) →+* (AlgebraicClosure ℚ))) := by
      rw [hdef]; simp only [Category.assoc]
      rw [heinv, twistG_snd, ← Category.assoc, he]
    have hhe : h ≫ e.hom = e.hom ≫ twistG πX sbar σ := by
      rw [hdef]; simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    obtain ⟨g, hgb, hgerm, hpt⟩ :=
      AlgebraicCurve.CurveModel.exists_semilinearAut_baseAut_eq_and_pointEquivPlace_eq_smul M (σ : (AlgebraicClosure ℚ) ≃+* (AlgebraicClosure ℚ)) h hh

    have hg : g = galHom πX sbar σ := by
      refine semilinearAut_ext g (galHom πX sbar σ) (fun z => ?_) hgb
      obtain ⟨U, hηU, t, ht⟩ := TopCat.Presheaf.germ_exist (pullback πX sbar).presheaf (x := genericPoint _) z
      haveI hUne : Nonempty (Scheme.Opens.toScheme U) := ⟨⟨_, hηU⟩⟩
      haveI : Nonempty (Scheme.Opens.toScheme (e.hom ⁻¹ᵁ U)) := nonempty_preimage_of_isIso e.hom U
      haveI : Nonempty (Scheme.Opens.toScheme (h ⁻¹ᵁ (e.hom ⁻¹ᵁ U))) := nonempty_preimage_of_isIso h _
      haveI : Nonempty (Scheme.Opens.toScheme ((twistG πX sbar σ) ⁻¹ᵁ U)) := nonempty_preimage_of_isIso _ U
      haveI : Nonempty (Scheme.Opens.toScheme (e.hom ⁻¹ᵁ ((twistG πX sbar σ) ⁻¹ᵁ U))) := nonempty_preimage_of_isIso e.hom _
      haveI : Nonempty (Scheme.Opens.toScheme ((h ≫ e.hom) ⁻¹ᵁ U)) := nonempty_preimage_of_isIso (h ≫ e.hom) U
      haveI : Nonempty (Scheme.Opens.toScheme ((e.hom ≫ twistG πX sbar σ) ⁻¹ᵁ U)) :=
        nonempty_preimage_of_isIso (e.hom ≫ twistG πX sbar σ) U
      have hz : (pullback πX sbar).germToFunctionField U t = z := ht
      calc g • z = g • M.ffEquiv.symm (M.C.germToFunctionField (e.hom ⁻¹ᵁ U) ((e.hom.app U).hom t)) := by
              rw [hgermY U t, hz]
        _ = M.ffEquiv.symm (M.C.germToFunctionField (h ⁻¹ᵁ (e.hom ⁻¹ᵁ U)) ((h.app _).hom ((e.hom.app U).hom t))) :=
              hgerm _ _
        _ = M.ffEquiv.symm (M.C.germToFunctionField ((e.hom ≫ twistG πX sbar σ) ⁻¹ᵁ U)
              (((e.hom ≫ twistG πX sbar σ).app U).hom t)) := by
              congr 1; exact germ_key U t (h ≫ e.hom) (e.hom ≫ twistG πX sbar σ) hhe
        _ = (pullback πX sbar).germToFunctionField ((twistG πX sbar σ) ⁻¹ᵁ U) (((twistG πX sbar σ).app U).hom t) :=
              hgermY ((twistG πX sbar σ) ⁻¹ᵁ U) (((twistG πX sbar σ).app U).hom t)
        _ = pull (twistG πX sbar σ) (specializes_twistG πX sbar σ) ((pullback πX sbar).germToFunctionField U t) :=
              (pull_germToFunctionField (twistG πX sbar σ) (specializes_twistG πX sbar σ) U t).symm
        _ = galHom πX sbar σ • z := by rw [hz]; rfl

    have hσσ : CommRingCat.ofHom ((σ.symm : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) : (AlgebraicClosure ℚ) →+* (AlgebraicClosure ℚ)) ≫ CommRingCat.ofHom (σ : (AlgebraicClosure ℚ) →+* (AlgebraicClosure ℚ)) = 𝟙 _ := by
      apply CommRingCat.hom_ext; ext a; exact σ.apply_symm_apply a
    have hinvh : inv h ≫ M.toBase = M.toBase ≫ Spec.map (CommRingCat.ofHom ((σ.symm : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) : (AlgebraicClosure ℚ) →+* (AlgebraicClosure ℚ))) := by
      rw [IsIso.inv_comp_eq, ← Category.assoc, hh, Category.assoc, ← Spec.map_comp, hσσ, Spec.map_id, Category.comp_id]
    obtain ⟨x, hxdef⟩ : ∃ x, x = M.pointEquivPlace.symm P := ⟨_, rfl⟩
    let y : {p : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ M.C // p ≫ M.toBase = 𝟙 _} :=
      ⟨Spec.map (CommRingCat.ofHom (σ : (AlgebraicClosure ℚ) →+* (AlgebraicClosure ℚ))) ≫ x.1 ≫ inv h, by
        rw [Category.assoc, Category.assoc, hinvh, ← Category.assoc x.1, x.2, Category.id_comp, ← Spec.map_comp, hσσ,
          Spec.map_id]⟩
    have hxy : y.1 ≫ h = Spec.map (CommRingCat.ofHom (σ : (AlgebraicClosure ℚ) →+* (AlgebraicClosure ℚ))) ≫ x.1 := by
      show (Spec.map (CommRingCat.ofHom (σ : (AlgebraicClosure ℚ) →+* (AlgebraicClosure ℚ))) ≫ x.1 ≫ inv h) ≫ h = _
      simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    have hplace : M.pointEquivPlace y = galHom πX sbar σ • P := by
      rw [hpt x y hxy, hg, hxdef, Equiv.apply_symm_apply]
    have hy : M.pointEquivPlace.symm (galHom πX sbar σ • P) = y := by
      rw [← hplace, Equiv.symm_apply_apply]
    have hfix : inv h ≫ e.hom ≫ pullback.fst πX sbar = e.hom ≫ pullback.fst πX sbar := by
      rw [IsIso.inv_comp_eq, ← Category.assoc, hhe, Category.assoc, twistG_fst]
    show (M.pointEquivPlace.symm (galHom πX sbar σ • P)).1 ≫ e.hom ≫ pullback.fst πX sbar =
      Spec.map (CommRingCat.ofHom (σ : (AlgebraicClosure ℚ) →+* (AlgebraicClosure ℚ))) ≫ ((M.pointEquivPlace.symm P).1 ≫ e.hom ≫ pullback.fst πX sbar)
    rw [hy, ← hxdef]
    show (Spec.map (CommRingCat.ofHom (σ : (AlgebraicClosure ℚ) →+* (AlgebraicClosure ℚ))) ≫ x.1 ≫ inv h) ≫ e.hom ≫ pullback.fst πX sbar = _
    simp only [Category.assoc]
    rw [hfix]
  ·
    intro P f

    haveI := IsScalarTower.of_algebraMap_eq' (R := ℤ) (S := (Localization.Away ((D : ℕ) : ℤ))) (A := ℚ)
      (IsLocalization.Away.lift_comp ((D : ℕ) : ℤ) (g := algebraMap ℤ ℚ)
        (by rw [isUnit_iff_ne_zero, eq_intCast, Int.cast_natCast]; exact hn0)).symm
    haveI : IsFractionRing (Localization.Away ((D : ℕ) : ℤ)) ℚ :=
      IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers ((D : ℕ) : ℤ)) (Localization.Away ((D : ℕ) : ℤ)) ℚ
    haveI : Module.Flat (Localization.Away ((D : ℕ) : ℤ)) ℚ := IsLocalization.flat ℚ (nonZeroDivisors (Localization.Away ((D : ℕ) : ℤ)))
    haveI hflat : Flat (pullback.fst πX sbar) := by
      have hs : Flat sbar := by
        rw [hsb, ← Spec.map_comp, Flat.SpecMap_iff]
        show ((algebraMap ℚ (AlgebraicClosure ℚ)).comp (algebraMap (Localization.Away ((D : ℕ) : ℤ)) ℚ)).Flat
        exact RingHom.Flat.comp (RingHom.flat_algebraMap_iff.mpr inferInstance) (RingHom.flat_algebraMap_iff.mpr inferInstance)
      exact MorphismProperty.pullback_fst (P := @Flat) _ _ hs

    have key : ∀ z : ↥(pullback πX sbar).functionField,
        M.ffEquiv.symm (pull e.hom (specializes_of_iso e) z) = z := by
      intro z
      obtain ⟨U, hηU, t, ht⟩ := TopCat.Presheaf.germ_exist (pullback πX sbar).presheaf (x := genericPoint _) z
      haveI : Nonempty (Scheme.Opens.toScheme U) := ⟨⟨_, hηU⟩⟩
      haveI : Nonempty (Scheme.Opens.toScheme (e.hom ⁻¹ᵁ U)) := nonempty_preimage_of_isIso e.hom U
      have hz : (pullback πX sbar).germToFunctionField U t = z := ht
      have h1 := pull_germToFunctionField e.hom (specializes_of_iso e) U t
      have h2 := hgermY U t
      rw [← hz, h1, h2]
    have hffE : ∀ w : ↥M.C.functionField, M.ffEquiv.symm w = (equivOfIso e).symm w := by
      intro w
      obtain ⟨z, rfl⟩ : ∃ z, w = equivOfIso e z := ⟨(equivOfIso e).symm w, ((equivOfIso e).apply_symm_apply w).symm⟩
      rw [RingEquiv.symm_apply_apply, equivOfIso_apply]
      exact key z

    obtain ⟨xM, hxM⟩ : ∃ xM, xM = M.pointEquivPlace.symm P := ⟨_, rfl⟩
    have hPx : M.pointEquivPlace xM = P := by rw [hxM, Equiv.apply_symm_apply]
    have hd : IsLocalRing.closedPoint (AlgebraicClosure ℚ) = (default : ↥(Spec (CommRingCat.of (AlgebraicClosure ℚ)))) := Subsingleton.elim _ _
    have hval : (P.toValuationSubring : Set ↥(pullback πX sbar).functionField) =
        ((algebraMap ((pullback πX sbar).presheaf.stalk (e.hom.base (xM.1.base default))) (pullback πX sbar).functionField).range :
          Set _) := by
      rw [← hPx, coe_toValuationSubring_pointEquivPlace M xM, hd]
      have himg : ∀ S : Set ↥M.C.functionField, (M.ffEquiv.symm : _ → _) '' S = ((equivOfIso e).symm : _ → _) '' S :=
        fun S => Set.image_congr (fun w _ => hffE w)
      rw [himg, image_equivOfIso_symm_range_stalk e]

    have hgoal : toBarMap πX sbar hinj f ∈ P.toValuationSubring ↔
        f ∈ (algebraMap (X.presheaf.stalk ((pullback.fst πX sbar).base (e.hom.base (xM.1.base default)))) X.functionField).range := by
      rw [← SetLike.mem_coe, hval, SetLike.mem_coe, toBarMap_apply]
      exact pull_mem_range_algebraMap_stalk_iff (pullback.fst πX sbar) (fst_genericPoint_specializes πX sbar hinj) _ f
    rw [hxM] at hgoal
    exact hgoal

end S_CerednikDrinfeld_exists_barFunctionField_curveModel_of_smoothProperCurve_of_two_mul_dvd
end P2MW
export P2MW.S_CerednikDrinfeld_exists_barFunctionField_curveModel_of_smoothProperCurve_of_two_mul_dvd (solution)
