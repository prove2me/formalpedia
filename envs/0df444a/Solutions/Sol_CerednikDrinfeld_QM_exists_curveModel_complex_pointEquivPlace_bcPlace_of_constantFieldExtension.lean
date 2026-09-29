-- Prove2me | solution 1 for CerednikDrinfeld.QM.exists_curveModel_complex_pointEquivPlace_bcPlace_of_constantFieldExtension
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/918a8e44-b02c-59a9-8c1e-808c37f3f172

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Theorems.Thm_AlgebraicGeometry_exists_ringEquiv_functionField_pullback_of_closure_eq_top_of_linearIndependent_of_isIntegral_pullback
import Theorems.Thm_AlgebraicCurve_exists_curveModel_iso_of_algEquiv_functionField
import Theorems.Thm_AlgebraicCurve_CurveModel_existsUnique_point_and_ord_eq_and_ord_eq_zero_of_iso_pullback_of_ffEquiv_symm_germToFunctionField_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_exists_curveModel_complex_pointEquivPlace_bcPlace_of_constantFieldExtension
p2m_attr_erase "instance" "AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup"
p2m_attr_erase "instance" "CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong"
p2m_attr_erase "simp" "AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq"
p2m_attr_erase "simp" "TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField MatrixGroups Topology
open CategoryTheory.Limits

theorem solution
    (M : ℕ) [NeZero M]
    (X : Scheme.{0}) [hXint : IsIntegral X]
    (πX : X ⟶ Spec (CommRingCat.of (Localization.Away ((M : ℕ) : ℤ))))
    (hproper : IsProper πX) (hsmooth1 : SmoothOfRelativeDimension 1 πX)
    (hgeom : ∀ (k : Type) [Field k] [IsAlgClosed k]
      (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away ((M : ℕ) : ℤ)))),
      IsIntegral (CategoryTheory.Limits.pullback πX s))
    (sbar : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of (Localization.Away ((M : ℕ) : ℤ))))
    (Fbar : Type) [Field Fbar] [Algebra (AlgebraicClosure ℚ) Fbar]
    [IsCurveOver (AlgebraicClosure ℚ) Fbar] [Algebra.EssFiniteType (AlgebraicClosure ℚ) Fbar]
    (𝔐 : AlgebraicCurve.CurveModel (AlgebraicClosure ℚ) Fbar)
    (e𝔐 : 𝔐.C ⟶ CategoryTheory.Limits.pullback πX sbar) (he𝔐 : IsIso e𝔐)
    (he𝔐_snd : e𝔐 ≫ CategoryTheory.Limits.pullback.snd πX sbar = 𝔐.toBase)
    (emb : AlgebraicClosure ℚ →+* ℂ)
    (Fc : Type) [Field Fc] [Algebra ℂ Fc] [AlgebraicCurve.IsCurveOver ℂ Fc] [Algebra.EssFiniteType ℂ Fc]
    (toC : Fbar →+* Fc) (bcPlace : Place (AlgebraicClosure ℚ) Fbar → Place ℂ Fc)
    (hcmp :
      (∀ z : AlgebraicClosure ℚ, toC (algebraMap (AlgebraicClosure ℚ) Fbar z) = algebraMap ℂ Fc (emb z)) ∧
      Subfield.closure (Set.range (algebraMap ℂ Fc) ∪ Set.range toC) = ⊤ ∧
      (∀ s : Finset Fbar, LinearIndependent (AlgebraicClosure ℚ) (fun x : s => (x : Fbar)) →
        LinearIndependent ℂ (fun x : s => toC (x : Fbar))) ∧
      (∀ (P : Place (AlgebraicClosure ℚ) Fbar) (x : Fbar), toC x ∈ (bcPlace P).toValuationSubring ↔ x ∈ P.toValuationSubring)) :
    ∃ (𝔐c : AlgebraicCurve.CurveModel ℂ Fc)
      (e𝔐c : 𝔐c.C ⟶ CategoryTheory.Limits.pullback πX (Spec.map (CommRingCat.ofHom emb) ≫ sbar)) (_ : IsIso e𝔐c),
      e𝔐c ≫ CategoryTheory.Limits.pullback.snd πX (Spec.map (CommRingCat.ofHom emb) ≫ sbar) = 𝔐c.toBase ∧
      ∀ P : Place (AlgebraicClosure ℚ) Fbar,
        (𝔐c.pointEquivPlace.symm (bcPlace P)).1 ≫ e𝔐c ≫
            CategoryTheory.Limits.pullback.fst πX (Spec.map (CommRingCat.ofHom emb) ≫ sbar) =
          Spec.map (CommRingCat.ofHom emb) ≫ (𝔐.pointEquivPlace.symm P).1 ≫ e𝔐 ≫ CategoryTheory.Limits.pullback.fst πX sbar := by
  classical
  obtain ⟨htoC, hcl, hli, hmem⟩ := hcmp
  haveI := he𝔐
  letI instAlg : Algebra (AlgebraicClosure ℚ) ℂ := emb.toAlgebra
  have halg : algebraMap (AlgebraicClosure ℚ) ℂ = emb := rfl
  have hbase : 𝔐.toBase = e𝔐 ≫ pullback.snd πX sbar := he𝔐_snd.symm

  have wJ : ((pullback.fst 𝔐.toBase (Spec.map (CommRingCat.ofHom (algebraMap (AlgebraicClosure ℚ) ℂ)))) ≫ e𝔐 ≫ pullback.fst πX sbar) ≫ πX = (pullback.snd 𝔐.toBase (Spec.map (CommRingCat.ofHom (algebraMap (AlgebraicClosure ℚ) ℂ)))) ≫ ((Spec.map (CommRingCat.ofHom (algebraMap (AlgebraicClosure ℚ) ℂ))) ≫ sbar) := by
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc e𝔐, he𝔐_snd, ← Category.assoc,
      pullback.condition, Category.assoc]
  have hJfst : pullback.lift _ _ wJ ≫ pullback.fst πX ((Spec.map (CommRingCat.ofHom (algebraMap (AlgebraicClosure ℚ) ℂ))) ≫ sbar) = (pullback.fst 𝔐.toBase (Spec.map (CommRingCat.ofHom (algebraMap (AlgebraicClosure ℚ) ℂ)))) ≫ e𝔐 ≫ pullback.fst πX sbar :=
    pullback.lift_fst _ _ _
  have hJsnd : pullback.lift _ _ wJ ≫ pullback.snd πX ((Spec.map (CommRingCat.ofHom (algebraMap (AlgebraicClosure ℚ) ℂ))) ≫ sbar) = (pullback.snd 𝔐.toBase (Spec.map (CommRingCat.ofHom (algebraMap (AlgebraicClosure ℚ) ℂ)))) := pullback.lift_snd _ _ _
  have wK : pullback.fst πX ((Spec.map (CommRingCat.ofHom (algebraMap (AlgebraicClosure ℚ) ℂ))) ≫ sbar) ≫ πX = (pullback.snd πX ((Spec.map (CommRingCat.ofHom (algebraMap (AlgebraicClosure ℚ) ℂ))) ≫ sbar) ≫ (Spec.map (CommRingCat.ofHom (algebraMap (AlgebraicClosure ℚ) ℂ)))) ≫ sbar := by
    rw [pullback.condition, Category.assoc]
  have wJi : (pullback.lift _ _ wK ≫ inv e𝔐) ≫ 𝔐.toBase = pullback.snd πX ((Spec.map (CommRingCat.ofHom (algebraMap (AlgebraicClosure ℚ) ℂ))) ≫ sbar) ≫ (Spec.map (CommRingCat.ofHom (algebraMap (AlgebraicClosure ℚ) ℂ))) := by
    rw [hbase, Category.assoc, IsIso.inv_hom_id_assoc, pullback.lift_snd]
  have hJ1 : pullback.lift _ _ wJ ≫ pullback.lift _ _ wJi = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.id_comp, ← cancel_mono e𝔐, Category.assoc, Category.assoc,
        IsIso.inv_hom_id, Category.comp_id]
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, hJfst, Category.assoc]
      · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, hJsnd, Category.assoc, ← hbase, pullback.condition]
    · rw [Category.assoc, pullback.lift_snd, hJsnd, Category.id_comp]
  have hJ2 : pullback.lift _ _ wJi ≫ pullback.lift _ _ wJ = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hJfst, Category.id_comp, ← Category.assoc, pullback.lift_fst, Category.assoc,
        IsIso.inv_hom_id_assoc, pullback.lift_fst]
    · rw [Category.assoc, hJsnd, pullback.lift_snd, Category.id_comp]
  haveI hJiso : IsIso (pullback.lift _ _ wJ) := ⟨⟨pullback.lift _ _ wJi, hJ1, hJ2⟩⟩

  haveI hTint : IsIntegral ↑(pullback πX ((Spec.map (CommRingCat.ofHom (algebraMap (AlgebraicClosure ℚ) ℂ))) ≫ sbar)) := hgeom ℂ ((Spec.map (CommRingCat.ofHom (algebraMap (AlgebraicClosure ℚ) ℂ))) ≫ sbar)
  haveI : Nonempty ↑(pullback 𝔐.toBase (Spec.map (CommRingCat.ofHom (algebraMap (AlgebraicClosure ℚ) ℂ)))) := ⟨(pullback.lift _ _ wJi).base (Nonempty.some inferInstance)⟩
  haveI hYint : IsIntegral ↑(pullback 𝔐.toBase (Spec.map (CommRingCat.ofHom (algebraMap (AlgebraicClosure ℚ) ℂ)))) := isIntegral_of_isOpenImmersion (pullback.lift _ _ wJ)

  haveI : IsProper (pullback.snd 𝔐.toBase (Spec.map (CommRingCat.ofHom (algebraMap (AlgebraicClosure ℚ) ℂ)))) := inferInstance
  haveI := (AlgebraicGeometry.smoothOfRelativeDimension_isStableUnderBaseChange (n := 1))
  haveI : SmoothOfRelativeDimension 1 (pullback.snd 𝔐.toBase (Spec.map (CommRingCat.ofHom (algebraMap (AlgebraicClosure ℚ) ℂ)))) := MorphismProperty.pullback_snd _ _ inferInstance
  obtain ⟨eFc, hconst, hgermA⟩ :=
    AlgebraicGeometry.exists_ringEquiv_functionField_pullback_of_closure_eq_top_of_linearIndependent_of_isIntegral_pullback
      (K' := ℂ) 𝔐.toBase 𝔐.ffEquiv 𝔐.ffEquiv_algebraMap toC htoC hcl hli
  obtain ⟨𝔐c, e, he, hgermE⟩ := AlgebraicCurve.exists_curveModel_iso_of_algEquiv_functionField ℂ
    (pullback 𝔐.toBase (Spec.map (CommRingCat.ofHom (algebraMap (AlgebraicClosure ℚ) ℂ)))) (pullback.snd 𝔐.toBase (Spec.map (CommRingCat.ofHom (algebraMap (AlgebraicClosure ℚ) ℂ)))) Fc eFc hconst

  have hsq : ∀ (U : 𝔐.C.Opens) [Nonempty (Scheme.Opens.toScheme U)]
      [Nonempty (Scheme.Opens.toScheme ((e.hom ≫ (pullback.fst 𝔐.toBase (Spec.map (CommRingCat.ofHom (algebraMap (AlgebraicClosure ℚ) ℂ))))) ⁻¹ᵁ U))] (s : Γ(𝔐.C, U)),
      𝔐c.ffEquiv.symm (𝔐c.C.germToFunctionField ((e.hom ≫ (pullback.fst 𝔐.toBase (Spec.map (CommRingCat.ofHom (algebraMap (AlgebraicClosure ℚ) ℂ))))) ⁻¹ᵁ U) (((e.hom ≫ (pullback.fst 𝔐.toBase (Spec.map (CommRingCat.ofHom (algebraMap (AlgebraicClosure ℚ) ℂ))))).app U).hom s)) =
        toC (𝔐.ffEquiv.symm (𝔐.C.germToFunctionField U s)) := by
    intro U _ hne s
    haveI : Nonempty (Scheme.Opens.toScheme ((pullback.fst 𝔐.toBase (Spec.map (CommRingCat.ofHom (algebraMap (AlgebraicClosure ℚ) ℂ)))) ⁻¹ᵁ U)) := by
      obtain ⟨⟨x, hx⟩⟩ := hne
      exact ⟨⟨e.hom.base x, hx⟩⟩
    haveI : Nonempty (Scheme.Opens.toScheme (e.hom ⁻¹ᵁ ((pullback.fst 𝔐.toBase (Spec.map (CommRingCat.ofHom (algebraMap (AlgebraicClosure ℚ) ℂ)))) ⁻¹ᵁ U))) := hne
    have h1 := hgermA U s
    have h2 := hgermE ((pullback.fst 𝔐.toBase (Spec.map (CommRingCat.ofHom (algebraMap (AlgebraicClosure ℚ) ℂ)))) ⁻¹ᵁ U) (((pullback.fst 𝔐.toBase (Spec.map (CommRingCat.ofHom (algebraMap (AlgebraicClosure ℚ) ℂ)))).app U).hom s)
    rw [← h1, RingEquiv.symm_apply_apply] at h2
    rw [← h2]
    congr 1
  obtain ⟨hL3, hL1, hL2⟩ :=
    AlgebraicCurve.CurveModel.existsUnique_point_and_ord_eq_and_ord_eq_zero_of_iso_pullback_of_ffEquiv_symm_germToFunctionField_eq
      (algebraMap (AlgebraicClosure ℚ) ℂ) 𝔐 𝔐c e he toC hsq

  have ordzero_mem : ∀ (Q : Place ℂ Fc) (g : Fc), g ≠ 0 → Q.ord g = 0 → g ∈ Q.toValuationSubring := by
    intro Q g hg h0
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible Q.toValuationSubring
    obtain ⟨u, hu⟩ := Q.exists_unit_mul_zpow hg hπ
    rw [h0, zpow_zero, mul_one] at hu
    rw [hu]; exact (u : Q.toValuationSubring).2
  have hcomap : ∀ P : Place (AlgebraicClosure ℚ) Fbar,
      (bcPlace P).toValuationSubring.comap toC = P.toValuationSubring := by
    intro P; ext x; rw [ValuationSubring.mem_comap]; exact hmem P x

  show ∃ (𝔐c : AlgebraicCurve.CurveModel ℂ Fc)
        (e𝔐c : 𝔐c.C ⟶ CategoryTheory.Limits.pullback πX (Spec.map (CommRingCat.ofHom (algebraMap (AlgebraicClosure ℚ) ℂ)) ≫ sbar)) (_ : IsIso e𝔐c),
        e𝔐c ≫ CategoryTheory.Limits.pullback.snd πX (Spec.map (CommRingCat.ofHom (algebraMap (AlgebraicClosure ℚ) ℂ)) ≫ sbar) = 𝔐c.toBase ∧
        ∀ P : Place (AlgebraicClosure ℚ) Fbar,
          (𝔐c.pointEquivPlace.symm (bcPlace P)).1 ≫ e𝔐c ≫
              CategoryTheory.Limits.pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap (AlgebraicClosure ℚ) ℂ)) ≫ sbar) =
            Spec.map (CommRingCat.ofHom (algebraMap (AlgebraicClosure ℚ) ℂ)) ≫ (𝔐.pointEquivPlace.symm P).1 ≫ e𝔐 ≫ CategoryTheory.Limits.pullback.fst πX sbar
  refine ⟨𝔐c, e.hom ≫ pullback.lift _ _ wJ, inferInstance, ?_, ?_⟩
  · rw [Category.assoc, hJsnd]; exact he
  · intro P
    obtain ⟨y, hy, hyuniq⟩ := hL3 (𝔐.pointEquivPlace.symm P)
    have hQ : bcPlace P = 𝔐c.pointEquivPlace y := by
      by_contra hne
      by_cases hex : ∃ (y₀ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔐.C // q ≫ 𝔐.toBase = 𝟙 _})
          (y' : {q : Spec (CommRingCat.of ℂ) ⟶ 𝔐c.C // q ≫ 𝔐c.toBase = 𝟙 _}),
          y'.1 ≫ (e.hom ≫ (pullback.fst 𝔐.toBase (Spec.map (CommRingCat.ofHom (algebraMap (AlgebraicClosure ℚ) ℂ))))) = (Spec.map (CommRingCat.ofHom (algebraMap (AlgebraicClosure ℚ) ℂ))) ≫ y₀.1 ∧ bcPlace P = 𝔐c.pointEquivPlace y'
      · obtain ⟨y₀, y', hy', hQ'⟩ := hex
        have hc := (hL1 y₀ y' hy').1
        have hP : 𝔐.pointEquivPlace y₀ = P :=
          AlgebraicCurve.Place.ext (by rw [← hc, ← hQ', hcomap])
        have hy₀ : y₀ = 𝔐.pointEquivPlace.symm P := by rw [← hP, Equiv.symm_apply_apply]
        subst hy₀
        exact hne (hQ'.trans (congrArg _ (hyuniq y' hy')))
      · push Not at hex
        have h0 := hL2 (bcPlace P) (fun y₀ y' hy' heq => hex y₀ y' hy' heq)
        apply P.ne_top'
        rw [← hcomap P, eq_top_iff]
        intro f _
        rw [ValuationSubring.mem_comap]
        rcases eq_or_ne f 0 with rfl | hf0
        · rw [map_zero]; exact (bcPlace P).toValuationSubring.zero_mem
        · exact ordzero_mem _ _ ((map_ne_zero toC).2 hf0) (h0 f hf0)
    have hy' : 𝔐c.pointEquivPlace.symm (bcPlace P) = y := by rw [hQ, Equiv.symm_apply_apply]
    rw [hy', Category.assoc, hJfst]
    have := congrArg (· ≫ e𝔐 ≫ pullback.fst πX sbar) hy
    simp only [Category.assoc] at this ⊢
    exact this

end S_CerednikDrinfeld_QM_exists_curveModel_complex_pointEquivPlace_bcPlace_of_constantFieldExtension
end P2MW
export P2MW.S_CerednikDrinfeld_QM_exists_curveModel_complex_pointEquivPlace_bcPlace_of_constantFieldExtension (solution)
