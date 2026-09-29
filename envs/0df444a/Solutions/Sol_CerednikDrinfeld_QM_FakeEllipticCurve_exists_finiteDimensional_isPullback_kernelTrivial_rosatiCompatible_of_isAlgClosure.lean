-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_finiteDimensional_isPullback_kernelTrivial_rosatiCompatible_of_isAlgClosure
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/166998e1-00e9-5f2d-8fe6-8f1df5eb933f

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullback_levelIff
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_IsPullbackVia_exists_comp_eq_and_isPullbackVia_of_comp_eq
import Theorems.Thm_AlgebraicGeometry_Polarisation_kernelTrivial_of_kernelTrivial_pullback_of_isPullback_of_field
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_eq_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_intermediateField_isInvertible_nonempty_pullback_iso_of_isAlgebraic
import Theorems.Thm_AlgebraicGeometry_Polarisation_rosatiCompatible_of_rosatiCompatible_pullback_of_isPullback_of_field
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_finiteDimensional_isPullback_kernelTrivial_rosatiCompatible_of_isAlgClosure
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModulePreGlue AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies SheafOfModules.isIso_ihomModelToIhom TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower"
p2m_attr_erase "instance" "CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app"
p2m_attr_erase "simp" "IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.glueComponent_glueMk AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.injEq AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.sizeOf_spec AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq"
p2m_attr_erase "simp" "TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq GoodReductionJacobian.prodInr_comp_prodFst GoodReductionJacobian.RelativeGroupLaw.prod_inv GoodReductionJacobian.prodInl_comp_prodSnd GoodReductionJacobian.prodInr_comp_prodSnd GoodReductionJacobian.prodInl_comp_prodFst GoodReductionJacobian.prodFstPt_prodPairPt GoodReductionJacobian.prodFst_coe GoodReductionJacobian.prodSndPt_prodPairPt GoodReductionJacobian.RelativeGroupLaw.prod_one GoodReductionJacobian.prodPairPt_coe GoodReductionJacobian.prodPairPt_prodFstPt_prodSndPt GoodReductionJacobian.prodFstPt_coe GoodReductionJacobian.RelativeGroupLaw.prod_mul GoodReductionJacobian.prodSndPt_coe GoodReductionJacobian.prodSnd_coe AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt"
p2m_attr_erase "simp" "AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans"

set_option autoImplicit false

open scoped TensorProduct Quaternion
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

namespace L4Stubs

noncomputable def inverseUnique' {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
    {L M M' : C} (e : L ⊗ M ≅ 𝟙_ C) (e' : L ⊗ M' ≅ 𝟙_ C) : M ≅ M' :=
  (λ_ M).symm ≪≫ (e'.symm ⊗ᵢ Iso.refl M) ≪≫ (β_ L M' ⊗ᵢ Iso.refl M) ≪≫ α_ M' L M ≪≫
    (Iso.refl M' ⊗ᵢ e) ≪≫ ρ_ M'

theorem nonempty_mumfordBundle_iso_of_iso {k : Type} [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f)
    (𝓛 𝓛' : A.Modules) (h : Scheme.Modules.IsInvertible 𝓛) (h' : Scheme.Modules.IsInvertible 𝓛') (e : 𝓛 ≅ 𝓛') :
    Nonempty (mumfordBundle f L 𝓛 ≅ mumfordBundle f L 𝓛') := by
  obtain ⟨-, ⟨e₁⟩⟩ := Scheme.Modules.IsInvertible.dual_monoidalV2 h
  obtain ⟨-, ⟨e₁'⟩⟩ := Scheme.Modules.IsInvertible.dual_monoidalV2 h'
  have ed : Scheme.Modules.dual 𝓛 ≅ Scheme.Modules.dual 𝓛' := inverseUnique' e₁ ((e ⊗ᵢ Iso.refl _) ≪≫ e₁')
  exact ⟨(Scheme.Modules.pullback (addMor f L)).mapIso e ⊗ᵢ
    ((Scheme.Modules.pullback (pullback.fst f f)).mapIso ed ⊗ᵢ (Scheme.Modules.pullback (pullback.snd f f)).mapIso ed)⟩

theorem locIsoOnBase_of_iso' {S' : Type} [CommRing S'] {X : Scheme.{0}} (g : X ⟶ Spec (CommRingCat.of S'))
    {M M' : X.Modules} (e : M ≅ M') : LocIsoOnBase g M M' :=
  fun _ => ⟨⊤, trivial, ⟨(Scheme.Modules.pullback _).mapIso e⟩⟩

theorem kernelTrivial_of_iso {k : Type} [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f)
    (𝓛 𝓛' : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (h𝓛' : Scheme.Modules.IsInvertible 𝓛')
    (e : 𝓛 ≅ 𝓛') (h : KernelTrivial f L 𝓛) : KernelTrivial f L 𝓛' := by
  obtain ⟨eΛ⟩ := nonempty_mumfordBundle_iso_of_iso f L 𝓛 𝓛' h𝓛 h𝓛' e
  intro R _ t x hx
  apply h R t x
  exact (LocIsoOnBase.equivalence _).trans (locIsoOnBase_of_iso' _ ((Scheme.Modules.pullback (sliceAt f x)).mapIso eΛ)) hx

theorem rosatiCompatible_of_iso {k : Type} [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f)
    {I : Type} (act : I → (A ⟶ A)) (act_over : ∀ x : I, act x ≫ f = f) (star : I → I)
    (𝓛 𝓛' : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (h𝓛' : Scheme.Modules.IsInvertible 𝓛')
    (e : 𝓛 ≅ 𝓛') (h : RosatiCompatible f L 𝓛 act act_over star) : RosatiCompatible f L 𝓛' act act_over star := by
  obtain ⟨eΛ⟩ := nonempty_mumfordBundle_iso_of_iso f L 𝓛 𝓛' h𝓛 h𝓛' e
  intro b
  have E := LocIsoOnBase.equivalence (pullback.fst f f ≫ f)
  exact E.trans (E.trans (locIsoOnBase_of_iso' _ ((Scheme.Modules.pullback _).mapIso eΛ.symm)) (h b))
    (locIsoOnBase_of_iso' _ ((Scheme.Modules.pullback _).mapIso eΛ))

end L4Stubs
open L4Stubs

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (N : ℕ) (K : Type) [Field K] (Kbar : Type) [Field Kbar] [Algebra K Kbar] [IsAlgClosure K Kbar]
    (E_K : FakeEllipticCurve Λ N K) (E_Kbar : FakeEllipticCurve Λ N Kbar)
    (hbar : FakeEllipticCurve.IsPullback (algebraMap K Kbar) E_K E_Kbar)
    (𝓛bar : E_Kbar.A.Modules) (h𝓛bar : (Scheme.Modules.IsInvertible 𝓛bar ∧ KernelTrivial E_Kbar.f E_Kbar.L 𝓛bar ∧
      (∀ (k' : Type) [Field k'] [IsAlgClosed k'] (sk : Kbar →+* k'), 0 < Scheme.Modules.geomFibreH0Finrank E_Kbar.f 𝓛bar k' sk) ∧
      RosatiCompatible E_Kbar.f E_Kbar.L 𝓛bar E_Kbar.act E_Kbar.act_over star)) :
    ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K')
      (E' : FakeEllipticCurve Λ N K') (_ : FakeEllipticCurve.IsPullback (algebraMap K K') E_K E')
      (𝓛' : E'.A.Modules), (Scheme.Modules.IsInvertible 𝓛' ∧ KernelTrivial E'.f E'.L 𝓛' ∧
      (∀ (k' : Type) [Field k'] [IsAlgClosed k'] (sk : K' →+* k'), 0 < Scheme.Modules.geomFibreH0Finrank E'.f 𝓛' k' sk) ∧
      RosatiCompatible E'.f E'.L 𝓛' E'.act E'.act_over star) := by
  classical
  obtain ⟨g, hg, hmul, hact, hlev⟩ := hbar
  obtain ⟨hinv, hKT, hpos, hR⟩ := h𝓛bar
  haveI : Algebra.IsAlgebraic K Kbar := IsAlgClosure.isAlgebraic
  haveI : IsProper E_K.f := E_K.bundle.proper

  let c : E_Kbar.A ≅ Limits.pullback E_K.f (Spec.map (CommRingCat.ofHom (algebraMap K Kbar))) := hg.isoPullback
  have hc1 : c.hom ≫ Limits.pullback.fst _ _ = g := hg.isoPullback_hom_fst
  have hc2 : c.hom ≫ Limits.pullback.snd _ _ = E_Kbar.f := hg.isoPullback_hom_snd

  obtain ⟨F, hF, 𝓛F, h𝓛F, hcomp⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_intermediateField_isInvertible_nonempty_pullback_iso_of_isAlgebraic
      K Kbar E_K.f ((Scheme.Modules.pullback c.inv).obj 𝓛bar) (Scheme.Modules.IsInvertible.pullback c.inv hinv)
  haveI := hF

  obtain ⟨E', g', hg', hmul', hact', hlev', hlev''⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_levelIff (algebraMap K (↥F)) E_K
  have hE' : FakeEllipticCurve.IsPullback (algebraMap K (↥F)) E_K E' := ⟨g', hg', hmul', hact', hlev'⟩
  let c' : E'.A ≅ Limits.pullback E_K.f (Spec.map (CommRingCat.ofHom (algebraMap K (↥F)))) := hg'.isoPullback
  have hc'1 : c'.hom ≫ Limits.pullback.fst _ _ = g' := hg'.isoPullback_hom_fst
  have hc'2 : c'.hom ≫ Limits.pullback.snd _ _ = E'.f := hg'.isoPullback_hom_snd

  have hcompalg : (algebraMap (↥F) Kbar).comp (algebraMap K (↥F)) = algebraMap K Kbar :=
    (IsScalarTower.algebraMap_eq K (↥F) Kbar).symm
  obtain ⟨g'', hg''g, hg''f, -, hvia⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia.exists_comp_eq_and_isPullbackVia_of_comp_eq
      (algebraMap K (↥F)) (algebraMap (↥F) Kbar) (algebraMap K Kbar) hcompalg E_K E' E_Kbar g' ⟨hg', hmul', hact', hlev'⟩ hlev''
      g ⟨hg, hmul, hact, hlev⟩
  obtain ⟨hg'', hmul'', hact'', -⟩ := hvia

  let cX : Limits.pullback E_K.f (Spec.map (CommRingCat.ofHom (algebraMap K Kbar))) ⟶
      Limits.pullback E_K.f (Spec.map (CommRingCat.ofHom (algebraMap K (↥F)))) := c.inv ≫ g'' ≫ c'.hom
  have hcX1 : cX ≫ Limits.pullback.fst _ _ = Limits.pullback.fst _ _ := by
    simp only [cX, Category.assoc, hc'1, hg''g]; rw [← hc1, Iso.inv_hom_id_assoc]
  have hcX2 : cX ≫ Limits.pullback.snd _ _ =
      Limits.pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (algebraMap (↥F) Kbar)) := by
    simp only [cX, Category.assoc, hc'2, hg''f]; rw [← Category.assoc, ← hc2, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  obtain ⟨eX⟩ := hcomp cX hcX1 hcX2

  let 𝓛' : E'.A.Modules := (Scheme.Modules.pullback c'.hom).obj 𝓛F
  have h𝓛' : Scheme.Modules.IsInvertible 𝓛' := Scheme.Modules.IsInvertible.pullback c'.hom h𝓛F
  have e'' : (Scheme.Modules.pullback g'').obj 𝓛' ≅ 𝓛bar :=
    (Scheme.Modules.pullbackComp g'' c'.hom).app 𝓛F ≪≫
      (Scheme.Modules.pullbackCongr (show g'' ≫ c'.hom = c.hom ≫ cX by
        simp only [cX, Iso.hom_inv_id_assoc])).app 𝓛F ≪≫
      ((Scheme.Modules.pullbackComp c.hom cX).app 𝓛F).symm ≪≫
      (Scheme.Modules.pullback c.hom).mapIso eX ≪≫
      (Scheme.Modules.pullbackComp c.hom c.inv).app 𝓛bar ≪≫
      (Scheme.Modules.pullbackCongr c.hom_inv_id).app 𝓛bar ≪≫
      (Scheme.Modules.pullbackId _).app 𝓛bar
  refine ⟨↥F, inferInstance, inferInstance, hF, E', hE', 𝓛', h𝓛', ?_, ?_, ?_⟩
  ·
    exact AlgebraicGeometry.Polarisation.kernelTrivial_of_kernelTrivial_pullback_of_isPullback_of_field
      (↥F) Kbar E'.f E'.L E_Kbar.f E_Kbar.L g'' hg'' hmul'' 𝓛' h𝓛' (kernelTrivial_of_iso _ _ _ _ hinv (Scheme.Modules.IsInvertible.pullback g'' h𝓛') e''.symm hKT)
  ·
    intro k _ _ sk
    letI : Algebra (↥F) k := sk.toAlgebra
    haveI : Module.IsTorsionFree (↥F) k := by infer_instance
    haveI : Algebra.IsAlgebraic (↥F) Kbar := Algebra.IsAlgebraic.tower_top (K := K) (↥F)
    let j : Kbar →ₐ[↥F] k := IsAlgClosed.lift
    have hj : (j : Kbar →+* k).comp (algebraMap (↥F) Kbar) = sk := by
      ext x; simp [RingHom.algebraMap_toAlgebra]
    have := AlgebraicGeometry.Scheme.Modules.geomFibreH0Finrank_eq_of_isPullback (algebraMap (↥F) Kbar)
      E'.f E_Kbar.f g'' hg'' 𝓛' 𝓛bar e'' k (j : Kbar →+* k)
    rw [hj] at this
    rw [← this]
    exact hpos k (j : Kbar →+* k)
  ·
    exact AlgebraicGeometry.Polarisation.rosatiCompatible_of_rosatiCompatible_pullback_of_isPullback_of_field
      (↥F) Kbar E'.f E'.L E'.bundle E_Kbar.f E_Kbar.L g'' hg'' hmul'' E'.act E'.act_over E_Kbar.act E_Kbar.act_over hact'' star
      𝓛' h𝓛' (rosatiCompatible_of_iso _ _ _ _ _ _ _ hinv (Scheme.Modules.IsInvertible.pullback g'' h𝓛') e''.symm hR)

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_finiteDimensional_isPullback_kernelTrivial_rosatiCompatible_of_isAlgClosure
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_finiteDimensional_isPullback_kernelTrivial_rosatiCompatible_of_isAlgClosure (solution)
