-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_isNoetherianRing_injective_isLocalHom_isPullback_isCanonicalPol_nonempty_pullback_iso_of_locIsoOnBase_sqrt_of_isLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/5be4f44f-b3fc-590b-bb58-894be9217474

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_isPullback_kernelIsTwoTorsion_kernelTrivial_nonempty_pullback_iso
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isLocalRing_injective_isLocalHom_isPullback_comp_eq_of_injective
import Theorems.Thm_AlgebraicGeometry_Polarisation_KernelIsTwoTorsion_pullback_of_isPullback_of_isInvertible
import Theorems.Thm_AlgebraicGeometry_Polarisation_KernelTrivial_pullback_of_isPullback
import Theorems.Thm_CerednikDrinfeld_QM_IsCanonicalPolData_of_locIsoOnBase
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isCanonicalPol_of_isCanonicalPol_pullback_of_injective_of_isLocalHom
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isNoetherianRing_injective_isLocalHom_isPullback_isCanonicalPol_nonempty_pullback_iso_of_locIsoOnBase_sqrt_of_isLocalRing
p2m_attr_erase "instance" "IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid MvFormalGroup.instIsCommAddMv AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModulePreGlue AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies SheafOfModules.isIso_ihomModelToIhom PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ"
p2m_attr_erase "instance" "PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of"
p2m_attr_erase "simp" "IsDirectLimit.Equiv_apply AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg"
p2m_attr_erase "simp" "MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg' MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast MvFormalGroup.mk.injEq MvFormalGroup.nthSeries_zero MvFormalGroup.Hom.mk.sizeOf_spec MvFormalGroup.Hom.mk.injEq MvFormalGroup.mk.sizeOf_spec AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.glueComponent_glueMk AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.injEq AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.sizeOf_spec AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply"
p2m_attr_erase "simp" "SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app GoodReductionJacobian.RelativeGroupLaw.sndPoint_coe GoodReductionJacobian.RelativeGroupLaw.fstPoint_coe AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app GoodReductionJacobian.prodInr_comp_prodFst GoodReductionJacobian.RelativeGroupLaw.prod_inv GoodReductionJacobian.prodInl_comp_prodSnd GoodReductionJacobian.prodInr_comp_prodSnd GoodReductionJacobian.prodInl_comp_prodFst GoodReductionJacobian.prodFstPt_prodPairPt GoodReductionJacobian.prodFst_coe GoodReductionJacobian.prodSndPt_prodPairPt GoodReductionJacobian.RelativeGroupLaw.prod_one GoodReductionJacobian.prodPairPt_coe GoodReductionJacobian.prodPairPt_prodFstPt_prodSndPt GoodReductionJacobian.prodFstPt_coe GoodReductionJacobian.RelativeGroupLaw.prod_mul GoodReductionJacobian.prodSndPt_coe GoodReductionJacobian.prodSnd_coe AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec"
set_option autoImplicit false

open scoped TensorProduct Quaternion
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

namespace T3RedD1

theorem locIsoOnBase_of_iso {R : Type} [CommRing R] {X : Scheme.{0}} (g : X ⟶ Spec (CommRingCat.of R))
    {M M' : X.Modules} (e : M ≅ M') : LocIsoOnBase g M M' :=
  fun _ => ⟨⊤, trivial, ⟨(Scheme.Modules.pullback (g ⁻¹ᵁ ⊤).ι).mapIso e⟩⟩

end T3RedD1

open T3RedD1 in
theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (N : ℕ) (R : Type) [CommRing R] [IsLocalRing R] (E : FakeEllipticCurve Λ N R)
    (𝓜 𝓜' : E.A.Modules) (h : E.IsCanonicalPol star 𝓜) (h' : E.IsCanonicalPol star 𝓜')
    (𝓜₀ 𝓜₀' : E.A.Modules) (h₀ : Scheme.Modules.IsInvertible 𝓜₀) (h₀' : Scheme.Modules.IsInvertible 𝓜₀')
    (hK₀ : KernelTrivial E.f E.L 𝓜₀) (hK₀' : KernelTrivial E.f E.L 𝓜₀')
    (hsq : LocIsoOnBase E.f 𝓜 (𝓜₀ ⊗ (Scheme.Modules.pullback (negMor E.f E.L)).obj 𝓜₀))
    (hsq' : LocIsoOnBase E.f 𝓜' (𝓜₀' ⊗ (Scheme.Modules.pullback (negMor E.f E.L)).obj 𝓜₀')) :
    ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsLocalRing R₁) (_ : IsNoetherianRing R₁) (φ : R₁ →+* R)
      (E₁ : FakeEllipticCurve Λ N R₁) (g : E.A ⟶ E₁.A),
      CategoryTheory.IsPullback g E.f E₁.f (Spec.map (CommRingCat.ofHom φ)) ∧ Function.Injective φ ∧ IsLocalHom φ ∧
      ∃ (𝓜₁ 𝓜₁' : E₁.A.Modules), E₁.IsCanonicalPol star 𝓜₁ ∧ E₁.IsCanonicalPol star 𝓜₁' ∧
        Nonempty ((Scheme.Modules.pullback g).obj 𝓜₁ ≅ 𝓜) ∧ Nonempty ((Scheme.Modules.pullback g).obj 𝓜₁' ≅ 𝓜') := by
  classical

  obtain ⟨T, hTfg, ET, g, hg, hlaw, hact, 𝓜T, 𝓜T', 𝓜₀T, 𝓜₀T', iT, iT', i0T, i0T', kT, kT', k0T, k0T',
      ⟨e⟩, ⟨e'⟩, ⟨e₀⟩, ⟨e₀'⟩⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_fg_subalgebra_isPullback_kernelIsTwoTorsion_kernelTrivial_nonempty_pullback_iso
      Λ hΛ N R E 𝓜 𝓜' 𝓜₀ 𝓜₀' h.1 h'.1 h₀ h₀' h.2.2.1 h'.2.2.1 hK₀ hK₀'
  haveI : Algebra.FiniteType ℤ ↥T := (Subalgebra.fg_iff_finiteType T).mp hTfg
  haveI : IsNoetherianRing ↥T := Algebra.FiniteType.isNoetherianRing ℤ ↥T

  obtain ⟨T₁, _, _, _, ψ, φ₁, hcomp, hφ₁, hφ₁l, E₁, g₁, hg₁, hmap, hh, hfac, hlaw₁, hact₁, hlawh⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_isLocalRing_injective_isLocalHom_isPullback_comp_eq_of_injective
      Λ hΛ N (T.val.toRingHom) (fun x y hxy => Subtype.ext hxy) ET E g hg hlaw hact

  have key : ∀ (𝓝 𝓝₀ : E.A.Modules) (𝓝T 𝓝₀T : ET.A.Modules), E.IsCanonicalPol star 𝓝 →
      Scheme.Modules.IsInvertible 𝓝T → Scheme.Modules.IsInvertible 𝓝₀T →
      KernelIsTwoTorsion ET.f ET.L 𝓝T → KernelTrivial ET.f ET.L 𝓝₀T →
      ((Scheme.Modules.pullback g).obj 𝓝T ≅ 𝓝) → ((Scheme.Modules.pullback g).obj 𝓝₀T ≅ 𝓝₀) →
      LocIsoOnBase E.f 𝓝 (𝓝₀ ⊗ (Scheme.Modules.pullback (negMor E.f E.L)).obj 𝓝₀) →
      E₁.IsCanonicalPol star ((Scheme.Modules.pullback hmap).obj 𝓝T) ∧
        Nonempty ((Scheme.Modules.pullback g₁).obj ((Scheme.Modules.pullback hmap).obj 𝓝T) ≅ 𝓝) := by
    intro 𝓝 𝓝₀ 𝓝T 𝓝₀T hcan hiT hi0T hkT hk0T eN eN₀ hsqN

    let cmp : ∀ X : ET.A.Modules,
        (Scheme.Modules.pullback g₁).obj ((Scheme.Modules.pullback hmap).obj X) ≅ (Scheme.Modules.pullback g).obj X :=
      fun X => (Scheme.Modules.pullbackComp g₁ hmap).app X ≪≫ (Scheme.Modules.pullbackCongr hfac).app X
    let eM : (Scheme.Modules.pullback g₁).obj ((Scheme.Modules.pullback hmap).obj 𝓝T) ≅ 𝓝 := cmp 𝓝T ≪≫ eN
    let eM₀ : (Scheme.Modules.pullback g₁).obj ((Scheme.Modules.pullback hmap).obj 𝓝₀T) ≅ 𝓝₀ := cmp 𝓝₀T ≪≫ eN₀

    have hK₁ : KernelIsTwoTorsion E₁.f E₁.L ((Scheme.Modules.pullback hmap).obj 𝓝T) :=
      AlgebraicGeometry.Polarisation.KernelIsTwoTorsion.pullback_of_isPullback_of_isInvertible ψ hh ET.L E₁.L hlawh 𝓝T hiT hkT
    have hK₀₁ : KernelTrivial E₁.f E₁.L ((Scheme.Modules.pullback hmap).obj 𝓝₀T) :=
      AlgebraicGeometry.Polarisation.KernelTrivial.pullback_of_isPullback ψ hh ET.L E₁.L hlawh 𝓝₀T hi0T hk0T

    have E0 := AlgebraicGeometry.Polarisation.LocIsoOnBase.equivalence E.f
    have hcan₁ : E.IsCanonicalPol star ((Scheme.Modules.pullback g₁).obj ((Scheme.Modules.pullback hmap).obj 𝓝T)) :=
      CerednikDrinfeld.QM.IsCanonicalPolData.of_locIsoOnBase E.f E.L E.act E.act_over star 𝓝 _
        ((hiT.pullback hmap).pullback g₁) (locIsoOnBase_of_iso E.f eM.symm) hcan
    have hsq₁ : LocIsoOnBase E.f ((Scheme.Modules.pullback g₁).obj ((Scheme.Modules.pullback hmap).obj 𝓝T))
        ((Scheme.Modules.pullback g₁).obj ((Scheme.Modules.pullback hmap).obj 𝓝₀T) ⊗
          (Scheme.Modules.pullback (negMor E.f E.L)).obj
            ((Scheme.Modules.pullback g₁).obj ((Scheme.Modules.pullback hmap).obj 𝓝₀T))) :=
      E0.trans (locIsoOnBase_of_iso E.f eM)
        (E0.trans hsqN (locIsoOnBase_of_iso E.f
          (eM₀.symm ⊗ᵢ (Scheme.Modules.pullback (negMor E.f E.L)).mapIso eM₀.symm)))
    refine ⟨?_, ⟨eM⟩⟩
    exact CerednikDrinfeld.QM.FakeEllipticCurve.isCanonicalPol_of_isCanonicalPol_pullback_of_injective_of_isLocalHom
      Λ hΛ star N φ₁ hφ₁ hφ₁l E₁ E g₁ hg₁ hlaw₁ hact₁ _ _ (hiT.pullback hmap) (hi0T.pullback hmap) hK₁ hK₀₁ hcan₁ hsq₁
  obtain ⟨hc₁, hiso₁⟩ := key 𝓜 𝓜₀ 𝓜T 𝓜₀T h iT i0T kT k0T e e₀ hsq
  obtain ⟨hc₁', hiso₁'⟩ := key 𝓜' 𝓜₀' 𝓜T' 𝓜₀T' h' iT' i0T' kT' k0T' e' e₀' hsq'
  exact ⟨T₁, inferInstance, inferInstance, inferInstance, φ₁, E₁, g₁, hg₁, hφ₁, hφ₁l, _, _, hc₁, hc₁', hiso₁, hiso₁'⟩

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isNoetherianRing_injective_isLocalHom_isPullback_isCanonicalPol_nonempty_pullback_iso_of_locIsoOnBase_sqrt_of_isLocalRing
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isNoetherianRing_injective_isLocalHom_isPullback_isCanonicalPol_nonempty_pullback_iso_of_locIsoOnBase_sqrt_of_isLocalRing (solution)
