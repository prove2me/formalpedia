-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_fg_subalgebra_isPullback_kernelIsTwoTorsion_kernelTrivial_nonempty_pullback_iso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/bb8860ec-fbe8-5ec0-951f-77f35d6df6f0

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_isPullback_hom
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_extension_isInvertible_nonempty_pullback_iso
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_extension_kernelIsTwoTorsion_pullback
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_extension_kernelTrivial_pullback
import Theorems.Thm_AlgebraicGeometry_Polarisation_KernelIsTwoTorsion_pullback_of_isPullback_of_isInvertible
import Theorems.Thm_AlgebraicGeometry_Polarisation_KernelTrivial_pullback_of_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_isPullback_kernelIsTwoTorsion_kernelTrivial_nonempty_pullback_iso
p2m_attr_erase "instance" "IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid MvFormalGroup.instIsCommAddMv AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModulePreGlue AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies SheafOfModules.isIso_ihomModelToIhom PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ"
p2m_attr_erase "instance" "PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of"
p2m_attr_erase "simp" "IsDirectLimit.Equiv_apply AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg"
p2m_attr_erase "simp" "MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg' MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast MvFormalGroup.mk.injEq MvFormalGroup.nthSeries_zero MvFormalGroup.Hom.mk.sizeOf_spec MvFormalGroup.Hom.mk.injEq MvFormalGroup.mk.sizeOf_spec AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.glueComponent_glueMk AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.injEq AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.sizeOf_spec AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply"
p2m_attr_erase "simp" "SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app GoodReductionJacobian.RelativeGroupLaw.sndPoint_coe GoodReductionJacobian.RelativeGroupLaw.fstPoint_coe AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app"

set_option autoImplicit false

open scoped TensorProduct Quaternion
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

namespace T3RedDM

noncomputable def dualIso {X : Scheme.{0}} {M M' : X.Modules} (e : M ≅ M') :
    Scheme.Modules.dual M ≅ Scheme.Modules.dual M' :=
  ((MonoidalClosed.internalHom.mapIso e.op).app (𝟙_ X.Modules)).symm

noncomputable def mumfordBundleIso {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S))
    (L : RelativeGroupLaw S f) {M M' : A.Modules} (e : M ≅ M') :
    mumfordBundle f L M ≅ mumfordBundle f L M' :=
  (Scheme.Modules.pullback (addMor f L)).mapIso e ⊗ᵢ
    ((Scheme.Modules.pullback (pullback.fst f f)).mapIso (dualIso e) ⊗ᵢ
      (Scheme.Modules.pullback (pullback.snd f f)).mapIso (dualIso e))

theorem locIsoOnBase_of_iso_left {S' : Type} [CommRing S'] {X : Scheme.{0}} (g : X ⟶ Spec (CommRingCat.of S'))
    {N N' P : X.Modules} (e : N ≅ N') (h : LocIsoOnBase g N' P) : LocIsoOnBase g N P := by
  intro s
  obtain ⟨U, hs, ⟨φ⟩⟩ := h s
  exact ⟨U, hs, ⟨(Scheme.Modules.pullback _).mapIso e ≪≫ φ⟩⟩

theorem kernelTrivial_of_iso {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    {M M' : A.Modules} (e : M ≅ M') (h : KernelTrivial f L M) : KernelTrivial f L M' := by
  intro R _ t x hx
  exact h R t x (locIsoOnBase_of_iso_left _ ((Scheme.Modules.pullback (sliceAt f x)).mapIso (mumfordBundleIso f L e)) hx)

theorem kernelIsTwoTorsion_of_iso {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S))
    (L : RelativeGroupLaw S f) {M M' : A.Modules} (e : M ≅ M') (h : KernelIsTwoTorsion f L M) :
    KernelIsTwoTorsion f L M' := by
  intro R _ t x
  rw [← h R t x]
  constructor
  · exact locIsoOnBase_of_iso_left _ ((Scheme.Modules.pullback (sliceAt f x)).mapIso (mumfordBundleIso f L e))
  · exact locIsoOnBase_of_iso_left _ ((Scheme.Modules.pullback (sliceAt f x)).mapIso (mumfordBundleIso f L e.symm))

noncomputable def isoUp {EA E₀A ETA : Scheme.{0}} (g₀ : EA ⟶ E₀A) (g : EA ⟶ ETA) (h : ETA ⟶ E₀A) (hfac : g ≫ h = g₀)
    {X : E₀A.Modules} {Y : EA.Modules} (e : (Scheme.Modules.pullback g₀).obj X ≅ Y) :
    (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback h).obj X) ≅ Y :=
  (Scheme.Modules.pullbackComp g h).app X ≪≫ (Scheme.Modules.pullbackCongr hfac).app X ≪≫ e

end T3RedDM

open T3RedDM in
theorem solution
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (N : ℕ) (R : Type) [CommRing R] (E : FakeEllipticCurve Λ N R)
    (𝓜 𝓜' 𝓜₀ 𝓜₀' : E.A.Modules)
    (h : Scheme.Modules.IsInvertible 𝓜) (h' : Scheme.Modules.IsInvertible 𝓜')
    (h₀ : Scheme.Modules.IsInvertible 𝓜₀) (h₀' : Scheme.Modules.IsInvertible 𝓜₀')
    (hK : KernelIsTwoTorsion E.f E.L 𝓜) (hK' : KernelIsTwoTorsion E.f E.L 𝓜')
    (hK₀ : KernelTrivial E.f E.L 𝓜₀) (hK₀' : KernelTrivial E.f E.L 𝓜₀') :
    ∃ (T : Subalgebra ℤ R) (_ : T.FG) (ET : FakeEllipticCurve Λ N ↥T) (g : E.A ⟶ ET.A)
      (hg : CategoryTheory.IsPullback g E.f ET.f (Spec.map (CommRingCat.ofHom T.val.toRingHom))),
      (∀ {X : Scheme.{0}} (t' : X ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t' E.f),
        (E.L.mul t' P Q).1 ≫ g =
          (ET.L.mul (t' ≫ Spec.map (CommRingCat.ofHom T.val.toRingHom))
            ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1) ∧
      (∀ x : ↥Λ, E.act x ≫ g = g ≫ ET.act x) ∧
      ∃ (𝓜T 𝓜T' 𝓜₀T 𝓜₀T' : ET.A.Modules),
        Scheme.Modules.IsInvertible 𝓜T ∧ Scheme.Modules.IsInvertible 𝓜T' ∧
        Scheme.Modules.IsInvertible 𝓜₀T ∧ Scheme.Modules.IsInvertible 𝓜₀T' ∧
        KernelIsTwoTorsion ET.f ET.L 𝓜T ∧ KernelIsTwoTorsion ET.f ET.L 𝓜T' ∧
        KernelTrivial ET.f ET.L 𝓜₀T ∧ KernelTrivial ET.f ET.L 𝓜₀T' ∧
        Nonempty ((Scheme.Modules.pullback g).obj 𝓜T ≅ 𝓜) ∧ Nonempty ((Scheme.Modules.pullback g).obj 𝓜T' ≅ 𝓜') ∧
        Nonempty ((Scheme.Modules.pullback g).obj 𝓜₀T ≅ 𝓜₀) ∧ Nonempty ((Scheme.Modules.pullback g).obj 𝓜₀T' ≅ 𝓜₀') := by
  classical

  obtain ⟨T0, hT0, E0, g0, hg0, hlaw0, hact0⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.exists_fg_subalgebra_isPullback_hom Λ hΛ N R E

  obtain ⟨T1, hT1, hle1, E1, g1, hg1, h1, hh1, hfac1, hlaw1, hact1, hlawh1, hacth1, 𝓜1, i𝓜1, ⟨e𝓜1⟩⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_fg_subalgebra_extension_isInvertible_nonempty_pullback_iso Λ hΛ N R E T0 hT0 E0 g0 hg0 hlaw0 hact0 𝓜 h

  obtain ⟨T2, hT2, hle2, E2, g2, hg2, h2, hh2, hfac2, hlaw2, hact2, hlawh2, hacth2, k𝓜2⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_fg_subalgebra_extension_kernelIsTwoTorsion_pullback Λ hΛ N R E T1 hT1 E1 g1 hg1 hlaw1 hact1 𝓜1 i𝓜1 (kernelIsTwoTorsion_of_iso E.f E.L e𝓜1.symm hK)
  let 𝓜2 := (Scheme.Modules.pullback h2).obj 𝓜1
  have i𝓜2 : Scheme.Modules.IsInvertible 𝓜2 := i𝓜1.pullback h2
  have e𝓜2 : (Scheme.Modules.pullback g2).obj 𝓜2 ≅ 𝓜 := isoUp g1 g2 h2 hfac2 e𝓜1

  obtain ⟨T3, hT3, hle3, E3, g3, hg3, h3, hh3, hfac3, hlaw3, hact3, hlawh3, hacth3, 𝓝3, i𝓝3, ⟨e𝓝3⟩⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_fg_subalgebra_extension_isInvertible_nonempty_pullback_iso Λ hΛ N R E T2 hT2 E2 g2 hg2 hlaw2 hact2 𝓜' h'
  let 𝓜3 := (Scheme.Modules.pullback h3).obj 𝓜2
  have i𝓜3 : Scheme.Modules.IsInvertible 𝓜3 := i𝓜2.pullback h3
  have e𝓜3 : (Scheme.Modules.pullback g3).obj 𝓜3 ≅ 𝓜 := isoUp g2 g3 h3 hfac3 e𝓜2
  have k𝓜3 : KernelIsTwoTorsion E3.f E3.L 𝓜3 :=
    AlgebraicGeometry.Polarisation.KernelIsTwoTorsion.pullback_of_isPullback_of_isInvertible _ hh3 E2.L E3.L hlawh3 𝓜2 i𝓜2 k𝓜2

  obtain ⟨T4, hT4, hle4, E4, g4, hg4, h4, hh4, hfac4, hlaw4, hact4, hlawh4, hacth4, k𝓝4⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_fg_subalgebra_extension_kernelIsTwoTorsion_pullback Λ hΛ N R E T3 hT3 E3 g3 hg3 hlaw3 hact3 𝓝3 i𝓝3 (kernelIsTwoTorsion_of_iso E.f E.L e𝓝3.symm hK')
  let 𝓝4 := (Scheme.Modules.pullback h4).obj 𝓝3
  have i𝓝4 : Scheme.Modules.IsInvertible 𝓝4 := i𝓝3.pullback h4
  have e𝓝4 : (Scheme.Modules.pullback g4).obj 𝓝4 ≅ 𝓜' := isoUp g3 g4 h4 hfac4 e𝓝3
  let 𝓜4 := (Scheme.Modules.pullback h4).obj 𝓜3
  have i𝓜4 : Scheme.Modules.IsInvertible 𝓜4 := i𝓜3.pullback h4
  have e𝓜4 : (Scheme.Modules.pullback g4).obj 𝓜4 ≅ 𝓜 := isoUp g3 g4 h4 hfac4 e𝓜3
  have k𝓜4 : KernelIsTwoTorsion E4.f E4.L 𝓜4 :=
    AlgebraicGeometry.Polarisation.KernelIsTwoTorsion.pullback_of_isPullback_of_isInvertible _ hh4 E3.L E4.L hlawh4 𝓜3 i𝓜3 k𝓜3

  obtain ⟨T5, hT5, hle5, E5, g5, hg5, h5, hh5, hfac5, hlaw5, hact5, hlawh5, hacth5, 𝓟5, i𝓟5, ⟨e𝓟5⟩⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_fg_subalgebra_extension_isInvertible_nonempty_pullback_iso Λ hΛ N R E T4 hT4 E4 g4 hg4 hlaw4 hact4 𝓜₀ h₀
  let 𝓜5 := (Scheme.Modules.pullback h5).obj 𝓜4
  have i𝓜5 : Scheme.Modules.IsInvertible 𝓜5 := i𝓜4.pullback h5
  have e𝓜5 : (Scheme.Modules.pullback g5).obj 𝓜5 ≅ 𝓜 := isoUp g4 g5 h5 hfac5 e𝓜4
  have k𝓜5 : KernelIsTwoTorsion E5.f E5.L 𝓜5 :=
    AlgebraicGeometry.Polarisation.KernelIsTwoTorsion.pullback_of_isPullback_of_isInvertible _ hh5 E4.L E5.L hlawh5 𝓜4 i𝓜4 k𝓜4
  let 𝓝5 := (Scheme.Modules.pullback h5).obj 𝓝4
  have i𝓝5 : Scheme.Modules.IsInvertible 𝓝5 := i𝓝4.pullback h5
  have e𝓝5 : (Scheme.Modules.pullback g5).obj 𝓝5 ≅ 𝓜' := isoUp g4 g5 h5 hfac5 e𝓝4
  have k𝓝5 : KernelIsTwoTorsion E5.f E5.L 𝓝5 :=
    AlgebraicGeometry.Polarisation.KernelIsTwoTorsion.pullback_of_isPullback_of_isInvertible _ hh5 E4.L E5.L hlawh5 𝓝4 i𝓝4 k𝓝4

  obtain ⟨T6, hT6, hle6, E6, g6, hg6, h6, hh6, hfac6, hlaw6, hact6, hlawh6, hacth6, k𝓟6⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_fg_subalgebra_extension_kernelTrivial_pullback Λ hΛ N R E T5 hT5 E5 g5 hg5 hlaw5 hact5 𝓟5 i𝓟5 (kernelTrivial_of_iso E.f E.L e𝓟5.symm hK₀)
  let 𝓟6 := (Scheme.Modules.pullback h6).obj 𝓟5
  have i𝓟6 : Scheme.Modules.IsInvertible 𝓟6 := i𝓟5.pullback h6
  have e𝓟6 : (Scheme.Modules.pullback g6).obj 𝓟6 ≅ 𝓜₀ := isoUp g5 g6 h6 hfac6 e𝓟5
  let 𝓜6 := (Scheme.Modules.pullback h6).obj 𝓜5
  have i𝓜6 : Scheme.Modules.IsInvertible 𝓜6 := i𝓜5.pullback h6
  have e𝓜6 : (Scheme.Modules.pullback g6).obj 𝓜6 ≅ 𝓜 := isoUp g5 g6 h6 hfac6 e𝓜5
  have k𝓜6 : KernelIsTwoTorsion E6.f E6.L 𝓜6 :=
    AlgebraicGeometry.Polarisation.KernelIsTwoTorsion.pullback_of_isPullback_of_isInvertible _ hh6 E5.L E6.L hlawh6 𝓜5 i𝓜5 k𝓜5
  let 𝓝6 := (Scheme.Modules.pullback h6).obj 𝓝5
  have i𝓝6 : Scheme.Modules.IsInvertible 𝓝6 := i𝓝5.pullback h6
  have e𝓝6 : (Scheme.Modules.pullback g6).obj 𝓝6 ≅ 𝓜' := isoUp g5 g6 h6 hfac6 e𝓝5
  have k𝓝6 : KernelIsTwoTorsion E6.f E6.L 𝓝6 :=
    AlgebraicGeometry.Polarisation.KernelIsTwoTorsion.pullback_of_isPullback_of_isInvertible _ hh6 E5.L E6.L hlawh6 𝓝5 i𝓝5 k𝓝5

  obtain ⟨T7, hT7, hle7, E7, g7, hg7, h7, hh7, hfac7, hlaw7, hact7, hlawh7, hacth7, 𝓠7, i𝓠7, ⟨e𝓠7⟩⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_fg_subalgebra_extension_isInvertible_nonempty_pullback_iso Λ hΛ N R E T6 hT6 E6 g6 hg6 hlaw6 hact6 𝓜₀' h₀'
  let 𝓜7 := (Scheme.Modules.pullback h7).obj 𝓜6
  have i𝓜7 : Scheme.Modules.IsInvertible 𝓜7 := i𝓜6.pullback h7
  have e𝓜7 : (Scheme.Modules.pullback g7).obj 𝓜7 ≅ 𝓜 := isoUp g6 g7 h7 hfac7 e𝓜6
  have k𝓜7 : KernelIsTwoTorsion E7.f E7.L 𝓜7 :=
    AlgebraicGeometry.Polarisation.KernelIsTwoTorsion.pullback_of_isPullback_of_isInvertible _ hh7 E6.L E7.L hlawh7 𝓜6 i𝓜6 k𝓜6
  let 𝓝7 := (Scheme.Modules.pullback h7).obj 𝓝6
  have i𝓝7 : Scheme.Modules.IsInvertible 𝓝7 := i𝓝6.pullback h7
  have e𝓝7 : (Scheme.Modules.pullback g7).obj 𝓝7 ≅ 𝓜' := isoUp g6 g7 h7 hfac7 e𝓝6
  have k𝓝7 : KernelIsTwoTorsion E7.f E7.L 𝓝7 :=
    AlgebraicGeometry.Polarisation.KernelIsTwoTorsion.pullback_of_isPullback_of_isInvertible _ hh7 E6.L E7.L hlawh7 𝓝6 i𝓝6 k𝓝6
  let 𝓟7 := (Scheme.Modules.pullback h7).obj 𝓟6
  have i𝓟7 : Scheme.Modules.IsInvertible 𝓟7 := i𝓟6.pullback h7
  have e𝓟7 : (Scheme.Modules.pullback g7).obj 𝓟7 ≅ 𝓜₀ := isoUp g6 g7 h7 hfac7 e𝓟6
  have k𝓟7 : KernelTrivial E7.f E7.L 𝓟7 :=
    AlgebraicGeometry.Polarisation.KernelTrivial.pullback_of_isPullback _ hh7 E6.L E7.L hlawh7 𝓟6 i𝓟6 k𝓟6

  obtain ⟨T8, hT8, hle8, E8, g8, hg8, h8, hh8, hfac8, hlaw8, hact8, hlawh8, hacth8, k𝓠8⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_fg_subalgebra_extension_kernelTrivial_pullback Λ hΛ N R E T7 hT7 E7 g7 hg7 hlaw7 hact7 𝓠7 i𝓠7 (kernelTrivial_of_iso E.f E.L e𝓠7.symm hK₀')
  let 𝓠8 := (Scheme.Modules.pullback h8).obj 𝓠7
  have i𝓠8 : Scheme.Modules.IsInvertible 𝓠8 := i𝓠7.pullback h8
  have e𝓠8 : (Scheme.Modules.pullback g8).obj 𝓠8 ≅ 𝓜₀' := isoUp g7 g8 h8 hfac8 e𝓠7
  let 𝓜8 := (Scheme.Modules.pullback h8).obj 𝓜7
  have i𝓜8 : Scheme.Modules.IsInvertible 𝓜8 := i𝓜7.pullback h8
  have e𝓜8 : (Scheme.Modules.pullback g8).obj 𝓜8 ≅ 𝓜 := isoUp g7 g8 h8 hfac8 e𝓜7
  have k𝓜8 : KernelIsTwoTorsion E8.f E8.L 𝓜8 :=
    AlgebraicGeometry.Polarisation.KernelIsTwoTorsion.pullback_of_isPullback_of_isInvertible _ hh8 E7.L E8.L hlawh8 𝓜7 i𝓜7 k𝓜7
  let 𝓝8 := (Scheme.Modules.pullback h8).obj 𝓝7
  have i𝓝8 : Scheme.Modules.IsInvertible 𝓝8 := i𝓝7.pullback h8
  have e𝓝8 : (Scheme.Modules.pullback g8).obj 𝓝8 ≅ 𝓜' := isoUp g7 g8 h8 hfac8 e𝓝7
  have k𝓝8 : KernelIsTwoTorsion E8.f E8.L 𝓝8 :=
    AlgebraicGeometry.Polarisation.KernelIsTwoTorsion.pullback_of_isPullback_of_isInvertible _ hh8 E7.L E8.L hlawh8 𝓝7 i𝓝7 k𝓝7
  let 𝓟8 := (Scheme.Modules.pullback h8).obj 𝓟7
  have i𝓟8 : Scheme.Modules.IsInvertible 𝓟8 := i𝓟7.pullback h8
  have e𝓟8 : (Scheme.Modules.pullback g8).obj 𝓟8 ≅ 𝓜₀ := isoUp g7 g8 h8 hfac8 e𝓟7
  have k𝓟8 : KernelTrivial E8.f E8.L 𝓟8 :=
    AlgebraicGeometry.Polarisation.KernelTrivial.pullback_of_isPullback _ hh8 E7.L E8.L hlawh8 𝓟7 i𝓟7 k𝓟7
  exact ⟨T8, hT8, E8, g8, hg8, hlaw8, hact8, 𝓜8, 𝓝8, 𝓟8, 𝓠8, i𝓜8, i𝓝8, i𝓟8, i𝓠8, k𝓜8, k𝓝8, k𝓟8, k𝓠8,
    ⟨e𝓜8⟩, ⟨e𝓝8⟩, ⟨e𝓟8⟩, ⟨e𝓠8⟩⟩

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_isPullback_kernelIsTwoTorsion_kernelTrivial_nonempty_pullback_iso
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_isPullback_kernelIsTwoTorsion_kernelTrivial_nonempty_pullback_iso (solution)
