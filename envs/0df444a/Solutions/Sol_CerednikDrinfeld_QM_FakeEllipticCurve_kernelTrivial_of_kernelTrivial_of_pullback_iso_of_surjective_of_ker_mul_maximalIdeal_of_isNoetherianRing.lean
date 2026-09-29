-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.kernelTrivial_of_kernelTrivial_of_pullback_iso_of_surjective_of_ker_mul_maximalIdeal_of_isNoetherianRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/fd7d115f-f5b9-5741-9cf2-00906e959514

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_isClosedImmersion_forall_iff_locIsoOnBase_sliceAt_mumfordBundle_of_isNoetherianRing
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_pullback_of_comp_eq
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_kernelTrivial_of_kernelTrivial_of_pullback_iso_of_surjective_of_ker_mul_maximalIdeal_of_isNoetherianRing
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans"
p2m_attr_erase "instance" "AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.sndPoint_coe GoodReductionJacobian.RelativeGroupLaw.fstPoint_coe AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt"
p2m_attr_erase "simp" "AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RegularLocalRingQuotientAscent.dualNumberFst_apply GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd"
p2m_attr_erase "simp" "NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"

set_option autoImplicit false

open scoped TensorProduct Quaternion
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_kernelTrivial_of_kernelTrivial_of_pullback_iso_of_surjective_of_ker_mul_maximalIdeal_of_isNoetherianRing.CerednikDrinfeld CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_kernelTrivial_of_kernelTrivial_of_pullback_iso_of_surjective_of_ker_mul_maximalIdeal_of_isNoetherianRing.CerednikDrinfeld.QM NeronModelInfra~schemeHomOverComp~schemeHomOverComp_coe GoodReductionJacobian AlgebraicGeometry.Polarisation"

noncomputable section

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "QM.FakeEllipticCurve"
namespace QM
p2m_export "CerednikDrinfeld.QM" "FakeEllipticCurve"
namespace KerPermAux
p2m_open "CerednikDrinfeld.QM CerednikDrinfeld"

universe u

section Laws

variable {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}

theorem mul_val_congr (L : RelativeGroupLaw S f) {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of S)} (h : t = t')
    (P Q : SchemeHomOver t f) (P' Q' : SchemeHomOver t' f) (hP : P.1 = P'.1) (hQ : Q.1 = Q'.1) :
    (L.mul t P Q).1 = (L.mul t' P' Q').1 := by
  subst h
  obtain ⟨P, hP0⟩ := P; obtain ⟨Q, hQ0⟩ := Q; obtain ⟨P', hP1⟩ := P'; obtain ⟨Q', hQ1⟩ := Q'
  simp only at hP hQ
  subst hP; subst hQ
  rfl

theorem one_val_congr (L : RelativeGroupLaw S f) {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of S)} (h : t = t') :
    (L.one t).1 = (L.one t').1 := by
  subst h; rfl

theorem one_val_eq_comp (L : RelativeGroupLaw S f) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S)) :
    (L.one t').1 = t' ≫ (L.one (𝟙 (Spec (CommRingCat.of S)))).1 := by
  have h := congrArg Subtype.val (L.one_natural (𝟙 (Spec (CommRingCat.of S))) t' t' (Category.comp_id t'))
  simpa [schemeHomOverComp] using h.symm

theorem one_id_comp (L : RelativeGroupLaw S f) : (L.one (𝟙 (Spec (CommRingCat.of S)))).1 ≫ f = 𝟙 _ :=
  (L.one (𝟙 (Spec (CommRingCat.of S)))).2

theorem locIsoOnBase_of_iso {R : Type u} [CommRing R] {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of R))
    {M M' : X.Modules} (e : M ≅ M') : LocIsoOnBase g M M' :=
  fun _ => ⟨⊤, trivial, ⟨(Scheme.Modules.pullback (g ⁻¹ᵁ ⊤).ι).mapIso e⟩⟩

theorem locIsoOnBase_pullback_of_isInvertible_base {R : Type u} [CommRing R] {X : Scheme.{u}}
    (g : X ⟶ Spec (CommRingCat.of R)) {N : (Spec (CommRingCat.of R)).Modules} (hN : Scheme.Modules.IsInvertible N) :
    LocIsoOnBase g ((Scheme.Modules.pullback g).obj N) (𝟙_ _) := by
  intro s
  obtain ⟨U, hs, ⟨e⟩⟩ := hN.exists_trivialization s
  refine ⟨U, hs, ⟨?_⟩⟩
  refine (Scheme.Modules.pullbackComp (g ⁻¹ᵁ U).ι g).app N ≪≫
    (Scheme.Modules.pullbackCongr (morphismRestrict_ι g U).symm).app N ≪≫
    ((Scheme.Modules.pullbackComp (g ∣_ U) U.ι).app N).symm ≪≫
    (Scheme.Modules.pullback (g ∣_ U)).mapIso e ≪≫
    Scheme.Modules.pullbackTensorUnitObjIso (g ∣_ U) ≪≫
    (Scheme.Modules.pullbackTensorUnitObjIso (g ⁻¹ᵁ U).ι).symm

theorem sliceAt_fst {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)} (x : SchemeHomOver t f) :
    sliceAt f x ≫ pullback.fst f f = pullback.fst f t := by
  simp only [sliceAt, pullback.lift_fst]

theorem sliceAt_snd {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)} (x : SchemeHomOver t f) :
    sliceAt f x ≫ pullback.snd f f = pullback.snd f t ≫ x.1 := by
  simp only [sliceAt, pullback.lift_snd]

theorem sliceAt_one_addMor (L : RelativeGroupLaw S f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) :
    sliceAt f (L.one t) ≫ addMor f L = pullback.fst f t := by
  have nat := congrArg Subtype.val
    (L.mul_natural (pullback.fst f f ≫ f) (sliceAt f (L.one t) ≫ pullback.fst f f ≫ f) (sliceAt f (L.one t)) rfl
      ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩)
  simp only [schemeHomOverComp_coe] at nat
  rw [addMor, nat]
  have hone := congrArg Subtype.val (L.one_natural t (pullback.snd f t ≫ t) (pullback.snd f t) rfl)
  simp only [schemeHomOverComp_coe] at hone
  have key : (L.mul (pullback.snd f t ≫ t) ⟨pullback.fst f t, pullback.condition⟩ (L.one _)).1 = pullback.fst f t := by
    rw [L.mul_one]
  rw [← key]
  refine mul_val_congr L ?_ _ _ _ _ ?_ ?_
  · rw [← Category.assoc, sliceAt_fst]; exact pullback.condition
  · simp only [schemeHomOverComp_coe, sliceAt_fst]
  · simp only [schemeHomOverComp_coe, sliceAt_snd]; exact hone

theorem locIsoOnBase_sliceAt_one_mumfordBundle (L : RelativeGroupLaw S f) (𝓛 : A.Modules)
    (hinv : Scheme.Modules.IsInvertible 𝓛)
    (R : Type u) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)) :
    LocIsoOnBase (pullback.snd f t)
      ((Scheme.Modules.pullback (sliceAt f (L.one t))).obj (mumfordBundle f L 𝓛)) (𝟙_ _) := by
  set s := sliceAt f (L.one t) with hs
  set pT := pullback.fst f t
  set qT := pullback.snd f t
  have h1 : s ≫ addMor f L = pT := sliceAt_one_addMor L t
  have h2 : s ≫ pullback.fst f f = pT := sliceAt_fst _
  have h3 : s ≫ pullback.snd f f = qT ≫ (L.one t).1 := sliceAt_snd _
  obtain ⟨D⟩ := hinv.pullback_dual_monoidalV2 pT
  obtain ⟨-, ⟨triv⟩⟩ := (hinv.pullback pT).dual_monoidalV2
  let J1 : (Scheme.Modules.pullback s).obj ((Scheme.Modules.pullback (addMor f L)).obj 𝓛) ≅
      (Scheme.Modules.pullback pT).obj 𝓛 :=
    (Scheme.Modules.pullbackComp s (addMor f L)).app 𝓛 ≪≫ (Scheme.Modules.pullbackCongr h1).app 𝓛
  let J2 : (Scheme.Modules.pullback s).obj ((Scheme.Modules.pullback (pullback.fst f f)).obj (Scheme.Modules.dual 𝓛)) ≅
      Scheme.Modules.dual ((Scheme.Modules.pullback pT).obj 𝓛) :=
    (Scheme.Modules.pullbackComp s (pullback.fst f f)).app _ ≪≫ (Scheme.Modules.pullbackCongr h2).app _ ≪≫ D
  let J3 : (Scheme.Modules.pullback s).obj ((Scheme.Modules.pullback (pullback.snd f f)).obj (Scheme.Modules.dual 𝓛)) ≅
      (Scheme.Modules.pullback qT).obj ((Scheme.Modules.pullback (L.one t).1).obj (Scheme.Modules.dual 𝓛)) :=
    (Scheme.Modules.pullbackComp s (pullback.snd f f)).app _ ≪≫ (Scheme.Modules.pullbackCongr h3).app _ ≪≫
      ((Scheme.Modules.pullbackComp qT (L.one t).1).app _).symm
  let I : (Scheme.Modules.pullback s).obj (mumfordBundle f L 𝓛) ≅
      (Scheme.Modules.pullback qT).obj ((Scheme.Modules.pullback (L.one t).1).obj (Scheme.Modules.dual 𝓛)) :=
    Scheme.Modules.pullbackTensorObjIso s _ _ ≪≫
      whiskerLeftIso _ (Scheme.Modules.pullbackTensorObjIso s _ _) ≪≫
      (J1 ⊗ᵢ (J2 ⊗ᵢ J3)) ≪≫ (α_ _ _ _).symm ≪≫ whiskerRightIso triv _ ≪≫ λ_ _
  have hN : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback (L.one t).1).obj (Scheme.Modules.dual 𝓛)) :=
    (hinv.dual_monoidalV2.1).pullback _
  exact (LocIsoOnBase.equivalence _).trans (locIsoOnBase_of_iso _ I) (locIsoOnBase_pullback_of_isInvertible_base qT hN)

def inverseUnique {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
    {L M M' : C} (e : L ⊗ M ≅ 𝟙_ C) (e' : L ⊗ M' ≅ 𝟙_ C) : M ≅ M' :=
  (λ_ M).symm ≪≫ (e'.symm ⊗ᵢ Iso.refl M) ≪≫ (β_ L M' ⊗ᵢ Iso.refl M) ≪≫ α_ M' L M ≪≫
    (Iso.refl M' ⊗ᵢ e) ≪≫ ρ_ M'

theorem nonempty_dual_iso_of_iso {X : Scheme.{u}} {M M' : X.Modules} (hM : Scheme.Modules.IsInvertible M)
    (hM' : Scheme.Modules.IsInvertible M') (e : M ≅ M') :
    Nonempty (Scheme.Modules.dual M ≅ Scheme.Modules.dual M') := by
  obtain ⟨-, ⟨d⟩⟩ := hM.dual_monoidalV2
  obtain ⟨-, ⟨d'⟩⟩ := hM'.dual_monoidalV2
  exact ⟨inverseUnique d ((e ⊗ᵢ Iso.refl _) ≪≫ d')⟩

theorem nonempty_mumfordBundle_iso_of_iso (L : RelativeGroupLaw S f) {𝓛 𝓛' : A.Modules}
    (h : Scheme.Modules.IsInvertible 𝓛) (h' : Scheme.Modules.IsInvertible 𝓛') (e : 𝓛 ≅ 𝓛') :
    Nonempty (mumfordBundle f L 𝓛 ≅ mumfordBundle f L 𝓛') := by
  obtain ⟨d⟩ := nonempty_dual_iso_of_iso h h' e
  exact ⟨(Scheme.Modules.pullback _).mapIso e ⊗ᵢ
    ((Scheme.Modules.pullback _).mapIso d ⊗ᵢ (Scheme.Modules.pullback _).mapIso d)⟩

theorem kernelTrivial_of_iso (L : RelativeGroupLaw S f) {𝓛 𝓛' : A.Modules}
    (h : Scheme.Modules.IsInvertible 𝓛) (h' : Scheme.Modules.IsInvertible 𝓛') (e : 𝓛 ≅ 𝓛')
    (hker : KernelTrivial f L 𝓛) : KernelTrivial f L 𝓛' := by
  obtain ⟨m⟩ := nonempty_mumfordBundle_iso_of_iso L h h' e
  intro R _ t x H
  refine hker R t x ((LocIsoOnBase.equivalence _).trans
    (locIsoOnBase_of_iso _ ((Scheme.Modules.pullback (sliceAt f x)).mapIso m)) H)

variable {S' : Type u} [CommRing S'] {A' : Scheme.{u}} {f' : A' ⟶ Spec (CommRingCat.of S')}

def pushAlong (ψ : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (u : A' ⟶ A) (hu : u ≫ f = f' ≫ ψ)
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' f') : SchemeHomOver (t' ≫ ψ) f :=
  ⟨P.1 ≫ u, by rw [Category.assoc, hu, ← Category.assoc, P.2]⟩

@[scoped simp] theorem pushAlong_val (ψ : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (u : A' ⟶ A)
    (hu : u ≫ f = f' ≫ ψ) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' f') :
    (pushAlong ψ u hu t' P).1 = P.1 ≫ u := rfl

section Hom

variable (L : RelativeGroupLaw S f) (L' : RelativeGroupLaw S' f')
  (ψ : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (u : A' ⟶ A) (hu : u ≫ f = f' ≫ ψ)
  (hom : ∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' f'),
    (L'.mul t' P Q).1 ≫ u =
      (L.mul (t' ≫ ψ)
        ⟨P.1 ≫ u, by rw [Category.assoc, hu, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ u, by rw [Category.assoc, hu, ← Category.assoc, Q.2]⟩).1)

def pushHom {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) :
    letI := L'.pointGroup t'
    letI := L.pointGroup (t' ≫ ψ)
    SchemeHomOver t' f' →* SchemeHomOver (t' ≫ ψ) f :=
  letI := L'.pointGroup t'
  letI := L.pointGroup (t' ≫ ψ)
  MonoidHom.mk' (fun P => pushAlong ψ u hu t' P) (fun P Q => Subtype.ext (hom T t' P Q))

include hom in

theorem one_val_comp {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) :
    (L'.one t').1 ≫ u = (L.one (t' ≫ ψ)).1 := by
  letI := L'.pointGroup t'
  letI := L.pointGroup (t' ≫ ψ)
  have h : pushAlong ψ u hu t' (L'.one t') = L.one (t' ≫ ψ) := map_one (pushHom L L' ψ u hu hom t')
  exact congrArg Subtype.val h

include hom in

theorem addMor_comp :
    addMor f' L' ≫ u = pullback.map f' f' f f u u ψ hu.symm hu.symm ≫ addMor f L := by
  have lhs := hom _ (pullback.fst f' f' ≫ f') ⟨pullback.fst f' f', rfl⟩ ⟨pullback.snd f' f', pullback.condition.symm⟩
  have rhs := congrArg Subtype.val
    (L.mul_natural (pullback.fst f f ≫ f) (pullback.map f' f' f f u u ψ hu.symm hu.symm ≫ pullback.fst f f ≫ f)
      (pullback.map f' f' f f u u ψ hu.symm hu.symm) rfl ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩)
  simp only [schemeHomOverComp_coe] at rhs
  rw [addMor, addMor, lhs, rhs]
  refine mul_val_congr L ?_ _ _ _ _ ?_ ?_
  · simp only [Category.assoc, pullback.lift_fst_assoc, hu]
  · simp only [schemeHomOverComp_coe, pullback.lift_fst]
  · simp only [schemeHomOverComp_coe, pullback.lift_snd]

include hom in

theorem nonempty_mumfordBundle_pullback_iso (𝓛 : A.Modules) (hinv : Scheme.Modules.IsInvertible 𝓛) :
    Nonempty (mumfordBundle f' L' ((Scheme.Modules.pullback u).obj 𝓛) ≅
      (Scheme.Modules.pullback (pullback.map f' f' f f u u ψ hu.symm hu.symm)).obj (mumfordBundle f L 𝓛)) := by
  set pp : pullback f' f' ⟶ pullback f f := pullback.map f' f' f f u u ψ hu.symm hu.symm
  have hadd : addMor f' L' ≫ u = pp ≫ addMor f L := addMor_comp L L' ψ u hu hom
  have hfst : pullback.fst f' f' ≫ u = pp ≫ pullback.fst f f := by simp only [pp, pullback.lift_fst]
  have hsnd : pullback.snd f' f' ≫ u = pp ≫ pullback.snd f f := by simp only [pp, pullback.lift_snd]
  obtain ⟨D⟩ := hinv.pullback_dual_monoidalV2 u
  let J1 : (Scheme.Modules.pullback (addMor f' L')).obj ((Scheme.Modules.pullback u).obj 𝓛) ≅
      (Scheme.Modules.pullback pp).obj ((Scheme.Modules.pullback (addMor f L)).obj 𝓛) :=
    (Scheme.Modules.pullbackComp (addMor f' L') u).app 𝓛 ≪≫ (Scheme.Modules.pullbackCongr hadd).app 𝓛 ≪≫
      ((Scheme.Modules.pullbackComp pp (addMor f L)).app 𝓛).symm
  let J2 : (Scheme.Modules.pullback (pullback.fst f' f')).obj (Scheme.Modules.dual ((Scheme.Modules.pullback u).obj 𝓛)) ≅
      (Scheme.Modules.pullback pp).obj ((Scheme.Modules.pullback (pullback.fst f f)).obj (Scheme.Modules.dual 𝓛)) :=
    (Scheme.Modules.pullback (pullback.fst f' f')).mapIso D.symm ≪≫
      (Scheme.Modules.pullbackComp (pullback.fst f' f') u).app _ ≪≫ (Scheme.Modules.pullbackCongr hfst).app _ ≪≫
        ((Scheme.Modules.pullbackComp pp (pullback.fst f f)).app _).symm
  let J3 : (Scheme.Modules.pullback (pullback.snd f' f')).obj (Scheme.Modules.dual ((Scheme.Modules.pullback u).obj 𝓛)) ≅
      (Scheme.Modules.pullback pp).obj ((Scheme.Modules.pullback (pullback.snd f f)).obj (Scheme.Modules.dual 𝓛)) :=
    (Scheme.Modules.pullback (pullback.snd f' f')).mapIso D.symm ≪≫
      (Scheme.Modules.pullbackComp (pullback.snd f' f') u).app _ ≪≫ (Scheme.Modules.pullbackCongr hsnd).app _ ≪≫
        ((Scheme.Modules.pullbackComp pp (pullback.snd f f)).app _).symm
  exact ⟨(J1 ⊗ᵢ (J2 ⊗ᵢ J3)) ≪≫
      whiskerLeftIso _ (Scheme.Modules.pullbackTensorObjIso pp _ _).symm ≪≫
        (Scheme.Modules.pullbackTensorObjIso pp _ _).symm⟩

include hom in

theorem eq_one_of_locIsoOnBase_of_isPullback (hP : IsPullback u f' f ψ)
    (𝓛 : A.Modules) (hinv : Scheme.Modules.IsInvertible 𝓛)
    (hker' : KernelTrivial f' L' ((Scheme.Modules.pullback u).obj 𝓛))
    (R : Type u) [CommRing R] (s : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S'))
    (x : SchemeHomOver (s ≫ ψ) f)
    (H : LocIsoOnBase (pullback.snd f (s ≫ ψ))
      ((Scheme.Modules.pullback (sliceAt f x)).obj (mumfordBundle f L 𝓛)) (𝟙_ _)) :
    x = L.one (s ≫ ψ) := by

  let x' : SchemeHomOver s f' := ⟨hP.lift x.1 s x.2, hP.lift_snd _ _ _⟩
  have hx' : x'.1 ≫ u = x.1 := hP.lift_fst _ _ _

  set pp : pullback f' f' ⟶ pullback f f := pullback.map f' f' f f u u ψ hu.symm hu.symm with hpp
  let r : pullback f' s ⟶ pullback f (s ≫ ψ) :=
    pullback.map f' s f (s ≫ ψ) u (𝟙 _) ψ hu.symm (by rw [Category.id_comp])
  have hr : r ≫ pullback.snd f (s ≫ ψ) = pullback.snd f' s ≫ 𝟙 _ := by
    simp only [r, pullback.lift_snd]
  have hslice : sliceAt f' x' ≫ pp = r ≫ sliceAt f x := by
    apply pullback.hom_ext
    · simp only [pp, r, sliceAt, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
    · simp only [pp, r, sliceAt, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, Category.id_comp]
      rw [hx']
  obtain ⟨ΛIso⟩ := nonempty_mumfordBundle_pullback_iso L L' ψ u hu hom 𝓛 hinv

  have Hr := AlgebraicGeometry.Polarisation.LocIsoOnBase.pullback_of_comp_eq
    (g := pullback.snd f (s ≫ ψ)) (pullback.snd f' s) r (𝟙 _) hr H
  let I1 : (Scheme.Modules.pullback r).obj (𝟙_ (pullback f (s ≫ ψ)).Modules) ≅ 𝟙_ _ :=
    Scheme.Modules.pullbackTensorUnitObjIso r
  let I2 : (Scheme.Modules.pullback (sliceAt f' x')).obj (mumfordBundle f' L' ((Scheme.Modules.pullback u).obj 𝓛)) ≅
      (Scheme.Modules.pullback r).obj ((Scheme.Modules.pullback (sliceAt f x)).obj (mumfordBundle f L 𝓛)) :=
    (Scheme.Modules.pullback (sliceAt f' x')).mapIso ΛIso ≪≫
      (Scheme.Modules.pullbackComp (sliceAt f' x') pp).app _ ≪≫
        (Scheme.Modules.pullbackCongr hslice).app _ ≪≫
          ((Scheme.Modules.pullbackComp r (sliceAt f x)).app _).symm
  have Hx' : LocIsoOnBase (pullback.snd f' s)
      ((Scheme.Modules.pullback (sliceAt f' x')).obj (mumfordBundle f' L' ((Scheme.Modules.pullback u).obj 𝓛))) (𝟙_ _) :=
    (LocIsoOnBase.equivalence _).trans (locIsoOnBase_of_iso _ I2)
      ((LocIsoOnBase.equivalence _).trans Hr (locIsoOnBase_of_iso _ I1))
  have hx'one : x' = L'.one s := hker' R s x' Hx'
  apply Subtype.ext
  rw [← hx', hx'one, one_val_comp L L' ψ u hu hom s]

end Hom

end Laws

section Algebra

variable {R B : Type u} [CommRing R] [CommRing B]

theorem apply_aug_eq_self (σ : R →+* B) (aug : B →+* R) (hret : ∀ r, aug (σ r) = r)
    (I : Ideal R) (hI : I * I = ⊥) (h : ∀ b, b - σ (aug b) ∈ I.map σ) (b : B) : σ (aug b) = b := by

  let p : B → B := fun b => b - σ (aug b)
  have hpJ : ∀ b, p b ∈ RingHom.ker aug := by
    intro b
    simp only [p, RingHom.mem_ker, map_sub, hret, sub_self]
  have hp_add : ∀ b c, p (b + c) = p b + p c := by
    intro b c; simp only [p, map_add]; ring

  have key : ∀ x ∈ I.map σ, ∀ b, p (b * x) ∈ I.map σ * RingHom.ker aug := by
    intro x hx
    refine Submodule.span_induction (p := fun x _ => ∀ b, p (b * x) ∈ I.map σ * RingHom.ker aug) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨i, hi, rfl⟩ b
      have : p (b * σ i) = p b * σ i := by
        simp only [p, map_mul, hret]; ring
      rw [this]
      exact Ideal.mul_mem_mul_rev (Ideal.mem_map_of_mem σ hi) (hpJ b)
    · intro b; simp only [mul_zero]; simpa [p] using (Ideal.zero_mem _)
    · intro x y _ _ hx hy b
      rw [mul_add, hp_add]
      exact Ideal.add_mem _ (hx b) (hy b)
    · intro c x _ hx b
      have : b * (c • x) = (b * c) * x := by simp [smul_eq_mul, mul_assoc]
      rw [this]
      exact hx (b * c)

  have hJ : RingHom.ker aug ≤ I.map σ * RingHom.ker aug := by
    intro j hj
    have hj0 : aug j = 0 := hj
    have hpj : p (1 * j) = j := by simp [p, hj0]
    have hjI : j ∈ I.map σ := by simpa [hj0] using h j
    have := key j hjI 1
    rwa [hpj] at this

  have hII : I.map σ * I.map σ = ⊥ := by
    rw [← Ideal.map_mul, hI, Ideal.map_bot]
  have hJbot : RingHom.ker aug = ⊥ := by
    refine le_bot_iff.mp ?_
    calc RingHom.ker aug ≤ I.map σ * RingHom.ker aug := hJ
      _ ≤ I.map σ * (I.map σ * RingHom.ker aug) := Ideal.mul_mono_right hJ
      _ = (I.map σ * I.map σ) * RingHom.ker aug := (mul_assoc _ _ _).symm
      _ = ⊥ := by rw [hII, Ideal.bot_mul]
  have hb : b - σ (aug b) ∈ RingHom.ker aug := hpJ b
  rw [hJbot, Ideal.mem_bot, sub_eq_zero] at hb
  exact hb.symm

end Algebra

section Rigid

variable {R₁ R₀ : Type u} [CommRing R₁] [IsLocalRing R₁] [CommRing R₀] [Nontrivial R₀]
  (φ : R₁ →+* R₀) (hφ : Function.Surjective φ)
  (hsmall : ∀ x ∈ RingHom.ker φ, ∀ m ∈ IsLocalRing.maximalIdeal R₁, x * m = 0)

theorem ker_le_maximalIdeal : RingHom.ker φ ≤ IsLocalRing.maximalIdeal R₁ :=
  IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top φ)

include hsmall in
theorem ker_mul_ker_eq_bot : RingHom.ker φ * RingHom.ker φ = ⊥ := by
  refine le_bot_iff.mp (Ideal.mul_le.mpr ?_)
  intro x hx y hy
  rw [Ideal.mem_bot]
  exact hsmall x hx y (ker_le_maximalIdeal φ hy)

include hφ hsmall in

theorem exists_comp_eq_of_isReduced {C : Type u} [CommRing C] [IsReduced C] (χ : R₁ →+* C) :
    ∃ χ₀ : R₀ →+* C, χ₀.comp φ = χ := by
  have hle : RingHom.ker φ ≤ RingHom.ker χ := by
    intro x hx
    have hxx : x * x = 0 := hsmall x hx x (ker_le_maximalIdeal φ hx)
    have h2 : χ x ^ 2 = 0 := by rw [pow_two, ← map_mul, hxx, map_zero]
    exact RingHom.mem_ker.mpr (IsReduced.eq_zero (χ x) ⟨2, h2⟩)
  refine ⟨φ.liftOfRightInverse (Function.surjInv hφ) (Function.rightInverse_surjInv hφ) ⟨χ, hle⟩, ?_⟩
  exact φ.liftOfRightInverse_comp _ _ ⟨χ, hle⟩

variable {A₁ A₀ : Scheme.{u}} {f₁ : A₁ ⟶ Spec (CommRingCat.of R₁)} {f₀ : A₀ ⟶ Spec (CommRingCat.of R₀)}
  (L₁ : RelativeGroupLaw R₁ f₁) (L₀ : RelativeGroupLaw R₀ f₀)
  (u : A₀ ⟶ A₁) (hP : IsPullback u f₀ f₁ (Spec.map (CommRingCat.ofHom φ)))
  (hom : ∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of R₀)) (P Q : SchemeHomOver t' f₀),
    (L₀.mul t' P Q).1 ≫ u =
      (L₁.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
        ⟨P.1 ≫ u, by rw [Category.assoc, hP.w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ u, by rw [Category.assoc, hP.w, ← Category.assoc, Q.2]⟩).1)

include hφ hsmall hom in

theorem kernelTrivial_of_kernelTrivial_pullback [IsNoetherianRing R₁] (hA₁ : AbelianSchemePropertyBundle R₁ f₁)
    (𝓛₁ : A₁.Modules) (hinv₁ : Scheme.Modules.IsInvertible 𝓛₁)
    (hker₀ : KernelTrivial f₀ L₀ ((Scheme.Modules.pullback u).obj 𝓛₁)) :
    KernelTrivial f₁ L₁ 𝓛₁ := by
  classical
  set ψ : Spec (CommRingCat.of R₀) ⟶ Spec (CommRingCat.of R₁) := Spec.map (CommRingCat.ofHom φ) with hψ

  have step1 : ∀ (R' : Type u) [CommRing R'] (s : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R₀))
      (y : SchemeHomOver (s ≫ ψ) f₁),
      LocIsoOnBase (pullback.snd f₁ (s ≫ ψ)) ((Scheme.Modules.pullback (sliceAt f₁ y)).obj (mumfordBundle f₁ L₁ 𝓛₁)) (𝟙_ _) →
        y = L₁.one (s ≫ ψ) :=
    fun R' _ s y Hy => eq_one_of_locIsoOnBase_of_isPullback L₁ L₀ ψ u hP.w hom hP 𝓛₁ hinv₁ hker₀ R' s y Hy

  obtain ⟨K, ι, hcl, hK⟩ :=
    hA₁.exists_isClosedImmersion_forall_iff_locIsoOnBase_sliceAt_mumfordBundle_of_isNoetherianRing L₁ 𝓛₁ hinv₁
  haveI := hcl

  set e₁ : Spec (CommRingCat.of R₁) ⟶ A₁ := (L₁.one (𝟙 _)).1 with he₁
  have he₁f : e₁ ≫ f₁ = 𝟙 _ := one_id_comp L₁
  obtain ⟨ε, hε⟩ : ∃ ε : Spec (CommRingCat.of R₁) ⟶ K, ε ≫ ι = e₁ :=
    (hK R₁ (𝟙 _) (L₁.one _)).mpr (locIsoOnBase_sliceAt_one_mumfordBundle L₁ 𝓛₁ hinv₁ R₁ (𝟙 _))

  obtain ⟨V, hVaff, hVmem, -⟩ := exists_isAffineOpen_mem_and_subset
    (X := A₁) (x := e₁.base (IsLocalRing.closedPoint R₁)) (U := ⊤) trivial
  have hVall : ∀ p : Spec (CommRingCat.of R₁), e₁.base p ∈ V := by
    have htop : e₁ ⁻¹ᵁ V = ⊤ := (IsLocalRing.closed_point_mem_iff (R := R₁)).mp hVmem
    intro p
    have : p ∈ e₁ ⁻¹ᵁ V := by rw [htop]; trivial
    exact this

  have hrange : Set.range ι.base ⊆ Set.range V.ι.base := by
    rintro _ ⟨k, rfl⟩
    rw [Scheme.Opens.range_ι]

    let ρ := K.fromSpecResidueField k
    let b : Spec (K.residueField k) ⟶ Spec (CommRingCat.of R₁) := ρ ≫ ι ≫ f₁
    obtain ⟨χ₀, hχ₀⟩ := exists_comp_eq_of_isReduced φ hφ hsmall (Spec.preimage b).hom
    let s : Spec (K.residueField k) ⟶ Spec (CommRingCat.of R₀) := Spec.map (CommRingCat.ofHom χ₀)
    have hb : b = s ≫ ψ := by
      have h1 : Spec.preimage b = CommRingCat.ofHom φ ≫ CommRingCat.ofHom χ₀ := by
        ext r
        have := congrArg (fun g => g r) hχ₀
        simpa using this.symm
      rw [← Spec.map_preimage b, h1, Spec.map_comp]
      rfl
    let y : SchemeHomOver (s ≫ ψ) f₁ := ⟨ρ ≫ ι, by rw [Category.assoc, ← hb]⟩
    have Hy := (hK _ (s ≫ ψ) y).mp ⟨ρ, rfl⟩
    have hy : y = L₁.one (s ≫ ψ) := step1 _ s y Hy
    have hval : ρ ≫ ι = (s ≫ ψ) ≫ e₁ := by
      have := congrArg Subtype.val hy
      simpa [y, he₁, one_val_eq_comp L₁ (s ≫ ψ)] using this
    have hk : ι.base k = (ρ ≫ ι).base (default : Spec (K.residueField k)) := by
      simp [ρ, Scheme.Hom.comp_apply]
    rw [hk, hval]
    simp only [Scheme.Hom.comp_apply]
    exact hVall _
  let ι' : K ⟶ V := IsOpenImmersion.lift V.ι ι hrange
  have hι' : ι' ≫ V.ι = ι := IsOpenImmersion.lift_fac _ _ _
  haveI : IsClosedImmersion (ι' ≫ V.ι) := by rw [hι']; infer_instance
  haveI : IsClosedImmersion ι' := IsClosedImmersion.of_comp ι' V.ι
  haveI : IsAffine V := hVaff
  haveI : IsAffine K := isAffine_of_isAffineHom ι'

  let eK : K ≅ Spec Γ(K, ⊤) := K.isoSpec
  let ιB : Spec Γ(K, ⊤) ⟶ A₁ := eK.inv ≫ ι
  haveI : Mono ιB := mono_comp _ _
  let σ' : CommRingCat.of R₁ ⟶ Γ(K, ⊤) := Spec.preimage (ιB ≫ f₁)
  have hσ' : Spec.map σ' = ιB ≫ f₁ := Spec.map_preimage _
  let aug' : Γ(K, ⊤) ⟶ CommRingCat.of R₁ := Spec.preimage (ε ≫ eK.hom)
  have haug' : Spec.map aug' = ε ≫ eK.hom := Spec.map_preimage _
  have hεB : Spec.map aug' ≫ ιB = e₁ := by
    rw [haug', Category.assoc]; simp only [ιB, Iso.hom_inv_id_assoc]; exact hε

  have hret' : σ' ≫ aug' = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_id, hσ', ← Category.assoc, hεB, he₁f]
  let σ : R₁ →+* Γ(K, ⊤) := σ'.hom
  let aug : Γ(K, ⊤) →+* R₁ := aug'.hom
  have hret : ∀ r, aug (σ r) = r := by
    intro r
    have := congrArg (fun g => (CommRingCat.Hom.hom g) r) hret'
    simpa [σ, aug] using this

  let I : Ideal R₁ := RingHom.ker φ
  let IB : Ideal Γ(K, ⊤) := I.map σ
  let C : Type u := Γ(K, ⊤) ⧸ IB
  let π : Γ(K, ⊤) →+* C := Ideal.Quotient.mk IB
  have hπσ : RingHom.ker φ ≤ RingHom.ker (π.comp σ) := by
    intro i hi
    simp only [RingHom.mem_ker, RingHom.coe_comp, Function.comp_apply, π]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem σ hi)
  let τ : R₀ →+* C := φ.liftOfRightInverse (Function.surjInv hφ) (Function.rightInverse_surjInv hφ) ⟨π.comp σ, hπσ⟩
  have hτ : τ.comp φ = π.comp σ := φ.liftOfRightInverse_comp _ _ ⟨π.comp σ, hπσ⟩
  let π' : Γ(K, ⊤) ⟶ CommRingCat.of C := CommRingCat.ofHom π
  let s : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of R₀) := Spec.map (CommRingCat.ofHom τ)
  have hbase : Spec.map π' ≫ ιB ≫ f₁ = s ≫ ψ := by
    rw [← hσ', ← Spec.map_comp, hψ, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hτ]
    rfl
  let y : SchemeHomOver (s ≫ ψ) f₁ := ⟨Spec.map π' ≫ ιB, by rw [Category.assoc, hbase]⟩
  have Hy := (hK C (s ≫ ψ) y).mp ⟨Spec.map π' ≫ eK.inv, by simp [y, ιB]⟩
  have hy : y = L₁.one (s ≫ ψ) := step1 C s y Hy
  have hyval : Spec.map π' ≫ ιB = Spec.map (σ' ≫ π') ≫ Spec.map aug' ≫ ιB := by
    have h1 : Spec.map π' ≫ ιB = (s ≫ ψ) ≫ e₁ := by
      have := congrArg Subtype.val hy
      simpa [y, he₁, one_val_eq_comp L₁ (s ≫ ψ)] using this
    rw [h1, hεB, ← hbase, ← hσ', ← Spec.map_comp]
  have hππ : π' = aug' ≫ σ' ≫ π' := by
    apply Spec.map_injective
    rw [← cancel_mono ιB, hyval, Spec.map_comp aug' (σ' ≫ π'), Category.assoc]
  have hdiff : ∀ bb : Γ(K, ⊤), bb - σ (aug bb) ∈ I.map σ := by
    intro bb
    have := congrArg (fun g => (CommRingCat.Hom.hom g) bb) hππ
    have h2 : π bb = π (σ (aug bb)) := by simpa [π', σ, aug] using this
    rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    exact h2

  have hsec : ∀ bb : Γ(K, ⊤), σ (aug bb) = bb :=
    apply_aug_eq_self σ aug hret I (ker_mul_ker_eq_bot φ hsmall) hdiff
  have hsec' : aug' ≫ σ' = 𝟙 _ := by
    ext bb
    simpa [σ, aug] using hsec bb

  intro R _ t' x H
  obtain ⟨k, hk⟩ := (hK R t' x).mpr H
  let κ' : Γ(K, ⊤) ⟶ CommRingCat.of R := Spec.preimage (k ≫ eK.hom)
  have hκ' : Spec.map κ' = k ≫ eK.hom := Spec.map_preimage _
  have hx1 : x.1 = Spec.map κ' ≫ ιB := by
    rw [hκ', Category.assoc]; simp only [ιB, Iso.hom_inv_id_assoc]; exact hk.symm
  have hκ'2 : Spec.map κ' = t' ≫ Spec.map aug' := by
    have : κ' = aug' ≫ σ' ≫ κ' := by rw [← Category.assoc, hsec', Category.id_comp]
    rw [this, Spec.map_comp, Spec.map_comp, Category.assoc, hσ', ← x.2, hx1]
    simp only [Category.assoc]
  apply Subtype.ext
  rw [hx1, hκ'2, Category.assoc, hεB, he₁, ← one_val_eq_comp L₁ t']

end Rigid

section Frame

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S] (E : FakeEllipticCurve Λ N S)

abbrev ιR (R : Type) [CommRing R] [Algebra S R] : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S) :=
  Spec.map (CommRingCat.ofHom (algebraMap S R))

abbrev fR (R : Type) [CommRing R] [Algebra S R] : pullback E.f (ιR (S := S) R) ⟶ Spec (CommRingCat.of R) :=
  pullback.snd E.f (ιR (S := S) R)

def CompatLaw (R : Type) [CommRing R] [Algebra S R] (LR : RelativeGroupLaw R (fR E R)) : Prop :=
  ∀ (T : Scheme) (t' : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t' (fR E R)),
    (LR.mul t' P Q).1 ≫ pullback.fst E.f (ιR (S := S) R) =
      (E.L.mul (t' ≫ ιR (S := S) R)
        ⟨P.1 ≫ pullback.fst E.f (ιR (S := S) R), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ pullback.fst E.f (ιR (S := S) R), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1

theorem bundle_baseChange (R : Type) [CommRing R] [Algebra S R] : AbelianSchemePropertyBundle R (fR E R) :=
  E.bundle.of_isPullback (IsPullback.of_hasPullback E.f (ιR (S := S) R))

variable {E}
variable {R₁ R₀ : Type} [CommRing R₁] [CommRing R₀] [Algebra S R₁] [Algebra S R₀] (φ : R₁ →ₐ[S] R₀)

theorem specMap_comp_ιR :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ ιR (S := S) R₁ = ιR (S := S) R₀ := by
  rw [ιR, ιR, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact φ.comp_algebraMap

variable
  (t : pullback E.f (ιR (S := S) R₀) ⟶ pullback E.f (ιR (S := S) R₁))
  (ht₁ : t ≫ pullback.fst E.f (ιR (S := S) R₁) = pullback.fst E.f (ιR (S := S) R₀))
  (ht₂ : t ≫ pullback.snd E.f (ιR (S := S) R₁) = pullback.snd E.f (ιR (S := S) R₀) ≫ Spec.map (CommRingCat.ofHom φ.toRingHom))
  (L₁ : RelativeGroupLaw R₁ (fR E R₁)) (hL₁ : CompatLaw E R₁ L₁)
  (L₀ : RelativeGroupLaw R₀ (fR E R₀)) (hL₀ : CompatLaw E R₀ L₀)

include ht₁ ht₂ in

theorem isPullback_transition :
    IsPullback t (fR E R₀) (fR E R₁) (Spec.map (CommRingCat.ofHom φ.toRingHom)) := by
  have sq : IsPullback (t ≫ pullback.fst E.f (ιR (S := S) R₁)) (fR E R₀) E.f
      (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ ιR (S := S) R₁) := by
    rw [ht₁, specMap_comp_ιR]
    exact IsPullback.of_hasPullback _ _
  exact IsPullback.of_right sq ht₂ (IsPullback.of_hasPullback _ _)

include ht₁ ht₂ hL₁ hL₀ in

theorem transition_hom :
    ∀ (T : Scheme) (t' : T ⟶ Spec (CommRingCat.of R₀)) (P Q : SchemeHomOver t' (fR E R₀)),
      (L₀.mul t' P Q).1 ≫ t =
        (L₁.mul (t' ≫ Spec.map (CommRingCat.ofHom φ.toRingHom))
          ⟨P.1 ≫ t, by rw [Category.assoc, ht₂, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ t, by rw [Category.assoc, ht₂, ← Category.assoc, Q.2]⟩).1 := by
  intro T t' P Q
  apply pullback.hom_ext
  · rw [Category.assoc, ht₁, hL₀ T t' P Q, hL₁ T _ _ _]
    refine mul_val_congr E.L ?_ _ _ _ _ ?_ ?_
    · rw [Category.assoc, specMap_comp_ιR]
    · simp only [Category.assoc, ht₁]
    · simp only [Category.assoc, ht₁]
  · conv_lhs => rw [Category.assoc, ht₂, ← Category.assoc, (L₀.mul t' P Q).2]
    exact ((L₁.mul _ _ _).2).symm

end Frame

end CerednikDrinfeld.QM.KerPermAux
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_kernelTrivial_of_kernelTrivial_of_pullback_iso_of_surjective_of_ker_mul_maximalIdeal_of_isNoetherianRing.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_kernelTrivial_of_kernelTrivial_of_pullback_iso_of_surjective_of_ker_mul_maximalIdeal_of_isNoetherianRing.CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_kernelTrivial_of_kernelTrivial_of_pullback_iso_of_surjective_of_ker_mul_maximalIdeal_of_isNoetherianRing.CerednikDrinfeld.QM.KerPermAux"
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_kernelTrivial_of_kernelTrivial_of_pullback_iso_of_surjective_of_ker_mul_maximalIdeal_of_isNoetherianRing.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_kernelTrivial_of_kernelTrivial_of_pullback_iso_of_surjective_of_ker_mul_maximalIdeal_of_isNoetherianRing.CerednikDrinfeld.QM"
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_kernelTrivial_of_kernelTrivial_of_pullback_iso_of_surjective_of_ker_mul_maximalIdeal_of_isNoetherianRing.CerednikDrinfeld"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_kernelTrivial_of_kernelTrivial_of_pullback_iso_of_surjective_of_ker_mul_maximalIdeal_of_isNoetherianRing.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_kernelTrivial_of_kernelTrivial_of_pullback_iso_of_surjective_of_ker_mul_maximalIdeal_of_isNoetherianRing.CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_kernelTrivial_of_kernelTrivial_of_pullback_iso_of_surjective_of_ker_mul_maximalIdeal_of_isNoetherianRing.CerednikDrinfeld.QM.KerPermAux"

open CerednikDrinfeld.QM.KerPermAux in
theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (N : ℕ) (S : Type) [CommRing S] (E : FakeEllipticCurve Λ N S)

    (R₁ R₀ : Type) [CommRing R₁] [IsLocalRing R₁] [IsNoetherianRing R₁]
    [CommRing R₀] [Nontrivial R₀] [Algebra S R₁] [Algebra S R₀]
    (φ : R₁ →ₐ[S] R₀) (hφ : Function.Surjective φ)
    (hsmall : ∀ x ∈ RingHom.ker φ.toRingHom, ∀ m ∈ IsLocalRing.maximalIdeal R₁, x * m = 0)

    (t : pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀))) ⟶ pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁))))
    (ht₁ : t ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁))) = pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀))))
    (ht₂ : t ≫ pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁))) =
      pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀))) ≫ Spec.map (CommRingCat.ofHom φ.toRingHom))

    (L₁ : RelativeGroupLaw R₁ (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁)))))
    (hL₁ : ∀ (T : Scheme) (t' : T ⟶ Spec (CommRingCat.of R₁))
        (P Q : SchemeHomOver t' (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁))))),
        (L₁.mul t' P Q).1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁))) =
          (E.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S R₁))))
            ⟨P.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1)
    (L₀ : RelativeGroupLaw R₀ (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀)))))
    (hL₀ : ∀ (T : Scheme) (t' : T ⟶ Spec (CommRingCat.of R₀))
        (P Q : SchemeHomOver t' (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀))))),
        (L₀.mul t' P Q).1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀))) =
          (E.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S R₀))))
            ⟨P.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1)

    (𝓛₀ : (pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀)))).Modules)
    (hker₀ : KernelTrivial (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀)))) L₀ 𝓛₀)
    (𝓛₁ : (pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁)))).Modules)
    (hinv₁ : Scheme.Modules.IsInvertible 𝓛₁) (hiso : Nonempty ((Scheme.Modules.pullback t).obj 𝓛₁ ≅ 𝓛₀)) :
    KernelTrivial (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁)))) L₁ 𝓛₁ := by
  obtain ⟨e⟩ := hiso
  have hP := isPullback_transition (E := E) φ t ht₁ ht₂
  have thom := transition_hom (E := E) φ t ht₁ ht₂ L₁ hL₁ L₀ hL₀

  have hinv₀ : Scheme.Modules.IsInvertible 𝓛₀ := by
    obtain ⟨U⟩ := (⟨e⟩ : Nonempty _)
    exact ⟨fun x => by
      obtain ⟨V, hx, ⟨i⟩⟩ := (hinv₁.pullback t).exists_trivialization x
      exact ⟨V, hx, ⟨((Scheme.Modules.pullback V.ι).mapIso U).symm ≪≫ i⟩⟩⟩
  have hker₀' : KernelTrivial (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀)))) L₀
      ((Scheme.Modules.pullback t).obj 𝓛₁) :=
    kernelTrivial_of_iso L₀ hinv₀ (hinv₁.pullback t) e.symm hker₀
  exact kernelTrivial_of_kernelTrivial_pullback φ.toRingHom hφ hsmall L₁ L₀ t hP thom
    (bundle_baseChange E R₁) 𝓛₁ hinv₁ hker₀'

end S_CerednikDrinfeld_QM_FakeEllipticCurve_kernelTrivial_of_kernelTrivial_of_pullback_iso_of_surjective_of_ker_mul_maximalIdeal_of_isNoetherianRing
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_kernelTrivial_of_kernelTrivial_of_pullback_iso_of_surjective_of_ker_mul_maximalIdeal_of_isNoetherianRing (solution)
