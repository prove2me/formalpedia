-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_fg_subalgebra_extension_kernelTrivial_pullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/86c97bad-2ce4-5536-8d10-c2f0fbd2982a

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_pullback_of_comp_eq
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_isClosedImmersion_forall_iff_locIsoOnBase_sliceAt_mumfordBundle_of_isNoetherianRing
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullback_levelIff
import Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_comp_eq_pullback_fst_comp_of_comp_eq_of_locallyOfFinitePresentation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_extension_kernelTrivial_pullback
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans"
p2m_attr_erase "instance" "AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.sndPoint_coe GoodReductionJacobian.RelativeGroupLaw.fstPoint_coe AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt"
p2m_attr_erase "simp" "AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"

set_option autoImplicit false

open scoped TensorProduct Quaternion
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

universe u v

noncomputable section

namespace P2DM4Kit

theorem isPullback_of_lift {C : Type*} [Category C] {A A' B B' T T₁ : C} {f : A ⟶ B} {f' : A' ⟶ B'} {gA : A' ⟶ A}
    {b : B' ⟶ B} (hg : IsPullback gA f' f b) (ι'' : T ⟶ B') (ι₁ : T₁ ⟶ B) (j : T ⟶ T₁) (hbase : ι'' ≫ b = j ≫ ι₁)
    [HasPullback f' ι''] [HasPullback f ι₁]
    (u₁ : pullback f' ι'' ⟶ pullback f ι₁) (h1 : u₁ ≫ pullback.fst f ι₁ = pullback.fst f' ι'' ≫ gA)
    (h2 : u₁ ≫ pullback.snd f ι₁ = pullback.snd f' ι'' ≫ j) :
    IsPullback u₁ (pullback.snd f' ι'') (pullback.snd f ι₁) j := by
  have big := (IsPullback.of_hasPullback f' ι'').paste_horiz hg
  rw [← h1, hbase] at big
  exact IsPullback.of_right big h2 (IsPullback.of_hasPullback f ι₁)

variable {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}

theorem mul_val_congr (L : RelativeGroupLaw S f) {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of S)} (h : t = t')
    (P Q : SchemeHomOver t f) (P' Q' : SchemeHomOver t' f) (hP : P.1 = P'.1) (hQ : Q.1 = Q'.1) :
    (L.mul t P Q).1 = (L.mul t' P' Q').1 := by
  subst h
  obtain ⟨P, hP0⟩ := P; obtain ⟨Q, hQ0⟩ := Q; obtain ⟨P', hP1⟩ := P'; obtain ⟨Q', hQ1⟩ := Q'
  simp only at hP hQ
  subst hP; subst hQ
  rfl

theorem inv_val_congr (L : RelativeGroupLaw S f) {T : Scheme.{u}} {s s' : T ⟶ Spec (CommRingCat.of S)} (hs : s = s')
    (P : SchemeHomOver s f) (Q : SchemeHomOver s' f) (hPQ : P.1 = Q.1) : (L.inv s P).1 = (L.inv s' Q).1 := by
  subst hs; cases Subtype.ext hPQ; rfl

theorem locIsoOnBase_of_iso {R : Type u} [CommRing R] {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of R))
    {M M' : X.Modules} (e : M ≅ M') : LocIsoOnBase g M M' :=
  fun _ => ⟨⊤, trivial, ⟨(Scheme.Modules.pullback (g ⁻¹ᵁ ⊤).ι).mapIso e⟩⟩

def transitionHom (G : RelativeGroupLaw S f) {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
    (t'' : T' ⟶ Spec (CommRingCat.of S)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t'') :
    letI := G.pointGroup t; letI := G.pointGroup t''; SchemeHomOver t f →* SchemeHomOver t'' f :=
  letI := G.pointGroup t; letI := G.pointGroup t''
  { toFun := GoodReductionJacobian.schemeHomOverComp ψ hψ
    map_one' := G.one_natural t t'' ψ hψ
    map_mul' := fun x y => G.mul_natural t t'' ψ hψ x y }

theorem inv_natural (G : RelativeGroupLaw S f) {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
    (t'' : T' ⟶ Spec (CommRingCat.of S)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t'') (x : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (G.inv t x) =
      G.inv t'' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by
  letI := G.pointGroup t; letI := G.pointGroup t''
  exact map_inv (transitionHom G t t'' ψ hψ) x

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
theorem pushAlong_mul {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' f') :
    pushAlong ψ u hu t' (L'.mul t' P Q) = L.mul (t' ≫ ψ) (pushAlong ψ u hu t' P) (pushAlong ψ u hu t' Q) :=
  Subtype.ext (hom T t' P Q)

include hom in
theorem pushAlong_one {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) :
    pushAlong ψ u hu t' (L'.one t') = L.one (t' ≫ ψ) := by
  letI := L'.pointGroup t'
  letI := L.pointGroup (t' ≫ ψ)
  exact map_one (pushHom L L' ψ u hu hom t')

include hom in
theorem pushAlong_inv {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' f') :
    pushAlong ψ u hu t' (L'.inv t' P) = L.inv (t' ≫ ψ) (pushAlong ψ u hu t' P) := by
  letI := L'.pointGroup t'
  letI := L.pointGroup (t' ≫ ψ)
  exact map_inv (pushHom L L' ψ u hu hom t') P

include hom in

theorem one_val_comp {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) :
    (L'.one t').1 ≫ u = (L.one (t' ≫ ψ)).1 :=
  congrArg Subtype.val (pushAlong_one L L' ψ u hu hom t')

include hom in

theorem negMor_comp : negMor f' L' ≫ u = u ≫ negMor f L := by
  have h1 : negMor f' L' ≫ u = (L.inv _ (pushAlong ψ u hu f' (idPt f'))).1 := by
    change (pushAlong ψ u hu f' (L'.inv f' (idPt f'))).1 = _
    rw [pushAlong_inv L L' ψ u hu hom]
  have h2 : u ≫ negMor f L = (L.inv (u ≫ f) (GoodReductionJacobian.schemeHomOverComp u rfl (idPt f))).1 := by
    change (GoodReductionJacobian.schemeHomOverComp u rfl (L.inv f (idPt f))).1 = _
    rw [inv_natural]
  rw [h1, h2]
  exact inv_val_congr L hu.symm _ _ (by simp [idPt])

include hom in

theorem addMor_comp :
    addMor f' L' ≫ u = pullback.map f' f' f f u u ψ hu.symm hu.symm ≫ addMor f L := by
  have lhs := hom _ (pullback.fst f' f' ≫ f') ⟨pullback.fst f' f', rfl⟩ ⟨pullback.snd f' f', pullback.condition.symm⟩
  have rhs := congrArg Subtype.val
    (L.mul_natural (pullback.fst f f ≫ f) (pullback.map f' f' f f u u ψ hu.symm hu.symm ≫ pullback.fst f f ≫ f)
      (pullback.map f' f' f f u u ψ hu.symm hu.symm) rfl ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩)
  simp only [GoodReductionJacobian.schemeHomOverComp_coe] at rhs
  rw [addMor, addMor, lhs, rhs]
  refine mul_val_congr L ?_ _ _ _ _ ?_ ?_
  · simp only [Category.assoc, pullback.lift_fst_assoc, hu]
  · simp only [GoodReductionJacobian.schemeHomOverComp_coe, pullback.lift_fst]
  · simp only [GoodReductionJacobian.schemeHomOverComp_coe, pullback.lift_snd]

include hom in
theorem nonempty_mumfordBundleIso (𝓛 : A.Modules) (hinv : Scheme.Modules.IsInvertible 𝓛) :
    Nonempty (mumfordBundle f' L' ((Scheme.Modules.pullback u).obj 𝓛) ≅
      (Scheme.Modules.pullback (pullback.map f' f' f f u u ψ hu.symm hu.symm)).obj (mumfordBundle f L 𝓛)) := by
  let pp : pullback f' f' ⟶ pullback f f := pullback.map f' f' f f u u ψ hu.symm hu.symm
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

theorem locIso_sliceAt_iff (hP : IsPullback u f' f ψ) (𝓛 : A.Modules) (hinv : Scheme.Modules.IsInvertible 𝓛)
    {R : Type u} [CommRing R] (t' : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S')) (x' : SchemeHomOver t' f') :
    LocIsoOnBase (pullback.snd f' t')
        ((Scheme.Modules.pullback (sliceAt f' x')).obj (mumfordBundle f' L' ((Scheme.Modules.pullback u).obj 𝓛)))
        (𝟙_ ((pullback f' t').Modules)) ↔
      LocIsoOnBase (pullback.snd f (t' ≫ ψ))
        ((Scheme.Modules.pullback (sliceAt f (pushAlong ψ u hu t' x'))).obj (mumfordBundle f L 𝓛))
        (𝟙_ ((pullback f (t' ≫ ψ)).Modules)) := by
  obtain ⟨ΛIso⟩ := nonempty_mumfordBundleIso L L' ψ u hu hom 𝓛 hinv
  let x : SchemeHomOver (t' ≫ ψ) f := pushAlong ψ u hu t' x'
  let pp : pullback f' f' ⟶ pullback f f := pullback.map f' f' f f u u ψ hu.symm hu.symm

  let r : pullback f (t' ≫ ψ) ⟶ pullback f' t' :=
    pullback.lift
      (hP.lift (pullback.fst f (t' ≫ ψ)) (pullback.snd f (t' ≫ ψ) ≫ t')
        (by rw [Category.assoc]; exact pullback.condition))
      (pullback.snd f (t' ≫ ψ)) (by rw [IsPullback.lift_snd])
  let s : pullback f' t' ⟶ pullback f (t' ≫ ψ) :=
    pullback.lift (pullback.fst f' t' ≫ u) (pullback.snd f' t')
      (by rw [Category.assoc, hu, ← Category.assoc, pullback.condition, Category.assoc])
  have hr : r ≫ pullback.snd f' t' = pullback.snd f (t' ≫ ψ) ≫ 𝟙 _ := by
    simp only [r, pullback.lift_snd, Category.comp_id]
  have hs : s ≫ pullback.snd f (t' ≫ ψ) = pullback.snd f' t' ≫ 𝟙 _ := by
    simp only [s, pullback.lift_snd, Category.comp_id]
  have hslice_r : (r ≫ sliceAt f' x') ≫ pp = sliceAt f x := by
    apply pullback.hom_ext
    · simp only [r, pp, sliceAt, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, IsPullback.lift_fst]
    · simp only [r, pp, sliceAt, x, pushAlong, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
  have hslice_s : s ≫ sliceAt f x = sliceAt f' x' ≫ pp := by
    apply pullback.hom_ext
    · simp only [s, pp, sliceAt, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
    · simp only [s, pp, sliceAt, x, pushAlong, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]

  let I1r : (Scheme.Modules.pullback r).obj (𝟙_ (pullback f' t').Modules) ≅ 𝟙_ _ :=
    Scheme.Modules.pullbackTensorUnitObjIso r
  let I2r : (Scheme.Modules.pullback r).obj
        ((Scheme.Modules.pullback (sliceAt f' x')).obj (mumfordBundle f' L' ((Scheme.Modules.pullback u).obj 𝓛))) ≅
      (Scheme.Modules.pullback (sliceAt f x)).obj (mumfordBundle f L 𝓛) :=
    (Scheme.Modules.pullback r).mapIso ((Scheme.Modules.pullback (sliceAt f' x')).mapIso ΛIso) ≪≫
      (Scheme.Modules.pullbackComp r (sliceAt f' x')).app _ ≪≫
        (Scheme.Modules.pullbackComp (r ≫ sliceAt f' x') pp).app _ ≪≫
          (Scheme.Modules.pullbackCongr hslice_r).app _

  let I1s : (Scheme.Modules.pullback s).obj (𝟙_ (pullback f (t' ≫ ψ)).Modules) ≅ 𝟙_ _ :=
    Scheme.Modules.pullbackTensorUnitObjIso s
  let I2s : (Scheme.Modules.pullback s).obj ((Scheme.Modules.pullback (sliceAt f x)).obj (mumfordBundle f L 𝓛)) ≅
      (Scheme.Modules.pullback (sliceAt f' x')).obj (mumfordBundle f' L' ((Scheme.Modules.pullback u).obj 𝓛)) :=
    (Scheme.Modules.pullbackComp s (sliceAt f x)).app _ ≪≫
      (Scheme.Modules.pullbackCongr hslice_s).app _ ≪≫
        ((Scheme.Modules.pullbackComp (sliceAt f' x') pp).app _).symm ≪≫
          (Scheme.Modules.pullback (sliceAt f' x')).mapIso ΛIso.symm
  constructor
  · intro H'
    have Hr := AlgebraicGeometry.Polarisation.LocIsoOnBase.pullback_of_comp_eq
      (g := pullback.snd f' t') (pullback.snd f (t' ≫ ψ)) r (𝟙 _) hr H'
    exact (AlgebraicGeometry.Polarisation.LocIsoOnBase.equivalence _).trans (locIsoOnBase_of_iso _ I2r.symm)
      ((AlgebraicGeometry.Polarisation.LocIsoOnBase.equivalence _).trans Hr (locIsoOnBase_of_iso _ I1r))
  · intro H
    have Hs := AlgebraicGeometry.Polarisation.LocIsoOnBase.pullback_of_comp_eq
      (g := pullback.snd f (t' ≫ ψ)) (pullback.snd f' t') s (𝟙 _) hs H
    exact (AlgebraicGeometry.Polarisation.LocIsoOnBase.equivalence _).trans (locIsoOnBase_of_iso _ I2s.symm)
      ((AlgebraicGeometry.Polarisation.LocIsoOnBase.equivalence _).trans Hs (locIsoOnBase_of_iso _ I1s))

include hom in

theorem mul_self_eq_one_iff (hP : IsPullback u f' f ψ) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S'))
    (x' : SchemeHomOver t' f') :
    L'.mul t' x' x' = L'.one t' ↔
      L.mul (t' ≫ ψ) (pushAlong ψ u hu t' x') (pushAlong ψ u hu t' x') = L.one (t' ≫ ψ) := by
  constructor
  · intro h
    rw [← pushAlong_mul L L' ψ u hu hom, h, pushAlong_one L L' ψ u hu hom]
  · intro h
    apply Subtype.ext
    apply hP.hom_ext
    · rw [one_val_comp L L' ψ u hu hom t']
      exact (hom T t' x' x').trans (congrArg Subtype.val h)
    · rw [(L'.mul t' x' x').2, (L'.one t').2]

include hom in

theorem kernelTrivial_of_isPullback (hP : IsPullback u f' f ψ)
    (𝓛 : A.Modules) (hinv : Scheme.Modules.IsInvertible 𝓛) (hker : KernelTrivial f L 𝓛) :
    KernelTrivial f' L' ((Scheme.Modules.pullback u).obj 𝓛) := by
  intro R _ t' x' H'
  have hx : pushAlong ψ u hu t' x' = L.one (t' ≫ ψ) :=
    hker R (t' ≫ ψ) (pushAlong ψ u hu t' x') ((locIso_sliceAt_iff L L' ψ u hu hom hP 𝓛 hinv t' x').1 H')
  apply Subtype.ext
  apply hP.hom_ext
  · rw [one_val_comp L L' ψ u hu hom t']
    exact congrArg Subtype.val hx
  · rw [x'.2, (L'.one t').2]

include hom in

theorem kernelIsTwoTorsion_of_isPullback (hP : IsPullback u f' f ψ)
    (𝓛 : A.Modules) (hinv : Scheme.Modules.IsInvertible 𝓛) (hK : KernelIsTwoTorsion f L 𝓛) :
    KernelIsTwoTorsion f' L' ((Scheme.Modules.pullback u).obj 𝓛) := by
  intro R _ t' x'
  rw [locIso_sliceAt_iff L L' ψ u hu hom hP 𝓛 hinv t' x', hK R (t' ≫ ψ) (pushAlong ψ u hu t' x'),
    mul_self_eq_one_iff L L' ψ u hu hom hP t' x']

end Hom

end P2DM4Kit
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_extension_kernelTrivial_pullback.P2DM4Kit"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_extension_kernelTrivial_pullback.P2DM4Kit"

open P2DM4Kit in
theorem solution
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (N : ℕ) (R : Type) [CommRing R] (E : FakeEllipticCurve Λ N R)
    (T₀ : Subalgebra ℤ R) (hT₀ : T₀.FG) (E₀ : FakeEllipticCurve Λ N ↥T₀) (g₀ : E.A ⟶ E₀.A)
    (hg₀ : CategoryTheory.IsPullback g₀ E.f E₀.f (Spec.map (CommRingCat.ofHom T₀.val.toRingHom)))
    (hlaw₀ :
      (∀ {X : Scheme.{0}} (t' : X ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t' E.f),
        (E.L.mul t' P Q).1 ≫ g₀ =
          (E₀.L.mul (t' ≫ Spec.map (CommRingCat.ofHom T₀.val.toRingHom))
            ⟨P.1 ≫ g₀, by rw [Category.assoc, hg₀.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ g₀, by rw [Category.assoc, hg₀.w, ← Category.assoc, Q.2]⟩).1))
    (hact₀ : ∀ x : ↥Λ, E.act x ≫ g₀ = g₀ ≫ E₀.act x)
    (𝓜₀ : E₀.A.Modules) (h₀ : Scheme.Modules.IsInvertible 𝓜₀)
    (hK : KernelTrivial E.f E.L ((Scheme.Modules.pullback g₀).obj 𝓜₀)) :
    ∃ (T : Subalgebra ℤ R) (_ : T.FG) (hle : T₀ ≤ T) (ET : FakeEllipticCurve Λ N ↥T) (g : E.A ⟶ ET.A)
      (hg : CategoryTheory.IsPullback g E.f ET.f (Spec.map (CommRingCat.ofHom T.val.toRingHom)))
      (h : ET.A ⟶ E₀.A)
      (hh : CategoryTheory.IsPullback h ET.f E₀.f (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hle).toRingHom))),
      g ≫ h = g₀ ∧
      (∀ {X : Scheme.{0}} (t' : X ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t' E.f),
        (E.L.mul t' P Q).1 ≫ g =
          (ET.L.mul (t' ≫ Spec.map (CommRingCat.ofHom T.val.toRingHom))
            ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1) ∧
      (∀ x : ↥Λ, E.act x ≫ g = g ≫ ET.act x) ∧
      (∀ {X : Scheme.{0}} (t' : X ⟶ Spec (CommRingCat.of ↥T)) (P Q : SchemeHomOver t' ET.f),
        (ET.L.mul t' P Q).1 ≫ h =
          (E₀.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hle).toRingHom))
            ⟨P.1 ≫ h, by rw [Category.assoc, hh.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ h, by rw [Category.assoc, hh.w, ← Category.assoc, Q.2]⟩).1) ∧
      (∀ x : ↥Λ, ET.act x ≫ h = h ≫ E₀.act x) ∧
      KernelTrivial ET.f ET.L ((Scheme.Modules.pullback h).obj 𝓜₀) := by
  classical

  haveI : IsNoetherianRing ↥T₀ := by
    haveI : Algebra.FiniteType ℤ ↥T₀ := (Subalgebra.fg_iff_finiteType T₀).1 hT₀
    exact Algebra.FiniteType.isNoetherianRing ℤ ↥T₀
  haveI : IsProper E₀.f := E₀.bundle.proper

  obtain ⟨K, ι, hι, hKpt⟩ :=
    GoodReductionJacobian.AbelianSchemePropertyBundle.exists_isClosedImmersion_forall_iff_locIsoOnBase_sliceAt_mumfordBundle_of_isNoetherianRing
      E₀.bundle E₀.L 𝓜₀ h₀
  haveI : IsClosedImmersion ι := hι

  have he₀ : (E₀.L.one (𝟙 _)).1 ≫ E₀.f = 𝟙 (Spec (CommRingCat.of ↥T₀)) := (E₀.L.one (𝟙 _)).2
  have hone₀ : ∀ {X : Scheme.{0}} (s : X ⟶ Spec (CommRingCat.of ↥T₀)), (E₀.L.one s).1 = s ≫ (E₀.L.one (𝟙 _)).1 :=
    fun s => (congrArg Subtype.val (E₀.L.one_natural (𝟙 _) s s (Category.comp_id s))).symm

  have hom₀ : ∀ (X : Scheme.{0}) (t' : X ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t' E.f),
      (E.L.mul t' P Q).1 ≫ g₀ =
        (E₀.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom T₀.val.toRingHom)))
          ⟨P.1 ≫ g₀, by rw [Category.assoc, hg₀.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g₀, by rw [Category.assoc, hg₀.w, ← Category.assoc, Q.2]⟩).1 :=
    fun X t' P Q => hlaw₀ t' P Q

  let κ : pullback (ι ≫ E₀.f) (Spec.map (CommRingCat.ofHom T₀.val.toRingHom)) ⟶ E.A :=
    hg₀.lift (pullback.fst (ι ≫ E₀.f) (Spec.map (CommRingCat.ofHom T₀.val.toRingHom)) ≫ ι) (pullback.snd (ι ≫ E₀.f) (Spec.map (CommRingCat.ofHom T₀.val.toRingHom)))
      (by rw [Category.assoc]; exact pullback.condition)
  have hκ1 : κ ≫ g₀ = pullback.fst (ι ≫ E₀.f) (Spec.map (CommRingCat.ofHom T₀.val.toRingHom)) ≫ ι := hg₀.lift_fst _ _ _
  have hκ2 : κ ≫ E.f = pullback.snd (ι ≫ E₀.f) (Spec.map (CommRingCat.ofHom T₀.val.toRingHom)) := hg₀.lift_snd _ _ _

  have key : ∀ (R' : Type) [CommRing R'] (m : Spec (CommRingCat.of R') ⟶ pullback (ι ≫ E₀.f) (Spec.map (CommRingCat.ofHom T₀.val.toRingHom))),
      m ≫ κ = m ≫ (E.L.one (pullback.snd (ι ≫ E₀.f) (Spec.map (CommRingCat.ofHom T₀.val.toRingHom)))).1 := by
    intro R' _ m
    let x : SchemeHomOver (m ≫ pullback.snd (ι ≫ E₀.f) (Spec.map (CommRingCat.ofHom T₀.val.toRingHom))) E.f := ⟨m ≫ κ, by rw [Category.assoc, hκ2]⟩
    have hx : x = E.L.one (m ≫ pullback.snd (ι ≫ E₀.f) (Spec.map (CommRingCat.ofHom T₀.val.toRingHom))) := by
      apply hK R' _ x
      refine (locIso_sliceAt_iff E₀.L E.L (Spec.map (CommRingCat.ofHom T₀.val.toRingHom)) g₀ hg₀.w hom₀ hg₀ 𝓜₀ h₀ _ x).2 ?_
      refine (hKpt R' _ (pushAlong (Spec.map (CommRingCat.ofHom T₀.val.toRingHom)) g₀ hg₀.w _ x)).1 ⟨m ≫ pullback.fst (ι ≫ E₀.f) (Spec.map (CommRingCat.ofHom T₀.val.toRingHom)), ?_⟩
      show (m ≫ pullback.fst (ι ≫ E₀.f) (Spec.map (CommRingCat.ofHom T₀.val.toRingHom))) ≫ ι = (m ≫ κ) ≫ g₀
      rw [Category.assoc, Category.assoc, hκ1]
    calc m ≫ κ = x.1 := rfl
      _ = (E.L.one (m ≫ pullback.snd (ι ≫ E₀.f) (Spec.map (CommRingCat.ofHom T₀.val.toRingHom)))).1 := by rw [hx]
      _ = m ≫ (E.L.one (pullback.snd (ι ≫ E₀.f) (Spec.map (CommRingCat.ofHom T₀.val.toRingHom)))).1 :=
        (congrArg Subtype.val (E.L.one_natural (pullback.snd (ι ≫ E₀.f) (Spec.map (CommRingCat.ofHom T₀.val.toRingHom))) _ m rfl)).symm

  have hκ : κ = (E.L.one (pullback.snd (ι ≫ E₀.f) (Spec.map (CommRingCat.ofHom T₀.val.toRingHom)))).1 :=
    Scheme.Cover.hom_ext (pullback (ι ≫ E₀.f) (Spec.map (CommRingCat.ofHom T₀.val.toRingHom))).affineCover _ _ (fun j => key _ _)

  have hfac : (pullback.snd (ι ≫ E₀.f) (Spec.map (CommRingCat.ofHom T₀.val.toRingHom)) ≫ (Spec.map (CommRingCat.ofHom T₀.val.toRingHom))) ≫ (E₀.L.one (𝟙 _)).1 =
      pullback.fst (ι ≫ E₀.f) (Spec.map (CommRingCat.ofHom T₀.val.toRingHom)) ≫ ι := by
    rw [← hone₀, ← hκ1, hκ]
    exact (one_val_comp E₀.L E.L (Spec.map (CommRingCat.ofHom T₀.val.toRingHom)) g₀ hg₀.w hom₀ _).symm

  haveI : LocallyOfFinitePresentation ((E₀.L.one (𝟙 _)).1 ≫ E₀.f) := by rw [he₀]; infer_instance
  obtain ⟨T, hT, hle, aT, haT⟩ :=
    AlgebraicGeometry.exists_fg_subalgebra_comp_eq_pullback_fst_comp_of_comp_eq_of_locallyOfFinitePresentation
      T₀ hT₀ E₀.f ι (E₀.L.one (𝟙 _)).1 (pullback.snd (ι ≫ E₀.f) (Spec.map (CommRingCat.ofHom T₀.val.toRingHom)) ≫ (Spec.map (CommRingCat.ofHom T₀.val.toRingHom))) hfac

  have hbase : (Spec.map (CommRingCat.ofHom T₀.val.toRingHom)) =
      Spec.map (CommRingCat.ofHom T.val.toRingHom) ≫ (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hle).toRingHom)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; rfl
  obtain ⟨ET, h, hh, hlawh, hacth, -, -⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_levelIff (Subalgebra.inclusion hle).toRingHom E₀
  let g : E.A ⟶ ET.A :=
    hh.lift g₀ (E.f ≫ Spec.map (CommRingCat.ofHom T.val.toRingHom)) (by rw [hg₀.w, hbase, Category.assoc])
  have hg1 : g ≫ h = g₀ := hh.lift_fst _ _ _
  have hg2 : g ≫ ET.f = E.f ≫ Spec.map (CommRingCat.ofHom T.val.toRingHom) := hh.lift_snd _ _ _
  have hg : CategoryTheory.IsPullback g E.f ET.f (Spec.map (CommRingCat.ofHom T.val.toRingHom)) := by
    have big : CategoryTheory.IsPullback (g ≫ h) E.f E₀.f
        (Spec.map (CommRingCat.ofHom T.val.toRingHom) ≫ (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hle).toRingHom))) := by
      rw [hg1, ← hbase]; exact hg₀
    exact IsPullback.of_right big hg2 hh
  have homh : ∀ (X : Scheme.{0}) (t' : X ⟶ Spec (CommRingCat.of ↥T)) (P Q : SchemeHomOver t' ET.f),
      (ET.L.mul t' P Q).1 ≫ h =
        (E₀.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hle).toRingHom)))
          ⟨P.1 ≫ h, by rw [Category.assoc, hh.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ h, by rw [Category.assoc, hh.w, ← Category.assoc, Q.2]⟩).1 :=
    fun X t' P Q => hlawh t' P Q
  refine ⟨T, hT, hle, ET, g, hg, h, hh, hg1, ?_, ?_, hlawh, hacth, ?_⟩
  · intro X t' P Q
    apply hh.hom_ext
    · rw [Category.assoc, hg1, hlaw₀ t' P Q, hlawh]
      refine mul_val_congr E₀.L ?_ _ _ _ _ ?_ ?_
      · rw [Category.assoc, ← hbase]
      · simp only [Category.assoc, hg1]
      · simp only [Category.assoc, hg1]
    · conv_lhs => rw [Category.assoc, hg2, ← Category.assoc, (E.L.mul t' P Q).2]
      exact ((ET.L.mul (t' ≫ Spec.map (CommRingCat.ofHom T.val.toRingHom)) _ _).2).symm
  · intro x
    apply hh.hom_ext
    · rw [Category.assoc, hg1, hact₀, Category.assoc, hacth, ← Category.assoc, hg1]
    · rw [Category.assoc, hg2, ← Category.assoc, E.act_over, Category.assoc, ET.act_over, hg2]
  ·
    intro R' _ t x Hx
    have H₀ := (locIso_sliceAt_iff E₀.L ET.L (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hle).toRingHom)) h hh.w homh hh 𝓜₀ h₀ t x).1 Hx
    obtain ⟨k, hk⟩ := (hKpt R' _ (pushAlong (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hle).toRingHom)) h hh.w t x)).2 H₀
    have hk' : k ≫ ι = x.1 ≫ h := hk
    have hkf : k ≫ ι ≫ E₀.f = t ≫ (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hle).toRingHom)) := by
      rw [← Category.assoc, hk', Category.assoc, hh.w, ← Category.assoc, x.2]
    let m : Spec (CommRingCat.of R') ⟶ pullback (ι ≫ E₀.f) (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hle).toRingHom)) := pullback.lift k t hkf
    have hm1 : m ≫ pullback.fst (ι ≫ E₀.f) (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hle).toRingHom)) = k := pullback.lift_fst _ _ _
    have hmT : m ≫ aT = t ≫ (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hle).toRingHom)) := by
      calc m ≫ aT = (m ≫ aT) ≫ ((E₀.L.one (𝟙 _)).1 ≫ E₀.f) := by rw [he₀, Category.comp_id]
        _ = m ≫ (aT ≫ (E₀.L.one (𝟙 _)).1) ≫ E₀.f := by simp only [Category.assoc]
        _ = (m ≫ pullback.fst (ι ≫ E₀.f) (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hle).toRingHom))) ≫ ι ≫ E₀.f := by rw [haT]; simp only [Category.assoc]
        _ = t ≫ (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hle).toRingHom)) := by rw [hm1, hkf]
    have hxh : x.1 ≫ h = (E₀.L.one (t ≫ (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hle).toRingHom)))).1 := by
      have e1 : (m ≫ aT) ≫ (E₀.L.one (𝟙 _)).1 = x.1 ≫ h := by
        rw [Category.assoc, haT, ← Category.assoc, hm1, hk']
      rw [hone₀, ← hmT]
      exact e1.symm
    apply Subtype.ext
    apply hh.hom_ext
    · rw [hxh]
      exact (one_val_comp E₀.L ET.L (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hle).toRingHom)) h hh.w homh t).symm
    · rw [x.2, (ET.L.one t).2]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_extension_kernelTrivial_pullback
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_extension_kernelTrivial_pullback (solution)
