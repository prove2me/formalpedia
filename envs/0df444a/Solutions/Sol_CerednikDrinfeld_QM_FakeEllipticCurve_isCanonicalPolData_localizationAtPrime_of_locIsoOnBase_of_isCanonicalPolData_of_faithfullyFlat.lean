-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.isCanonicalPolData_localizationAtPrime_of_locIsoOnBase_of_isCanonicalPolData_of_faithfullyFlat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/b0fe01e6-962c-5a86-a902-ac9c405625fb

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_pullback_of_comp_eq
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_of_pullback_of_faithfullyFlat_of_isSeparated
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_bijective_specIso_inv_comp_appTop_of_isPullback
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback
import Theorems.Thm_CerednikDrinfeld_QM_IsCanonicalPolData_of_locIsoOnBase
import Theorems.Thm_AlgebraicGeometry_Polarisation_KernelIsTwoTorsion_of_pullback_of_faithfullyFlat
import Theorems.Thm_AlgebraicGeometry_Polarisation_RosatiCompatible_of_pullback_of_faithfullyFlat
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_eq_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_comp_eq
import Theorems.Thm_AlgebraicGeometry_Polarisation_KernelTrivial_pullback_of_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_isCanonicalPolData_localizationAtPrime_of_locIsoOnBase_of_isCanonicalPolData_of_faithfullyFlat
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AdicCompletion.instIsLocalRingMaximalIdeal AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp"
p2m_attr_erase "instance" "DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.Scheme.Modules.exteriorPower_obj AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply"
p2m_attr_erase "simp" "IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst GoodReductionJacobian.prodInr_comp_prodFst GoodReductionJacobian.RelativeGroupLaw.prod_inv GoodReductionJacobian.prodInl_comp_prodSnd GoodReductionJacobian.prodInr_comp_prodSnd GoodReductionJacobian.prodInl_comp_prodFst GoodReductionJacobian.prodFstPt_prodPairPt GoodReductionJacobian.prodFst_coe GoodReductionJacobian.prodSndPt_prodPairPt GoodReductionJacobian.RelativeGroupLaw.prod_one GoodReductionJacobian.prodPairPt_coe GoodReductionJacobian.prodPairPt_prodFstPt_prodSndPt GoodReductionJacobian.prodFstPt_coe GoodReductionJacobian.RelativeGroupLaw.prod_mul GoodReductionJacobian.prodSndPt_coe GoodReductionJacobian.prodSnd_coe AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app"

set_option autoImplicit false

open scoped TensorProduct Quaternion
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

universe u v

noncomputable section

namespace E24DC

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

theorem one_val_congr (L : RelativeGroupLaw S f) {T : Scheme.{u}} {s s' : T ⟶ Spec (CommRingCat.of S)} (hs : s = s') :
    (L.one s).1 = (L.one s').1 := by
  subst hs; rfl

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

end Hom

end E24DC
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_isCanonicalPolData_localizationAtPrime_of_locIsoOnBase_of_isCanonicalPolData_of_faithfullyFlat.E24DC"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_isCanonicalPolData_localizationAtPrime_of_locIsoOnBase_of_isCanonicalPolData_of_faithfullyFlat.E24DC"

open E24DC in
theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (N : ℕ) (S : Type) [CommRing S] (E : FakeEllipticCurve Λ N S) (𝔭 : PrimeSpectrum S)
    (W : Type) [CommRing W] [Algebra S W] [Algebra (Localization.AtPrime 𝔭.asIdeal) W]
    [IsScalarTower S (Localization.AtPrime 𝔭.asIdeal) W] (hW : Module.FaithfullyFlat (Localization.AtPrime 𝔭.asIdeal) W)
    (L𝔭 : RelativeGroupLaw (Localization.AtPrime 𝔭.asIdeal) (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal))))))
    (hL𝔭 : (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of (Localization.AtPrime 𝔭.asIdeal)))
          (P Q : SchemeHomOver t' (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))))),
          (L𝔭.mul t' P Q).1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))) =
            (E.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal))))
              ⟨P.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))),
                by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
              ⟨Q.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))),
                by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1))
    (𝓛𝔭 : (pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal))))).Modules) (h𝓛𝔭 : Scheme.Modules.IsInvertible 𝓛𝔭)
    (LW : RelativeGroupLaw W (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S W)))))
    (hLW : (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of W))
          (P Q : SchemeHomOver t' (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S W))))),
          (LW.mul t' P Q).1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S W))) =
            (E.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S W)))
              ⟨P.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S W))),
                by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
              ⟨Q.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S W))),
                by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1))
    (𝓛W : (pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S W)))).Modules)
    (hdW : CerednikDrinfeld.QM.IsCanonicalPolData (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S W)))) LW
            (fun x : ↥Λ => pullback.lift (pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S W))) ≫ E.act x) (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S W))))
              (by rw [Category.assoc, E.act_over]; exact pullback.condition))
            (fun x => pullback.lift_snd _ _ _)
            star 𝓛W)
    (ρ : pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S W))) ⟶ pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))))
    (hρ₁ : ρ ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))) = pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S W))))
    (hρ₂ : ρ ≫ pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))) =
      pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S W))) ≫ Spec.map (CommRingCat.ofHom (algebraMap (Localization.AtPrime 𝔭.asIdeal) W)))
    (hcmp : LocIsoOnBase (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S W)))) ((Scheme.Modules.pullback ρ).obj 𝓛𝔭) 𝓛W) :
    CerednikDrinfeld.QM.IsCanonicalPolData (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal))))) L𝔭
            (fun x : ↥Λ => pullback.lift (pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))) ≫ E.act x) (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))))
              (by rw [Category.assoc, E.act_over]; exact pullback.condition))
            (fun x => pullback.lift_snd _ _ _)
            star 𝓛𝔭 := by
  classical

  let ι𝔭 : Spec (CommRingCat.of (Localization.AtPrime 𝔭.asIdeal)) ⟶ Spec (CommRingCat.of S) :=
    Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))
  let ιW : Spec (CommRingCat.of W) ⟶ Spec (CommRingCat.of S) := Spec.map (CommRingCat.ofHom (algebraMap S W))
  let ψ : Spec (CommRingCat.of W) ⟶ Spec (CommRingCat.of (Localization.AtPrime 𝔭.asIdeal)) :=
    Spec.map (CommRingCat.ofHom (algebraMap (Localization.AtPrime 𝔭.asIdeal) W))
  let f𝔭 := pullback.snd E.f ι𝔭
  let fW := pullback.snd E.f ιW
  let p𝔭 := pullback.fst E.f ι𝔭
  let pW := pullback.fst E.f ιW
  have hιW : Spec.map (CommRingCat.ofHom (algebraMap S W)) = ψ ≫ ι𝔭 := by
    rw [IsScalarTower.algebraMap_eq S (Localization.AtPrime 𝔭.asIdeal) W, CommRingCat.ofHom_comp, Spec.map_comp]
  haveI : Module.FaithfullyFlat (Localization.AtPrime 𝔭.asIdeal) W := hW

  have hρ : IsPullback ρ fW f𝔭 ψ := by
    have big : IsPullback (ρ ≫ p𝔭) fW E.f (ψ ≫ ι𝔭) := by
      rw [hρ₁, ← hιW]; exact IsPullback.of_hasPullback _ _
    exact IsPullback.of_right big hρ₂ (IsPullback.of_hasPullback E.f ι𝔭)
  have hw : ρ ≫ f𝔭 = fW ≫ ψ := hρ.w

  have hom : ∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of W)) (P Q : SchemeHomOver t' fW),
      (LW.mul t' P Q).1 ≫ ρ =
        (L𝔭.mul (t' ≫ ψ)
          ⟨P.1 ≫ ρ, by rw [Category.assoc, hw, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ ρ, by rw [Category.assoc, hw, ← Category.assoc, Q.2]⟩).1 := by
    intro T t' P Q
    apply pullback.hom_ext
    · rw [Category.assoc, hρ₁, hLW T t' P Q, hL𝔭 T (t' ≫ ψ)]
      refine mul_val_congr E.L ?_ _ _ _ _ ?_ ?_
      · show t' ≫ Spec.map _ = _
        rw [hιW, Category.assoc]
      · simp only [Category.assoc, hρ₁]
      · simp only [Category.assoc, hρ₁]
    · trans t' ≫ ψ
      · change ((LW.mul t' P Q).1 ≫ ρ) ≫ f𝔭 = t' ≫ ψ
        rw [Category.assoc, hw, ← Category.assoc, (LW.mul t' P Q).2]
      · exact ((L𝔭.mul (t' ≫ ψ) _ _).2).symm

  have hact : ∀ x : ↥Λ,
      pullback.lift (pW ≫ E.act x) fW (by rw [Category.assoc, E.act_over]; exact pullback.condition) ≫ ρ =
        ρ ≫ pullback.lift (p𝔭 ≫ E.act x) f𝔭 (by rw [Category.assoc, E.act_over]; exact pullback.condition) := by
    intro x
    apply pullback.hom_ext
    · rw [Category.assoc, hρ₁, pullback.lift_fst, Category.assoc, pullback.lift_fst, ← Category.assoc, hρ₁]
    · trans fW ≫ ψ
      · change (_ ≫ ρ) ≫ f𝔭 = fW ≫ ψ
        rw [Category.assoc, hw, ← Category.assoc, pullback.lift_snd]
      · change fW ≫ ψ = (ρ ≫ _) ≫ f𝔭
        rw [Category.assoc, pullback.lift_snd, hw]

  have hdW' := CerednikDrinfeld.QM.IsCanonicalPolData.of_locIsoOnBase fW LW
    (fun x : ↥Λ => pullback.lift (pW ≫ E.act x) fW (by rw [Category.assoc, E.act_over]; exact pullback.condition))
    (fun x => pullback.lift_snd _ _ _) star 𝓛W ((Scheme.Modules.pullback ρ).obj 𝓛𝔭) (h𝓛𝔭.pullback ρ)
    ((AlgebraicGeometry.Polarisation.LocIsoOnBase.equivalence fW).symm hcmp) hdW
  obtain ⟨-, hsymW, hK2W, hsqrtW, hposW, hrosW⟩ := hdW'

  have hA𝔭 : AbelianSchemePropertyBundle (Localization.AtPrime 𝔭.asIdeal) f𝔭 :=
    E.bundle.of_isPullback (IsPullback.of_hasPullback E.f ι𝔭)
  haveI : IsProper f𝔭 := hA𝔭.proper
  have hH0 : ∀ (T : Type) [CommRing T] [Algebra (Localization.AtPrime 𝔭.asIdeal) T],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (pullback.snd f𝔭 (Scheme.TwoAffineOpenCover.specMap (Localization.AtPrime 𝔭.asIdeal) T)) ⊤
      Function.Bijective (algebraMap T
        Γ(pullback f𝔭 (Scheme.TwoAffineOpenCover.specMap (Localization.AtPrime 𝔭.asIdeal) T), ⊤)) := by
    intro T _ _
    have hb := hA𝔭.bijective_specIso_inv_comp_appTop_of_isPullback (algebraMap (Localization.AtPrime 𝔭.asIdeal) T)
      (pullback.snd f𝔭 (Scheme.TwoAffineOpenCover.specMap (Localization.AtPrime 𝔭.asIdeal) T))
      (pullback.fst f𝔭 (Scheme.TwoAffineOpenCover.specMap (Localization.AtPrime 𝔭.asIdeal) T))
      (IsPullback.of_hasPullback _ _)
    convert hb using 2
    ext r
    rw [Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom]
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, Scheme.Hom.appTop,
      Scheme.Hom.app_eq_appLE]
    rfl
  refine ⟨h𝓛𝔭, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have hneg : negMor fW LW ≫ ρ = ρ ≫ negMor f𝔭 L𝔭 := negMor_comp L𝔭 LW ψ ρ hw hom
    have e : (Scheme.Modules.pullback (negMor fW LW)).obj ((Scheme.Modules.pullback ρ).obj 𝓛𝔭) ≅
        (Scheme.Modules.pullback ρ).obj ((Scheme.Modules.pullback (negMor f𝔭 L𝔭)).obj 𝓛𝔭) :=
      (Scheme.Modules.pullbackComp (negMor fW LW) ρ).app _ ≪≫ (Scheme.Modules.pullbackCongr hneg).app _ ≪≫
        ((Scheme.Modules.pullbackComp ρ (negMor f𝔭 L𝔭)).app _).symm
    have H : LocIsoOnBase fW ((Scheme.Modules.pullback ρ).obj ((Scheme.Modules.pullback (negMor f𝔭 L𝔭)).obj 𝓛𝔭))
        ((Scheme.Modules.pullback ρ).obj 𝓛𝔭) :=
      (AlgebraicGeometry.Polarisation.LocIsoOnBase.equivalence fW).trans (locIsoOnBase_of_iso _ e.symm) hsymW
    exact AlgebraicGeometry.Polarisation.LocIsoOnBase.of_pullback_of_faithfullyFlat_of_isSeparated W f𝔭 fW ρ hρ hH0
      _ _ (h𝓛𝔭.pullback _) h𝓛𝔭 H
  ·
    exact AlgebraicGeometry.Polarisation.KernelIsTwoTorsion.of_pullback_of_faithfullyFlat hρ L𝔭 hA𝔭 LW
      (fun t' P Q => hom _ t' P Q) 𝓛𝔭 h𝓛𝔭 hK2W
  ·
    obtain ⟨S', _instCR, _instAlg, hffW, H⟩ := hsqrtW
    letI : Algebra (Localization.AtPrime 𝔭.asIdeal) S' :=
      ((algebraMap W S').comp (algebraMap (Localization.AtPrime 𝔭.asIdeal) W)).toAlgebra
    haveI : IsScalarTower (Localization.AtPrime 𝔭.asIdeal) W S' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    haveI : Module.FaithfullyFlat W S' := hffW
    refine ⟨S', inferInstance, inferInstance, Module.FaithfullyFlat.trans (Localization.AtPrime 𝔭.asIdeal) W S', ?_⟩
    intro L'' hL''

    let σ𝔭 : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of (Localization.AtPrime 𝔭.asIdeal)) :=
      Spec.map (CommRingCat.ofHom (algebraMap (Localization.AtPrime 𝔭.asIdeal) S'))
    let σW : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of W) := Spec.map (CommRingCat.ofHom (algebraMap W S'))
    have hσ : Spec.map (CommRingCat.ofHom (algebraMap (Localization.AtPrime 𝔭.asIdeal) S')) = σW ≫ ψ := by
      rw [IsScalarTower.algebraMap_eq (Localization.AtPrime 𝔭.asIdeal) W S', CommRingCat.ofHom_comp, Spec.map_comp]
    let q𝔭 := pullback.fst f𝔭 σ𝔭
    let s𝔭 := pullback.snd f𝔭 σ𝔭
    let qW := pullback.fst fW σW
    let sW := pullback.snd fW σW

    have hlamc : q𝔭 ≫ f𝔭 = (s𝔭 ≫ σW) ≫ ψ := by rw [Category.assoc, ← hσ]; exact pullback.condition
    let lam := hρ.lift q𝔭 (s𝔭 ≫ σW) hlamc
    have hlam1 : lam ≫ ρ = q𝔭 := hρ.lift_fst _ _ _
    have hlam2 : lam ≫ fW = s𝔭 ≫ σW := hρ.lift_snd _ _ _
    let θ : pullback f𝔭 σ𝔭 ⟶ pullback fW σW := pullback.lift lam s𝔭 hlam2
    have hθ1 : θ ≫ qW = lam := pullback.lift_fst _ _ _
    have hθ2 : θ ≫ sW = s𝔭 := pullback.lift_snd _ _ _
    have hθρ : (θ ≫ qW) ≫ ρ = q𝔭 := by rw [hθ1, hlam1]
    have hid : Spec.map (CommRingCat.ofHom (RingHom.id S')) = 𝟙 (Spec (CommRingCat.of S')) := by
      rw [CommRingCat.ofHom_id]; exact Spec.map_id _

    have hcartlam : IsPullback lam s𝔭 fW σW := by
      have big : IsPullback (lam ≫ ρ) s𝔭 f𝔭 (σW ≫ ψ) := by
        rw [hlam1, ← hσ]; exact IsPullback.of_hasPullback _ _
      exact IsPullback.of_right big hlam2 hρ
    have hcart : IsPullback θ s𝔭 sW (Spec.map (CommRingCat.ofHom (RingHom.id S'))) := by
      rw [hid]
      have big : IsPullback (θ ≫ qW) s𝔭 fW (𝟙 _ ≫ σW) := by
        rw [hθ1, Category.id_comp]; exact hcartlam
      exact IsPullback.of_right big (by rw [hθ2, Category.comp_id]) (IsPullback.of_hasPullback _ _)
    have hθw : θ ≫ sW = s𝔭 ≫ Spec.map (CommRingCat.ofHom (RingHom.id S')) := hcart.w

    obtain ⟨𝓛₀W, hinv0, hKT0, hloc0⟩ := H (LW.baseChange σW)
      (fun T t' P Q => congrArg Subtype.val (RelativeGroupLaw.baseChangePointToBase_mul σW LW t' P Q))

    have hθρ' : θ ≫ qW ≫ ρ = q𝔭 := by rw [← Category.assoc]; exact hθρ
    have hbm : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of S')) (P' Q' : SchemeHomOver s sW),
        ((LW.baseChange σW).mul s P' Q').1 ≫ pullback.fst fW σW =
          (LW.mul (s ≫ σW) (RelativeGroupLaw.baseChangePointToBase σW P')
            (RelativeGroupLaw.baseChangePointToBase σW Q')).1 :=
      fun s P' Q' => congrArg Subtype.val (RelativeGroupLaw.baseChangePointToBase_mul σW LW s P' Q')
    have homθ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t s𝔭),
        (L''.mul t P Q).1 ≫ θ =
          ((LW.baseChange σW).mul (t ≫ Spec.map (CommRingCat.ofHom (RingHom.id S')))
            ⟨P.1 ≫ θ, by rw [Category.assoc, hθw, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ θ, by rw [Category.assoc, hθw, ← Category.assoc, Q.2]⟩).1 := by
      intro T t P Q
      apply pullback.hom_ext
      ·
        rw [hbm, Category.assoc, hθ1]
        apply hρ.hom_ext
        · rw [Category.assoc, hlam1, hL'' T t P Q, hom]
          refine mul_val_congr L𝔭 ?_ _ _ _ _ ?_ ?_
          · show t ≫ Spec.map _ = _
            rw [hσ, hid, Category.comp_id, Category.assoc]
          · simp only [RelativeGroupLaw.baseChangePointToBase_coe, Category.assoc]
            exact (congrArg (fun z => P.1 ≫ z) hθρ').symm
          · simp only [RelativeGroupLaw.baseChangePointToBase_coe, Category.assoc]
            exact (congrArg (fun z => Q.1 ≫ z) hθρ').symm
        · trans (t ≫ Spec.map (CommRingCat.ofHom (RingHom.id S'))) ≫ σW
          · rw [hid, Category.comp_id, Category.assoc, hlam2, ← Category.assoc, (L''.mul t P Q).2]
          · exact ((LW.mul _ _ _).2).symm
      · trans t ≫ Spec.map (CommRingCat.ofHom (RingHom.id S'))
        · rw [hid, Category.comp_id, Category.assoc, hθ2]
          exact (L''.mul t P Q).2
        · exact (((LW.baseChange σW).mul _ _ _).2).symm

    refine ⟨(Scheme.Modules.pullback θ).obj 𝓛₀W, hinv0.pullback θ, ?_, ?_⟩
    · exact AlgebraicGeometry.Polarisation.KernelTrivial.pullback_of_isPullback (RingHom.id S') hcart
        (LW.baseChange σW) L'' homθ 𝓛₀W hinv0 hKT0
    · have H1 := LocIsoOnBase.pullback_of_comp_eq s𝔭 θ (Spec.map (CommRingCat.ofHom (RingHom.id S'))) hθw hloc0
      have hneg : negMor s𝔭 L'' ≫ θ = θ ≫ negMor sW (LW.baseChange σW) :=
        negMor_comp (LW.baseChange σW) L'' (Spec.map (CommRingCat.ofHom (RingHom.id S'))) θ hθw
          (fun T t P Q => homθ t P Q)
      have iso1 : (Scheme.Modules.pullback θ).obj ((Scheme.Modules.pullback qW).obj ((Scheme.Modules.pullback ρ).obj 𝓛𝔭)) ≅
          (Scheme.Modules.pullback q𝔭).obj 𝓛𝔭 :=
        (Scheme.Modules.pullbackComp θ qW).app _ ≪≫ (Scheme.Modules.pullbackComp (θ ≫ qW) ρ).app _ ≪≫
          (Scheme.Modules.pullbackCongr hθρ).app _
      have iso3 : (Scheme.Modules.pullback θ).obj ((Scheme.Modules.pullback (negMor sW (LW.baseChange σW))).obj 𝓛₀W) ≅
          (Scheme.Modules.pullback (negMor s𝔭 L'')).obj ((Scheme.Modules.pullback θ).obj 𝓛₀W) :=
        (Scheme.Modules.pullbackComp θ (negMor sW (LW.baseChange σW))).app _ ≪≫
          (Scheme.Modules.pullbackCongr hneg.symm).app _ ≪≫
          ((Scheme.Modules.pullbackComp (negMor s𝔭 L'') θ).app _).symm
      have iso2 : (Scheme.Modules.pullback θ).obj (𝓛₀W ⊗ (Scheme.Modules.pullback (negMor sW (LW.baseChange σW))).obj 𝓛₀W) ≅
          (Scheme.Modules.pullback θ).obj 𝓛₀W ⊗
            (Scheme.Modules.pullback (negMor s𝔭 L'')).obj ((Scheme.Modules.pullback θ).obj 𝓛₀W) :=
        Scheme.Modules.pullbackTensorObjIso θ _ _ ≪≫ whiskerLeftIso _ iso3
      have E2 := AlgebraicGeometry.Polarisation.LocIsoOnBase.equivalence s𝔭
      exact E2.trans (E2.trans (locIsoOnBase_of_iso _ iso1.symm) H1) (locIsoOnBase_of_iso _ iso2)
  ·
    intro k _ _ sk
    letI : Algebra (Localization.AtPrime 𝔭.asIdeal) k := sk.toAlgebra
    haveI : Nontrivial (k ⊗[Localization.AtPrime 𝔭.asIdeal] W) := inferInstance
    obtain ⟨m, hm⟩ := Ideal.exists_maximal (k ⊗[Localization.AtPrime 𝔭.asIdeal] W)
    letI := Ideal.Quotient.field m
    let K : Type := AlgebraicClosure ((k ⊗[Localization.AtPrime 𝔭.asIdeal] W) ⧸ m)
    let π : k ⊗[Localization.AtPrime 𝔭.asIdeal] W →+* K :=
      (algebraMap ((k ⊗[Localization.AtPrime 𝔭.asIdeal] W) ⧸ m) K).comp (Ideal.Quotient.mk m)
    let jk : k →+* K := π.comp Algebra.TensorProduct.includeLeftRingHom
    let sK : W →+* K := π.comp (Algebra.TensorProduct.includeRight (R := Localization.AtPrime 𝔭.asIdeal) (A := k) (B := W)).toRingHom
    have hcomp : sK.comp (algebraMap (Localization.AtPrime 𝔭.asIdeal) W) = jk.comp sk := by
      change (π.comp _).comp _ = (π.comp _).comp _
      rw [RingHom.comp_assoc, RingHom.comp_assoc, ← Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap]
      rfl
    have h1 := AlgebraicGeometry.Scheme.Modules.geomFibreH0Finrank_comp_eq f𝔭 𝓛𝔭 h𝓛𝔭 k K sk jk
    have h2 := AlgebraicGeometry.Scheme.Modules.geomFibreH0Finrank_eq_of_isPullback
      (algebraMap (Localization.AtPrime 𝔭.asIdeal) W) f𝔭 fW ρ hρ 𝓛𝔭 _ (Iso.refl _) K sK
    have h3 := hposW K sK
    rw [h2, hcomp, h1] at h3
    exact h3
  ·
    exact AlgebraicGeometry.Polarisation.RosatiCompatible.of_pullback_of_faithfullyFlat f𝔭 L𝔭 hA𝔭 fW LW ρ hρ
      (fun t' P Q => hom _ t' P Q) _ _ _ _ hact star 𝓛𝔭 h𝓛𝔭 hrosW

end S_CerednikDrinfeld_QM_FakeEllipticCurve_isCanonicalPolData_localizationAtPrime_of_locIsoOnBase_of_isCanonicalPolData_of_faithfullyFlat
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_isCanonicalPolData_localizationAtPrime_of_locIsoOnBase_of_isCanonicalPolData_of_faithfullyFlat (solution)
