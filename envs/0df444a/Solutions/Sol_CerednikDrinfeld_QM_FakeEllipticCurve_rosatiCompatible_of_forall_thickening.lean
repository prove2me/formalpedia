-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.rosatiCompatible_of_forall_thickening
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/9b25fcdf-7d29-5a7e-bcb3-9f62de59e76e

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawProd
import Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_mumfordBundle_pullback_iso_pullback_mumfordBundle_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_pullback_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_of_forall_nonempty_pullback_thickening_iso_of_isProper
import Theorems.Thm_AlgebraicGeometry_Polarisation_locIsoOnBase_iff_nonempty_iso_of_isLocalRing
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_bijective_algebraMap_sections_pullback
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_prodStr_commRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_rosatiCompatible_of_forall_thickening
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback AlgebraicGeometry.isClosedImmersion_adicThickeningι AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.OModulePresheaf.moduleSectionsHomSub AlgebraicGeometry.OModulePresheaf.smulSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.adicThickeningTransition_ι AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.OModulePresheaf.internalHom.ofAffHom_apply AlgebraicGeometry.OModulePresheaf.internalHom.toAffHom_app AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.Scheme.Modules.exteriorPower_obj AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply"

set_option autoImplicit false

open scoped TensorProduct Quaternion
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

noncomputable section

namespace Ws23KP

theorem mul_coe_congr {S : Type} [CommRing S] {A Z : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    {b₁ b₂ : Z ⟶ Spec (CommRingCat.of S)} (hb : b₁ = b₂)
    (P Q : SchemeHomOver b₁ f) (P' Q' : SchemeHomOver b₂ f) (hP : P.1 = P'.1) (hQ : Q.1 = Q'.1) :
    (L.mul b₁ P Q).1 = (L.mul b₂ P' Q').1 := by
  subst hb
  obtain ⟨p, hp⟩ := P; obtain ⟨p', hp'⟩ := P'; obtain ⟨q, hq⟩ := Q; obtain ⟨q', hq'⟩ := Q'
  simp only at hP hQ
  subst hP; subst hQ
  rfl

theorem locIso_of_iso {S' : Type} [CommRing S'] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of S'))
    {M M' : X.Modules} (e : M ≅ M') : LocIsoOnBase p M M' :=
  fun _ => ⟨⊤, trivial, ⟨(Scheme.Modules.pullback _).mapIso e⟩⟩

def pullbackInvIso {X Y : Scheme.{0}} (ρ : X ⟶ Y) [IsIso ρ] (M : Y.Modules) :
    (Scheme.Modules.pullback (inv ρ)).obj ((Scheme.Modules.pullback ρ).obj M) ≅ M :=
  (Scheme.Modules.pullbackComp (inv ρ) ρ).app M ≪≫ (Scheme.Modules.pullbackCongr (IsIso.inv_hom_id ρ)).app M ≪≫
    (Scheme.Modules.pullbackId Y).app M

theorem specMap_id (R'' : Type) [CommRing R''] :
    Spec.map (CommRingCat.ofHom (RingHom.id R'')) = 𝟙 (Spec (CommRingCat.of R'')) := by
  rw [CommRingCat.ofHom_id]
  exact Scheme.Spec.map_id _

theorem isPullback_of_isIso_specMap_id {R'' : Type} [CommRing R''] {X Y : Scheme.{0}} (ρ : X ⟶ Y) [IsIso ρ]
    (p : X ⟶ Spec (CommRingCat.of R'')) (q : Y ⟶ Spec (CommRingCat.of R'')) (h : ρ ≫ q = p) :
    IsPullback ρ p q (Spec.map (CommRingCat.ofHom (RingHom.id R''))) := by
  rw [specMap_id]
  exact IsPullback.of_horiz_isIso ⟨by rw [h, Category.comp_id]⟩

theorem isInvertible_mumfordBundle {S' : Type} [CommRing S'] {A' : Scheme.{0}} (g : A' ⟶ Spec (CommRingCat.of S'))
    (L₀ : RelativeGroupLaw S' g) (𝓜 : A'.Modules) (h𝓜 : Scheme.Modules.IsInvertible 𝓜) :
    Scheme.Modules.IsInvertible (mumfordBundle g L₀ 𝓜) := by
  have hd := (AlgebraicGeometry.Scheme.Modules.IsInvertible.dual_monoidalV2 h𝓜).1
  unfold mumfordBundle
  exact (h𝓜.pullback _).tensor_monoidalV2 ((hd.pullback _).tensor_monoidalV2 (hd.pullback _))

section Square

variable {S R R' : Type} [CommRing S] [CommRing R] [CommRing R']
  {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
  (σ : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)) (σ' : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of S))
  (φ : R →+* R') (hπ : Spec.map (CommRingCat.ofHom φ) ≫ σ = σ')
  (j : pullback f σ' ⟶ pullback f σ)
  (hj₁ : j ≫ pullback.fst f σ = pullback.fst f σ')
  (hj₂ : j ≫ pullback.snd f σ = pullback.snd f σ' ≫ Spec.map (CommRingCat.ofHom φ))
  (L' : RelativeGroupLaw R (pullback.snd f σ))
  (hL' : ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t (pullback.snd f σ)),
      (L'.mul t P Q).1 ≫ pullback.fst f σ =
        (L.mul (t ≫ σ)
          ⟨P.1 ≫ pullback.fst f σ, by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ pullback.fst f σ, by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1)
  (Lk : RelativeGroupLaw R' (pullback.snd f σ'))
  (hLk : ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of R')) (P Q : SchemeHomOver t (pullback.snd f σ')),
      (Lk.mul t P Q).1 ≫ pullback.fst f σ' =
        (L.mul (t ≫ σ')
          ⟨P.1 ≫ pullback.fst f σ', by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ pullback.fst f σ', by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1)

include hπ hj₁ hj₂ in
theorem isPullback_j : IsPullback j (pullback.snd f σ') (pullback.snd f σ) (Spec.map (CommRingCat.ofHom φ)) := by
  have big : IsPullback (j ≫ pullback.fst f σ) (pullback.snd f σ') f (Spec.map (CommRingCat.ofHom φ) ≫ σ) := by
    rw [hj₁, hπ]
    exact IsPullback.of_hasPullback f σ'
  exact IsPullback.of_right big hj₂ (IsPullback.of_hasPullback f σ)

def pushPt {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R')} (y : SchemeHomOver t (pullback.snd f σ')) :
    SchemeHomOver (t ≫ Spec.map (CommRingCat.ofHom φ)) (pullback.snd f σ) :=
  ⟨y.1 ≫ j, by rw [Category.assoc, hj₂, ← Category.assoc, y.2]⟩

@[scoped simp] theorem pushPt_coe {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R')} (y : SchemeHomOver t (pullback.snd f σ')) :
    (pushPt σ σ' φ j hj₂ y).1 = y.1 ≫ j := rfl

include hπ hj₁ in

def liftPt {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R')}
    (x : SchemeHomOver (t ≫ Spec.map (CommRingCat.ofHom φ)) (pullback.snd f σ)) :
    SchemeHomOver t (pullback.snd f σ') :=
  ⟨(isPullback_j σ σ' φ hπ j hj₁ hj₂).lift x.1 t x.2, IsPullback.lift_snd _ _ _ _⟩

include hπ hj₁ in
theorem liftPt_comp_j {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R')}
    (x : SchemeHomOver (t ≫ Spec.map (CommRingCat.ofHom φ)) (pullback.snd f σ)) :
    (liftPt σ σ' φ hπ j hj₁ hj₂ x).1 ≫ j = x.1 :=
  IsPullback.lift_fst _ _ _ _

include hπ hj₁ in
theorem pushPt_liftPt {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R')}
    (x : SchemeHomOver (t ≫ Spec.map (CommRingCat.ofHom φ)) (pullback.snd f σ)) :
    pushPt σ σ' φ j hj₂ (liftPt σ σ' φ hπ j hj₁ hj₂ x) = x :=
  Subtype.ext (liftPt_comp_j σ σ' φ hπ j hj₁ hj₂ x)

include hπ hj₁ in

theorem pushPt_injective {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R')} :
    Function.Injective (pushPt σ σ' φ j hj₂ (t := t)) := by
  intro y y' h
  have h1 : y.1 ≫ j = y'.1 ≫ j := congrArg Subtype.val h
  apply Subtype.ext
  exact (isPullback_j σ σ' φ hπ j hj₁ hj₂).hom_ext h1 (by rw [y.2, y'.2])

include hπ hj₁ in
theorem liftPt_pushPt {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R')} (y : SchemeHomOver t (pullback.snd f σ')) :
    liftPt σ σ' φ hπ j hj₁ hj₂ (pushPt σ σ' φ j hj₂ y) = y :=
  pushPt_injective σ σ' φ hπ j hj₁ hj₂ (pushPt_liftPt σ σ' φ hπ j hj₁ hj₂ _)

include hπ hj₁ hj₂ hL' hLk in
theorem mul_comp_j {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R')) (P Q : SchemeHomOver t (pullback.snd f σ')) :
    (Lk.mul t P Q).1 ≫ j =
      (L'.mul (t ≫ Spec.map (CommRingCat.ofHom φ))
        ⟨P.1 ≫ j, by rw [Category.assoc, hj₂, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ j, by rw [Category.assoc, hj₂, ← Category.assoc, Q.2]⟩).1 := by
  apply pullback.hom_ext
  · rw [Category.assoc, hj₁, hLk T t P Q, hL' T _ _ _]
    exact mul_coe_congr L (by rw [Category.assoc, hπ]) _ _ _ _
      (by show P.1 ≫ pullback.fst f σ' = (P.1 ≫ j) ≫ pullback.fst f σ; rw [Category.assoc, hj₁])
      (by show Q.1 ≫ pullback.fst f σ' = (Q.1 ≫ j) ≫ pullback.fst f σ; rw [Category.assoc, hj₁])
  · trans t ≫ Spec.map (CommRingCat.ofHom φ)
    · rw [Category.assoc, hj₂, ← Category.assoc, (Lk.mul t P Q).2]
    · exact ((L'.mul (t ≫ Spec.map (CommRingCat.ofHom φ)) _ _).2).symm

include hπ hj₁ hj₂ hL' hLk in

theorem pushPt_mul {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R')) (P Q : SchemeHomOver t (pullback.snd f σ')) :
    pushPt σ σ' φ j hj₂ (Lk.mul t P Q) = L'.mul _ (pushPt σ σ' φ j hj₂ P) (pushPt σ σ' φ j hj₂ Q) :=
  Subtype.ext (mul_comp_j L σ σ' φ hπ j hj₁ hj₂ L' hL' Lk hLk t P Q)

include hπ hj₁ hj₂ hL' hLk in
theorem pushPt_one {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R')) :
    pushPt σ σ' φ j hj₂ (Lk.one t) = L'.one _ := by
  letI : Group (SchemeHomOver t (pullback.snd f σ')) := Lk.pointGroup t
  letI : Group (SchemeHomOver (t ≫ Spec.map (CommRingCat.ofHom φ)) (pullback.snd f σ)) := L'.pointGroup _
  let ψ : SchemeHomOver t (pullback.snd f σ') →* SchemeHomOver (t ≫ Spec.map (CommRingCat.ofHom φ)) (pullback.snd f σ) :=
    MonoidHom.mk' (pushPt σ σ' φ j hj₂) (pushPt_mul L σ σ' φ hπ j hj₁ hj₂ L' hL' Lk hLk t)
  exact map_one ψ

include hπ hj₁ hj₂ hL' hLk in
theorem one_comp_j {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R')) :
    (Lk.one t).1 ≫ j = (L'.one (t ≫ Spec.map (CommRingCat.ofHom φ))).1 :=
  congrArg Subtype.val (pushPt_one L σ σ' φ hπ j hj₁ hj₂ L' hL' Lk hLk t)

include hπ hj₁ hj₂ hL' hLk in
theorem eq_one_iff {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R')) (y : SchemeHomOver t (pullback.snd f σ')) :
    pushPt σ σ' φ j hj₂ y = L'.one _ ↔ y = Lk.one t := by
  rw [← pushPt_one L σ σ' φ hπ j hj₁ hj₂ L' hL' Lk hLk t]
  exact (pushPt_injective σ σ' φ hπ j hj₁ hj₂).eq_iff

include hπ hj₁ hj₂ hL' hLk in
theorem mul_self_eq_one_iff {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R')) (y : SchemeHomOver t (pullback.snd f σ')) :
    L'.mul _ (pushPt σ σ' φ j hj₂ y) (pushPt σ σ' φ j hj₂ y) = L'.one _ ↔ Lk.mul t y y = Lk.one t := by
  rw [← pushPt_mul L σ σ' φ hπ j hj₁ hj₂ L' hL' Lk hLk, ← pushPt_one L σ σ' φ hπ j hj₁ hj₂ L' hL' Lk hLk t]
  exact (pushPt_injective σ σ' φ hπ j hj₁ hj₂).eq_iff

include hπ hj₁ hj₂ hL' hLk in
theorem locIso_sliceAt_iff (𝓜 : (pullback f σ).Modules) (h𝓜 : Scheme.Modules.IsInvertible 𝓜)
    {R'' : Type} [CommRing R''] (t : Spec (CommRingCat.of R'') ⟶ Spec (CommRingCat.of R'))
    (y : SchemeHomOver t (pullback.snd f σ')) :
    LocIsoOnBase (pullback.snd (pullback.snd f σ) (t ≫ Spec.map (CommRingCat.ofHom φ)))
        ((Scheme.Modules.pullback (sliceAt (pullback.snd f σ) (pushPt σ σ' φ j hj₂ y))).obj
          (mumfordBundle (pullback.snd f σ) L' 𝓜))
        (𝟙_ ((pullback (pullback.snd f σ) (t ≫ Spec.map (CommRingCat.ofHom φ))).Modules)) ↔
      LocIsoOnBase (pullback.snd (pullback.snd f σ') t)
        ((Scheme.Modules.pullback (sliceAt (pullback.snd f σ') y)).obj
          (mumfordBundle (pullback.snd f σ') Lk ((Scheme.Modules.pullback j).obj 𝓜)))
        (𝟙_ ((pullback (pullback.snd f σ') t).Modules)) := by
  have hsq := isPullback_j σ σ' φ hπ j hj₁ hj₂

  obtain ⟨eΛ⟩ := AlgebraicGeometry.Polarisation.nonempty_mumfordBundle_pullback_iso_pullback_mumfordBundle_of_isPullback
    R R' φ (pullback.snd f σ) L' (pullback.snd f σ') Lk j hsq
    (fun t' P Q => mul_comp_j L σ σ' φ hπ j hj₁ hj₂ L' hL' Lk hLk t' P Q) 𝓜 h𝓜

  have big : IsPullback (pullback.fst (pullback.snd f σ') t ≫ j) (pullback.snd (pullback.snd f σ') t)
      (pullback.snd f σ) (t ≫ Spec.map (CommRingCat.ofHom φ)) :=
    IsPullback.paste_horiz (IsPullback.of_hasPullback (pullback.snd f σ') t) hsq
  let ρ : pullback (pullback.snd f σ') t ⟶ pullback (pullback.snd f σ) (t ≫ Spec.map (CommRingCat.ofHom φ)) :=
    big.isoPullback.hom
  have hρ₁ : ρ ≫ pullback.fst _ _ = pullback.fst (pullback.snd f σ') t ≫ j := big.isoPullback_hom_fst
  have hρ₂ : ρ ≫ pullback.snd _ _ = pullback.snd (pullback.snd f σ') t := big.isoPullback_hom_snd
  haveI : IsIso ρ := inferInstance
  have hρ : IsPullback ρ (pullback.snd (pullback.snd f σ') t) (pullback.snd (pullback.snd f σ) (t ≫ Spec.map (CommRingCat.ofHom φ)))
      (Spec.map (CommRingCat.ofHom (RingHom.id R''))) :=
    isPullback_of_isIso_specMap_id ρ _ _ hρ₂
  have hρ' : IsPullback (inv ρ) (pullback.snd (pullback.snd f σ) (t ≫ Spec.map (CommRingCat.ofHom φ))) (pullback.snd (pullback.snd f σ') t)
      (Spec.map (CommRingCat.ofHom (RingHom.id R''))) :=
    isPullback_of_isIso_specMap_id (inv ρ) _ _ (by rw [IsIso.inv_comp_eq, hρ₂])

  have hslice : sliceAt (pullback.snd f σ') y ≫
      pullback.lift (pullback.fst (pullback.snd f σ') (pullback.snd f σ') ≫ j) (pullback.snd (pullback.snd f σ') (pullback.snd f σ') ≫ j)
        (by rw [Category.assoc, Category.assoc, hsq.w, ← Category.assoc, pullback.condition, Category.assoc]) =
      ρ ≫ sliceAt (pullback.snd f σ) (pushPt σ σ' φ j hj₂ y) := by
    apply pullback.hom_ext
    · simp only [sliceAt, Category.assoc, pullback.lift_fst_assoc, pullback.lift_fst]
      exact hρ₁.symm
    · simp only [sliceAt, Category.assoc, pullback.lift_snd_assoc, pullback.lift_snd, pushPt_coe]
      rw [reassoc_of% hρ₂]

  have eA : (Scheme.Modules.pullback (sliceAt (pullback.snd f σ') y)).obj
        (mumfordBundle (pullback.snd f σ') Lk ((Scheme.Modules.pullback j).obj 𝓜)) ≅
      (Scheme.Modules.pullback ρ).obj ((Scheme.Modules.pullback (sliceAt (pullback.snd f σ) (pushPt σ σ' φ j hj₂ y))).obj
        (mumfordBundle (pullback.snd f σ) L' 𝓜)) :=
    (Scheme.Modules.pullback (sliceAt (pullback.snd f σ') y)).mapIso eΛ ≪≫
      (Scheme.Modules.pullbackComp (sliceAt (pullback.snd f σ') y) _).app _ ≪≫
      (Scheme.Modules.pullbackCongr hslice).app _ ≪≫
      ((Scheme.Modules.pullbackComp ρ (sliceAt (pullback.snd f σ) (pushPt σ σ' φ j hj₂ y))).app _).symm
  have eU : (Scheme.Modules.pullback ρ).obj (𝟙_ ((pullback (pullback.snd f σ) (t ≫ Spec.map (CommRingCat.ofHom φ))).Modules)) ≅
      𝟙_ ((pullback (pullback.snd f σ') t).Modules) :=
    Scheme.Modules.pullbackUnitIso ρ
  have E₁ := LocIsoOnBase.equivalence (pullback.snd (pullback.snd f σ') t)
  have E₂ := LocIsoOnBase.equivalence (pullback.snd (pullback.snd f σ) (t ≫ Spec.map (CommRingCat.ofHom φ)))
  constructor
  · intro h
    have h' := LocIsoOnBase.pullback_of_isPullback (RingHom.id R'') hρ h
    exact E₁.trans (locIso_of_iso _ eA) (E₁.trans h' (locIso_of_iso _ eU))
  · intro h
    have h1 : LocIsoOnBase (pullback.snd (pullback.snd f σ') t)
        ((Scheme.Modules.pullback ρ).obj ((Scheme.Modules.pullback (sliceAt (pullback.snd f σ) (pushPt σ σ' φ j hj₂ y))).obj
          (mumfordBundle (pullback.snd f σ) L' 𝓜)))
        ((Scheme.Modules.pullback ρ).obj (𝟙_ _)) :=
      E₁.trans (locIso_of_iso _ eA.symm) (E₁.trans h (locIso_of_iso _ eU.symm))
    have h2 := LocIsoOnBase.pullback_of_isPullback (RingHom.id R'') hρ' h1
    exact E₂.trans (locIso_of_iso _ (pullbackInvIso ρ _).symm) (E₂.trans h2 (locIso_of_iso _ (pullbackInvIso ρ _)))

omit L L' hL' Lk hLk hπ in
include hj₁ hj₂ in
theorem act_comp_j (a : A ⟶ A)
    (e : (pullback.fst f σ' ≫ a) ≫ f = pullback.snd f σ' ≫ σ') (e' : (pullback.fst f σ ≫ a) ≫ f = pullback.snd f σ ≫ σ) :
    pullback.lift (pullback.fst f σ' ≫ a) (pullback.snd f σ') e ≫ j =
      j ≫ pullback.lift (pullback.fst f σ ≫ a) (pullback.snd f σ) e' := by
  apply pullback.hom_ext
  · rw [Category.assoc, hj₁, pullback.lift_fst, Category.assoc, pullback.lift_fst, ← Category.assoc, hj₁]
  · rw [Category.assoc, hj₂, pullback.lift_snd_assoc, Category.assoc, pullback.lift_snd, hj₂]

omit φ hπ j hj₁ hj₂ Lk hLk in
theorem bundle_snd (hA : AbelianSchemePropertyBundle S f) : AbelianSchemePropertyBundle R (pullback.snd f σ) :=
  hA.of_isPullback (IsPullback.of_hasPullback f σ)

include hL' in
theorem isCommutative_of_compat (hc : L.IsCommutative) : L'.IsCommutative := by
  intro T t x y
  apply Subtype.ext
  apply pullback.hom_ext
  · rw [hL' T t x y, hL' T t y x, hc.mul_comm]
  · rw [(L'.mul t x y).2, (L'.mul t y x).2]

omit Lk hLk in

theorem compat_baseChange (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of R')) (P Q : SchemeHomOver t (pullback.snd f σ')) :
    ((L.baseChange σ').mul t P Q).1 ≫ pullback.fst f σ' =
      (L.mul (t ≫ σ')
        ⟨P.1 ≫ pullback.fst f σ', by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ pullback.fst f σ', by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1 :=
  congrArg Subtype.val (RelativeGroupLaw.baseChangePointToBase_mul σ' L t P Q)

end Square

end Ws23KP
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_rosatiCompatible_of_forall_thickening.Ws23KP"

namespace Ws23RPT

theorem isLocalRing_quot (R : Type) [CommRing R] [IsLocalRing R] (k : ℕ) :
    IsLocalRing (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1)) := by
  have hne : IsLocalRing.maximalIdeal R ^ (k + 1) ≠ ⊤ :=
    ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top (Ideal.pow_le_self (Nat.succ_ne_zero k))
  haveI : Nontrivial (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1)) := Ideal.Quotient.nontrivial_iff.mpr hne
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

end Ws23RPT
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_rosatiCompatible_of_forall_thickening.Ws23KP"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_rosatiCompatible_of_forall_thickening.Ws23KP"

theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (N : ℕ) (S : Type) [CommRing S] (E : FakeEllipticCurve Λ N S)
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [IsAlgClosed (IsLocalRing.ResidueField R)] [Algebra S R]
    (j : ∀ k : ℕ, pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))) ⟶ pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))))
    (hj₁ : ∀ k, j k ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))) = pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))))
    (hj₂ : ∀ k, j k ≫ pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))) =
      pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (k + 1)))))
    (L' : RelativeGroupLaw R (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R)))))
    (hL' : (∀ (T : Scheme) (t' : T ⟶ Spec (CommRingCat.of R))
            (P Q : SchemeHomOver t' (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))))),
            (L'.mul t' P Q).1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))) =
              (E.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S R))))
                ⟨P.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1))
    (𝓛 : (pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S R)))).Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (hk : ∀ (k : ℕ) (Lk : RelativeGroupLaw (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1)) (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))))),
        (∀ (T : Scheme) (t' : T ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))
            (P Q : SchemeHomOver t' (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))))),
            (Lk.mul t' P Q).1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))) =
              (E.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))))
                ⟨P.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
        RosatiCompatible (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1)))))) Lk
            ((Scheme.Modules.pullback (j k)).obj 𝓛)
            (fun x : ↥Λ => pullback.lift (pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))) ≫ E.act x) (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))))
              (by rw [Category.assoc, E.act_over]; exact pullback.condition))
            (fun x => pullback.lift_snd _ _ _)
            star) :
    RosatiCompatible (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R)))) L' 𝓛
            (fun x : ↥Λ => pullback.lift (pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))) ≫ E.act x) (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))))
              (by rw [Category.assoc, E.act_over]; exact pullback.condition))
            (fun x => pullback.lift_snd _ _ _)
            star := by
  classical
  haveI := E.bundle.proper
  intro b

  let σ : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S) := Spec.map (CommRingCat.ofHom (algebraMap S R))
  let fR : pullback E.f σ ⟶ Spec (CommRingCat.of R) := pullback.snd E.f σ
  let p : pullback fR fR ⟶ Spec (CommRingCat.of R) := pullback.fst fR fR ≫ fR
  have hAR : AbelianSchemePropertyBundle R fR := Ws23KP.bundle_snd σ E.bundle
  have hX : AbelianSchemePropertyBundle R p :=
    GoodReductionJacobian.AbelianSchemePropertyBundle.prodStr_commRing hAR hAR
  have hΛ : Scheme.Modules.IsInvertible (mumfordBundle fR L' 𝓛) := Ws23KP.isInvertible_mumfordBundle fR L' 𝓛 h𝓛

  rw [AlgebraicGeometry.Polarisation.locIsoOnBase_iff_nonempty_iso_of_isLocalRing]

  refine Scheme.Modules.IsInvertible.nonempty_iso_of_forall_nonempty_pullback_thickening_iso_of_isProper R p
    (fun k => pullback p (Scheme.TwoAffineOpenCover.specMap R (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))
    (fun k => pullback.snd _ _) (fun k => pullback.fst _ _) ?_ ?_ _ _ (hΛ.pullback _) (hΛ.pullback _) ?_
  ·
    intro k
    have e : Scheme.TwoAffineOpenCover.specMap R (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1)) =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (k + 1)))) := by
      show Spec.map _ = _
      rw [Ideal.Quotient.algebraMap_eq]
    rw [← e]
    exact IsPullback.of_hasPullback _ _
  ·
    intro k
    exact GoodReductionJacobian.AbelianSchemePropertyBundle.bijective_algebraMap_sections_pullback hX _
  ·
    intro k
    haveI := Ws23RPT.isLocalRing_quot R k

    let σ' : Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))) ⟶ Spec (CommRingCat.of S) :=
      Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))
    let π : Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))) ⟶ Spec (CommRingCat.of R) :=
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (k + 1))))
    let fk : pullback E.f σ' ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))) := pullback.snd E.f σ'
    have hπ : π ≫ σ = σ' := by
      show Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have hsq : IsPullback (j k) fk fR π := Ws23KP.isPullback_j σ σ' _ hπ (j k) (hj₁ k) (hj₂ k)

    let Lk := E.L.baseChange σ'
    have hLk := Ws23KP.compat_baseChange E.L σ'
    obtain ⟨e0⟩ := (AlgebraicGeometry.Polarisation.locIsoOnBase_iff_nonempty_iso_of_isLocalRing _ _ _).mp (hk k Lk hLk b)

    obtain ⟨eΛ⟩ := AlgebraicGeometry.Polarisation.nonempty_mumfordBundle_pullback_iso_pullback_mumfordBundle_of_isPullback
      R (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1)) (Ideal.Quotient.mk _) fR L' fk Lk (j k) hsq
      (fun t' P Q => Ws23KP.mul_comp_j E.L σ σ' _ hπ (j k) (hj₁ k) (hj₂ k) L' hL' Lk hLk t' P Q) 𝓛 h𝓛

    have e : Scheme.TwoAffineOpenCover.specMap R (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1)) = π := by
      show Spec.map _ = _
      rw [Ideal.Quotient.algebraMap_eq]
    let J := pullback.fst p (Scheme.TwoAffineOpenCover.specMap R (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1)))
    let qk := pullback.snd p (Scheme.TwoAffineOpenCover.specMap R (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1)))
    have w₁ : (J ≫ pullback.fst fR fR) ≫ fR = qk ≫ π := by
      rw [← e, Category.assoc]
      exact pullback.condition
    have w₂ : (J ≫ pullback.snd fR fR) ≫ fR = qk ≫ π := by
      rw [← e, Category.assoc, ← pullback.condition]
      exact pullback.condition
    obtain ⟨c, hc1, hc2⟩ : ∃ c : pullback p (Scheme.TwoAffineOpenCover.specMap R (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))) ⟶
        pullback fk fk,
        c ≫ pullback.fst fk fk ≫ j k = J ≫ pullback.fst fR fR ∧ c ≫ pullback.snd fk fk ≫ j k = J ≫ pullback.snd fR fR := by
      refine ⟨pullback.lift (hsq.lift _ _ w₁) (hsq.lift _ _ w₂) (by rw [hsq.lift_snd, hsq.lift_snd]), ?_, ?_⟩
      · rw [pullback.lift_fst_assoc, hsq.lift_fst]
      · rw [pullback.lift_snd_assoc, hsq.lift_fst]

    let ιR : ↥Λ → (pullback E.f σ ⟶ pullback E.f σ) := fun x =>
      pullback.lift (pullback.fst E.f σ ≫ E.act x) (pullback.snd E.f σ) (by rw [Category.assoc, E.act_over]; exact pullback.condition)
    let ιk : ↥Λ → (pullback E.f σ' ⟶ pullback E.f σ') := fun x =>
      pullback.lift (pullback.fst E.f σ' ≫ E.act x) (pullback.snd E.f σ') (by rw [Category.assoc, E.act_over]; exact pullback.condition)
    have hιR : ∀ x, ιR x ≫ fR = fR := fun x => pullback.lift_snd _ _ _
    have hιk : ∀ x, ιk x ≫ fk = fk := fun x => pullback.lift_snd _ _ _
    have hact : ∀ x, ιk x ≫ j k = j k ≫ ιR x := fun x =>
      Ws23KP.act_comp_j σ σ' _ (j k) (hj₁ k) (hj₂ k) (E.act x) _ _
    let sR : pullback fR fR ⟶ pullback fR fR :=
      pullback.lift (pullback.fst fR fR) (pullback.snd fR fR ≫ ιR b) (by rw [Category.assoc, hιR]; exact pullback.condition)
    let sR' : pullback fR fR ⟶ pullback fR fR :=
      pullback.lift (pullback.fst fR fR ≫ ιR (star b)) (pullback.snd fR fR) (by rw [Category.assoc, hιR]; exact pullback.condition)
    let sk : pullback fk fk ⟶ pullback fk fk :=
      pullback.lift (pullback.fst fk fk) (pullback.snd fk fk ≫ ιk b) (by rw [Category.assoc, hιk]; exact pullback.condition)
    let sk' : pullback fk fk ⟶ pullback fk fk :=
      pullback.lift (pullback.fst fk fk ≫ ιk (star b)) (pullback.snd fk fk) (by rw [Category.assoc, hιk]; exact pullback.condition)
    let jj : pullback fk fk ⟶ pullback fR fR :=
      pullback.lift (pullback.fst fk fk ≫ j k) (pullback.snd fk fk ≫ j k)
        (by rw [Category.assoc, Category.assoc, hsq.w, ← Category.assoc, pullback.condition, Category.assoc])

    have key₁ : J ≫ sR = c ≫ sk ≫ jj := by
      apply pullback.hom_ext
      · simp only [sR, sk, jj, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
        exact hc1.symm
      · simp only [sR, sk, jj, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
        rw [hact, reassoc_of% hc2]
    have key₂ : J ≫ sR' = c ≫ sk' ≫ jj := by
      apply pullback.hom_ext
      · simp only [sR', sk', jj, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
        rw [hact, reassoc_of% hc1]
      · simp only [sR', sk', jj, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
        exact hc2.symm

    let Λ' := mumfordBundle fR L' 𝓛
    let Λk := mumfordBundle fk Lk ((Scheme.Modules.pullback (j k)).obj 𝓛)
    refine ⟨(Scheme.Modules.pullbackComp J sR).app Λ' ≪≫ (Scheme.Modules.pullbackCongr key₁).app Λ' ≪≫
      ((Scheme.Modules.pullbackComp c (sk ≫ jj)).app Λ').symm ≪≫
      (Scheme.Modules.pullback c).mapIso
        (((Scheme.Modules.pullbackComp sk jj).app Λ').symm ≪≫ (Scheme.Modules.pullback sk).mapIso eΛ.symm ≪≫ e0 ≪≫
          (Scheme.Modules.pullback sk').mapIso eΛ ≪≫ (Scheme.Modules.pullbackComp sk' jj).app Λ') ≪≫
      (Scheme.Modules.pullbackComp c (sk' ≫ jj)).app Λ' ≪≫ (Scheme.Modules.pullbackCongr key₂.symm).app Λ' ≪≫
      ((Scheme.Modules.pullbackComp J sR').app Λ').symm⟩

end S_CerednikDrinfeld_QM_FakeEllipticCurve_rosatiCompatible_of_forall_thickening
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_rosatiCompatible_of_forall_thickening (solution)
