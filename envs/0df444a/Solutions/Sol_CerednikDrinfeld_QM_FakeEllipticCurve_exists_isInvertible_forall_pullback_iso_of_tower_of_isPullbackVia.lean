-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_isInvertible_forall_pullback_iso_of_tower_of_isPullbackVia
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/bbfc2523-9bc7-5701-aff8-d5eea3deee1a

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isInvertible_pullback_iso_of_forall_thickening
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isInvertible_forall_pullback_iso_of_tower_of_isPullbackVia
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.OModulePresheaf.moduleSectionsHomSub AlgebraicGeometry.OModulePresheaf.smulSections AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.familyFramesGradedModule.moduleBase AlgebraicGeometry.OModulePresheaf.FamilyFrames.module AlgebraicGeometry.OModulePresheaf.FamilyFrames.addCommGroup AlgebraicGeometry.isClosedImmersion_adicThickeningι AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModulePreGlue AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies SheafOfModules.isIso_ihomModelToIhom PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.cechPushforward_obj AlgebraicGeometry.OModulePresheaf.Hom.coe_cechPushforward_app AlgebraicGeometry.OModulePresheaf.AffHom.coe_cechPushforward_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.internalHom.ofAffHom_apply AlgebraicGeometry.OModulePresheaf.internalHom.toAffHom_app AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.adicThickeningTransition_ι AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.glueComponent_glueMk AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.injEq AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.sizeOf_spec AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app"

set_option autoImplicit false

open scoped TensorProduct Quaternion
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

namespace P2mWs41C4

noncomputable def pbComp {X Y Z : Scheme.{0}} (u : X ⟶ Y) (v : Y ⟶ Z) (M : Z.Modules) :
    (Scheme.Modules.pullback (u ≫ v)).obj M ≅ (Scheme.Modules.pullback u).obj ((Scheme.Modules.pullback v).obj M) :=
  ((Scheme.Modules.pullbackComp u v).app M).symm

noncomputable def pbCongr {X Y : Scheme.{0}} {u v : X ⟶ Y} (h : u = v) (M : Y.Modules) :
    (Scheme.Modules.pullback u).obj M ≅ (Scheme.Modules.pullback v).obj M :=
  (Scheme.Modules.pullbackCongr h).app M

noncomputable def pbId {X : Scheme.{0}} (M : X.Modules) : (Scheme.Modules.pullback (𝟙 X)).obj M ≅ M :=
  (Scheme.Modules.pullbackId X).app M

end P2mWs41C4

open P2mWs41C4 in
theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]

    (π : ∀ n : ℕ, (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1 + 1)) →+* (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1)))
    (hπ : ∀ n, (π n).comp (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1 + 1))) =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1)))

    (E : ∀ n : ℕ, FakeEllipticCurve Λ 1 (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1)))
    (t : ∀ n : ℕ, (E n).A ⟶ (E (n + 1)).A)
    (ht : ∀ n, FakeEllipticCurve.IsPullbackVia (π n) (E (n + 1)) (E n) (t n))

    (𝓛 : ∀ n : ℕ, (E n).A.Modules)
    (hinv : ∀ n, Scheme.Modules.IsInvertible (𝓛 n))
    (hcompat : ∀ n, Nonempty ((Scheme.Modules.pullback (t n)).obj (𝓛 (n + 1)) ≅ 𝓛 n))
    (ER : FakeEllipticCurve Λ 1 R) (j : ∀ n : ℕ, (E n).A ⟶ ER.A)
    (hj : ∀ n, FakeEllipticCurve.IsPullbackVia (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1))) ER (E n) (j n))
    (hjt : ∀ n, t n ≫ j (n + 1) = j n) :
    ∃ 𝓜 : ER.A.Modules, Scheme.Modules.IsInvertible 𝓜 ∧
      ∀ n, Nonempty ((Scheme.Modules.pullback (j n)).obj 𝓜 ≅ 𝓛 n) := by
  classical

  have sq : ∀ n, IsPullback (j n) (E n).f ER.f
      (Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1))))) := fun n => (hj n).1
  have hRR : Spec.map (CommRingCat.ofHom (algebraMap R R)) = 𝟙 (Spec (CommRingCat.of R)) := by
    rw [show algebraMap R R = RingHom.id R from RingHom.ext fun _ => rfl, CommRingCat.ofHom_id]
    exact (Scheme.Spec).map_id _
  haveI : IsIso (Spec.map (CommRingCat.ofHom (algebraMap R R))) := by rw [hRR]; infer_instance
  have sqR : IsPullback (𝟙 ER.A) ER.f ER.f (Spec.map (CommRingCat.ofHom (algebraMap R R))) :=
    IsPullback.of_horiz_isIso ⟨by rw [hRR, Category.id_comp, Category.comp_id]⟩

  let e : ∀ n, (E n).A ≅ pullback ER.f (Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1))))) :=
    fun n => (sq n).isoPullback
  let eR : ER.A ≅ pullback ER.f (Spec.map (CommRingCat.ofHom (algebraMap R R))) := sqR.isoPullback

  let j' : ∀ n, pullback ER.f (Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1))))) ⟶
      pullback ER.f (Spec.map (CommRingCat.ofHom (algebraMap R R))) := fun n => (e n).inv ≫ j n ≫ eR.hom
  let t' : ∀ n, pullback ER.f (Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1))))) ⟶
      pullback ER.f (Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1 + 1))))) := fun n => (e n).inv ≫ t n ≫ (e (n + 1)).hom
  have hj₁ : ∀ n, j' n ≫ pullback.fst ER.f (Spec.map (CommRingCat.ofHom (algebraMap R R))) =
      pullback.fst ER.f (Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1))))) := by
    intro n
    simp only [j', eR, e, Category.assoc, IsPullback.isoPullback_hom_fst, Category.comp_id, IsPullback.isoPullback_inv_fst]
  have hj₂ : ∀ n, j' n ≫ pullback.snd ER.f (Spec.map (CommRingCat.ofHom (algebraMap R R))) =
      pullback.snd ER.f (Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1))))) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1)))) := by
    intro n
    simp only [j', eR, e, Category.assoc, IsPullback.isoPullback_hom_snd]
    rw [(sq n).w, IsPullback.isoPullback_inv_snd_assoc]
  have ht₁ : ∀ n, t' n ≫ pullback.fst ER.f (Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1 + 1))))) =
      pullback.fst ER.f (Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1))))) := by
    intro n
    simp only [t', e, Category.assoc, IsPullback.isoPullback_hom_fst, hjt, IsPullback.isoPullback_inv_fst]
  have ht' : ∀ n, t' n ≫ j' (n + 1) = j' n := by
    intro n
    simp only [t', j', Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc (t n) (j (n + 1)), hjt n]

  let 𝓛' : ∀ n, (pullback ER.f (Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1)))))).Modules :=
    fun n => (Scheme.Modules.pullback (e n).inv).obj (𝓛 n)
  have hinv' : ∀ n, Scheme.Modules.IsInvertible (𝓛' n) := fun n => (hinv n).pullback _
  have hcompat' : ∀ n, Nonempty ((Scheme.Modules.pullback (t' n)).obj (𝓛' (n + 1)) ≅ 𝓛' n) := by
    intro n
    obtain ⟨c⟩ := hcompat n
    have hcomp : ((e n).inv ≫ t n ≫ (e (n + 1)).hom) ≫ (e (n + 1)).inv = (e n).inv ≫ t n := by
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact ⟨(pbComp _ _ _).symm ≪≫ pbCongr hcomp _ ≪≫ pbComp _ _ _ ≪≫ (Scheme.Modules.pullback (e n).inv).mapIso c⟩

  obtain ⟨𝓛R, h𝓛R, hk⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_isInvertible_pullback_iso_of_forall_thickening
      hqq' hB Λ hΛ μ hμ star hstar 1 R ER R j' hj₁ hj₂ t' ht₁ ht' 𝓛' hinv' hcompat'

  refine ⟨(Scheme.Modules.pullback eR.hom).obj 𝓛R, h𝓛R.pullback _, fun n => ?_⟩
  obtain ⟨c⟩ := hk n
  have hconj : j n ≫ eR.hom = (e n).hom ≫ j' n := by
    simp only [j', Iso.hom_inv_id_assoc]
  have hid : (e n).hom ≫ (e n).inv = 𝟙 _ := (e n).hom_inv_id
  exact ⟨(pbComp _ _ _).symm ≪≫ pbCongr hconj _ ≪≫ pbComp _ _ _ ≪≫ (Scheme.Modules.pullback (e n).hom).mapIso c ≪≫
    (pbComp _ _ _).symm ≪≫ pbCongr hid _ ≪≫ pbId _⟩

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isInvertible_forall_pullback_iso_of_tower_of_isPullbackVia
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isInvertible_forall_pullback_iso_of_tower_of_isPullbackVia (solution)
