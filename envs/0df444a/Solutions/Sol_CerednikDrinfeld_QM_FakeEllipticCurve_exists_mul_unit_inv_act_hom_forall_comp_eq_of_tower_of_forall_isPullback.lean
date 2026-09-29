-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_mul_unit_inv_act_hom_forall_comp_eq_of_tower_of_forall_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/29827d1d-f681-58d2-8554-595488824ff2

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_mul_forall_coe_mul_comp_eq_lift_comp_of_tower_of_forall_isPullback
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_inv_act_forall_comp_eq_of_tower_of_forall_isPullback
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_section_forall_coe_one_comp_eq_of_tower_of_forall_isPullback
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_mul_assoc_comm_and_act_identities_of_forall_comp_eq_of_tower_of_forall_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_mul_unit_inv_act_hom_forall_comp_eq_of_tower_of_forall_isPullback
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.OModulePresheaf.moduleSectionsHomSub AlgebraicGeometry.OModulePresheaf.smulSections AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.familyFramesGradedModule.moduleBase AlgebraicGeometry.OModulePresheaf.FamilyFrames.module AlgebraicGeometry.OModulePresheaf.FamilyFrames.addCommGroup"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec"
p2m_attr_erase "simp" "TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.cechPushforward_obj AlgebraicGeometry.OModulePresheaf.Hom.coe_cechPushforward_app AlgebraicGeometry.OModulePresheaf.AffHom.coe_cechPushforward_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.internalHom.ofAffHom_apply AlgebraicGeometry.OModulePresheaf.internalHom.toAffHom_app AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec"

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open scoped TensorProduct Quaternion
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

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
    {r : ℕ}
    (Z : Scheme.{0}) (G : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) R)) [IsFinite G] (jz : ∀ n : ℕ, (E n).A ⟶ Z)
    (hZ :
      (∀ n, t n ≫ jz (n + 1) = jz n) ∧
      (∀ n, CategoryTheory.IsPullback (jz n) (E n).f (G ≫ ProjSpace.π R r) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1))))))) :
    ∃ (m : pullback (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ⟶ Z) (e : Spec (CommRingCat.of R) ⟶ Z) (ι : Z ⟶ Z) (act : ↥Λ → (Z ⟶ Z))
      (hm : m ≫ (G ≫ ProjSpace.π R r) = pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r)) (he : e ≫ (G ≫ ProjSpace.π R r) = 𝟙 _) (hι : ι ≫ (G ≫ ProjSpace.π R r) = (G ≫ ProjSpace.π R r))
      (act_over : ∀ x : ↥Λ, act x ≫ (G ≫ ProjSpace.π R r) = (G ≫ ProjSpace.π R r)),

      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of R)) (x y z : SchemeHomOver t' (G ≫ ProjSpace.π R r)),
        pullback.lift (pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ m) z.1
            (by rw [Category.assoc, hm, pullback.lift_fst_assoc, x.2, z.2]) ≫ m =
          pullback.lift x.1 (pullback.lift y.1 z.1 (y.2.trans z.2.symm) ≫ m)
            (by rw [Category.assoc, hm, pullback.lift_fst_assoc, y.2, x.2]) ≫ m) ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t' (G ≫ ProjSpace.π R r)),
        pullback.lift (t' ≫ e) x.1 (by rw [Category.assoc, he, Category.comp_id, x.2]) ≫ m = x.1) ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t' (G ≫ ProjSpace.π R r)),
        pullback.lift x.1 (t' ≫ e) (by rw [Category.assoc, he, Category.comp_id, x.2]) ≫ m = x.1) ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t' (G ≫ ProjSpace.π R r)),
        pullback.lift (x.1 ≫ ι) x.1 (by rw [Category.assoc, hι]) ≫ m = t' ≫ e) ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t' (G ≫ ProjSpace.π R r)),
        pullback.lift y.1 x.1 (y.2.trans x.2.symm) ≫ m = pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ m) ∧

      (∀ h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ, act ⟨1, h1⟩ = 𝟙 Z) ∧
      (∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ), act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = act y ≫ act x) ∧
      (∀ (x : ↥Λ) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t' (G ≫ ProjSpace.π R r)),
        pullback.lift (P.1 ≫ act x) (Q.1 ≫ act x) (by rw [Category.assoc, act_over, Category.assoc, act_over, P.2, Q.2]) ≫ m =
          (pullback.lift P.1 Q.1 (P.2.trans Q.2.symm) ≫ m) ≫ act x) ∧
      (∀ (x y : ↥Λ) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t' (G ≫ ProjSpace.π R r)),
        P.1 ≫ act (x + y) =
          pullback.lift (P.1 ≫ act x) (P.1 ≫ act y) (by rw [Category.assoc, act_over, Category.assoc, act_over]) ≫ m) ∧

      (∀ (n : ℕ) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1))))
        (P Q : SchemeHomOver t' (E n).f),
        ((E n).L.mul t' P Q).1 ≫ jz n =
          pullback.lift (P.1 ≫ jz n) (Q.1 ≫ jz n)
            (by simp only [Category.assoc]; rw [(hZ.2 n).w, ← Category.assoc, P.2, ← Category.assoc, Q.2]) ≫ m) ∧
      (∀ (n : ℕ) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1)))),
        ((E n).L.one t').1 ≫ jz n = (t' ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1))))) ≫ e) ∧
      (∀ (n : ℕ) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1))))
        (P : SchemeHomOver t' (E n).f),
        ((E n).L.inv t' P).1 ≫ jz n = (P.1 ≫ jz n) ≫ ι) ∧
      (∀ (n : ℕ) (x : ↥Λ), (E n).act x ≫ jz n = jz n ≫ act x) := by
  obtain ⟨m, hm, hmul⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.exists_mul_forall_coe_mul_comp_eq_lift_comp_of_tower_of_forall_isPullback hqq' hB Λ hΛ μ hμ star hstar R π hπ E t ht Z G jz hZ
  obtain ⟨ι, hι, act, act_over, hinv, hact⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.exists_inv_act_forall_comp_eq_of_tower_of_forall_isPullback hqq' hB Λ hΛ μ hμ star hstar R π hπ E t ht Z G jz hZ
  obtain ⟨e, he, hone⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.exists_section_forall_coe_one_comp_eq_of_tower_of_forall_isPullback hqq' hB Λ hΛ μ hμ star hstar R π hπ E t ht Z G jz hZ
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.mul_assoc_comm_and_act_identities_of_forall_comp_eq_of_tower_of_forall_isPullback hqq' hB Λ hΛ μ hμ star hstar R π hπ E t ht Z G jz hZ m hm e he ι hι act act_over hmul hone hinv hact
  exact ⟨m, e, ι, act, hm, he, hι, act_over, h1, h2, h3, h4, h5, h6, h7, h8, h9, hmul, hone, hinv, hact⟩

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_mul_unit_inv_act_hom_forall_comp_eq_of_tower_of_forall_isPullback
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_mul_unit_inv_act_hom_forall_comp_eq_of_tower_of_forall_isPullback (solution)
