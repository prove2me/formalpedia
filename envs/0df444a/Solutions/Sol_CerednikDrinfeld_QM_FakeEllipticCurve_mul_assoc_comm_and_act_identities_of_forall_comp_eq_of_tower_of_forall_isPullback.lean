-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.mul_assoc_comm_and_act_identities_of_forall_comp_eq_of_tower_of_forall_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/de626e3e-eeb0-5bc5-bf3c-23a6e426bd62

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Theorems.Thm_AlgebraicGeometry_exists_hom_comp_eq_forall_pullback_fst_comp_eq_of_forall_truncation_of_isFinite_proj_of_isAdicComplete
import Theorems.Thm_AlgebraicGeometry_exists_isFinite_projSpace_pullback_of_isFinite_projSpace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_mul_assoc_comm_and_act_identities_of_forall_comp_eq_of_tower_of_forall_isPullback
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.OModulePresheaf.moduleSectionsHomSub AlgebraicGeometry.OModulePresheaf.smulSections AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.familyFramesGradedModule.moduleBase AlgebraicGeometry.OModulePresheaf.FamilyFrames.module AlgebraicGeometry.OModulePresheaf.FamilyFrames.addCommGroup"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec"
p2m_attr_erase "simp" "TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.cechPushforward_obj AlgebraicGeometry.OModulePresheaf.Hom.coe_cechPushforward_app AlgebraicGeometry.OModulePresheaf.AffHom.coe_cechPushforward_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.internalHom.ofAffHom_apply AlgebraicGeometry.OModulePresheaf.internalHom.toAffHom_app AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec"

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open scoped TensorProduct Quaternion
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

universe u

namespace IdentEngine

noncomputable abbrev tR (R : Type u) [CommRing R] (I : Ideal R) (n : ℕ) :
    Spec (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (n + 1 + 1))) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ _))))

theorem tR_sR (R : Type u) [CommRing R] (I : Ideal R)
    (sR : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ Spec (CommRingCat.of R))
    (hsR : ∀ n : ℕ, sR n = Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ I ^ (n + 1))))) (n : ℕ) :
    tR R I n ≫ sR (n + 1) = sR n := by
  rw [hsR, hsR, tR, ← Spec.map_comp]
  congr 1

noncomputable def trunc {R : Type u} [CommRing R] (I : Ideal R)
    (sR : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ Spec (CommRingCat.of R))
    (hsR : ∀ n : ℕ, sR n = Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ I ^ (n + 1)))))
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (n : ℕ) :
    pullback f (sR n) ⟶ pullback f (sR (n + 1)) :=
  pullback.lift (pullback.fst f (sR n)) (pullback.snd f (sR n) ≫ tR R I n)
    (by rw [Category.assoc, tR_sR R I sR hsR, pullback.condition])

theorem eq_of_forall_pullback_fst_truncation_comp_eq
    (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    (sR : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ Spec (CommRingCat.of R))
    (hsR : ∀ n : ℕ, sR n = Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ I ^ (n + 1)))))
    {W Z : Scheme.{u}} (w : W ⟶ Spec (CommRingCat.of R))
    (rW : ℕ) (GW : W ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (rW + 1)) R)) [IsFinite GW] (hGW : GW ≫ ProjSpace.π R rW = w)
    (f : Z ⟶ Spec (CommRingCat.of R))
    (rZ : ℕ) (GZ : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (rZ + 1)) R)) [IsFinite GZ] (hGZ : GZ ≫ ProjSpace.π R rZ = f)
    (φ₁ φ₂ : W ⟶ Z) (h₁ : φ₁ ≫ f = w) (h₂ : φ₂ ≫ f = w)
    (hn : ∀ n : ℕ, pullback.fst w (sR n) ≫ φ₁ = pullback.fst w (sR n) ≫ φ₂) :
    φ₁ = φ₂ := by
  let φ : ∀ n : ℕ, pullback w (sR n) ⟶ pullback f (sR n) := fun n =>
    pullback.lift (pullback.fst w (sR n) ≫ φ₁) (pullback.snd w (sR n))
      (by rw [Category.assoc, h₁, pullback.condition])
  obtain ⟨F, -, -, huniq⟩ :=
    AlgebraicGeometry.exists_hom_comp_eq_forall_pullback_fst_comp_eq_of_forall_truncation_of_isFinite_proj_of_isAdicComplete
      R I W w rW GW hGW Z f rZ GZ hGZ sR hsR (tR R I) (tR_sR R I sR hsR)
      (trunc I sR hsR w) (fun n => pullback.lift_fst _ _ _) (fun n => pullback.lift_snd _ _ _)
      (trunc I sR hsR f) (fun n => pullback.lift_fst _ _ _) (fun n => pullback.lift_snd _ _ _)
      φ (fun n => pullback.lift_snd _ _ _)
      (fun n => by
        apply pullback.hom_ext
        · simp only [Category.assoc, φ, trunc, pullback.lift_fst, pullback.lift_fst_assoc]
        · simp only [Category.assoc, φ, trunc, pullback.lift_snd, pullback.lift_snd_assoc])
  have e₁ : φ₁ = F := huniq φ₁ h₁ fun n => by simp only [φ, pullback.lift_fst]
  have e₂ : φ₂ = F := huniq φ₂ h₂ fun n => by simp only [φ, pullback.lift_fst, hn n]
  rw [e₁, e₂]

end IdentEngine

namespace IdentKit

noncomputable abbrev sRm (R : Type) [CommRing R] [IsLocalRing R] (n : ℕ) :
    Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1))) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1))))

theorem sRm_eq (R : Type) [CommRing R] [IsLocalRing R] (n : ℕ) :
    sRm R n = Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1)))) := rfl

end IdentKit

namespace IdentKit

variable {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
  {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}

theorem eq1 (E : ∀ n : ℕ, FakeEllipticCurve Λ 1 (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1)))
    {r : ℕ} (Z : Scheme.{0}) (G : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) R)) [IsFinite G]
    (jz : ∀ n : ℕ, (E n).A ⟶ Z)
    (hZ2 : ∀ n, IsPullback (jz n) (E n).f (G ≫ ProjSpace.π R r) (sRm R n))
    (φ₁ φ₂ : Z ⟶ Z) (h₁ : φ₁ ≫ (G ≫ ProjSpace.π R r) = G ≫ ProjSpace.π R r) (h₂ : φ₂ ≫ (G ≫ ProjSpace.π R r) = G ≫ ProjSpace.π R r)
    (hj : ∀ n, jz n ≫ φ₁ = jz n ≫ φ₂) : φ₁ = φ₂ := by
  refine IdentEngine.eq_of_forall_pullback_fst_truncation_comp_eq R (IsLocalRing.maximalIdeal R) (sRm R) (sRm_eq R)
    (G ≫ ProjSpace.π R r) r G rfl (G ≫ ProjSpace.π R r) r G rfl φ₁ φ₂ h₁ h₂ fun n => ?_
  have hX : pullback.fst (G ≫ ProjSpace.π R r) (sRm R n) ≫ (G ≫ ProjSpace.π R r) = pullback.snd _ _ ≫ sRm R n :=
    pullback.condition
  rw [← (hZ2 n).lift_fst _ _ hX, Category.assoc, Category.assoc, hj n]

theorem j2_cond (E : ∀ n : ℕ, FakeEllipticCurve Λ 1 (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1)))
    {r : ℕ} (Z : Scheme.{0}) (G : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) R))
    (jz : ∀ n : ℕ, (E n).A ⟶ Z)
    (hZ2 : ∀ n, IsPullback (jz n) (E n).f (G ≫ ProjSpace.π R r) (sRm R n)) (n : ℕ) :
    (pullback.fst (E n).f (E n).f ≫ jz n) ≫ (G ≫ ProjSpace.π R r) = (pullback.snd (E n).f (E n).f ≫ jz n) ≫ (G ≫ ProjSpace.π R r) := by
  rw [Category.assoc, Category.assoc, (hZ2 n).w, ← Category.assoc, ← Category.assoc, pullback.condition]

theorem eq2 (E : ∀ n : ℕ, FakeEllipticCurve Λ 1 (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1)))
    {r : ℕ} (Z : Scheme.{0}) (G : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) R)) [IsFinite G]
    (jz : ∀ n : ℕ, (E n).A ⟶ Z)
    (hZ2 : ∀ n, IsPullback (jz n) (E n).f (G ≫ ProjSpace.π R r) (sRm R n))
    (φ₁ φ₂ : pullback (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ⟶ Z)
    (h₁ : φ₁ ≫ (G ≫ ProjSpace.π R r) = pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r))
    (h₂ : φ₂ ≫ (G ≫ ProjSpace.π R r) = pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r))
    (hj : ∀ n, pullback.lift (pullback.fst (E n).f (E n).f ≫ jz n) (pullback.snd (E n).f (E n).f ≫ jz n) (j2_cond E Z G jz hZ2 n) ≫ φ₁ =
      pullback.lift (pullback.fst (E n).f (E n).f ≫ jz n) (pullback.snd (E n).f (E n).f ≫ jz n) (j2_cond E Z G jz hZ2 n) ≫ φ₂) :
    φ₁ = φ₂ := by
  obtain ⟨K, GP, hGPfin, hGP⟩ :=
    AlgebraicGeometry.exists_isFinite_projSpace_pullback_of_isFinite_projSpace
      (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) r G rfl r G rfl
  haveI := hGPfin
  refine IdentEngine.eq_of_forall_pullback_fst_truncation_comp_eq R (IsLocalRing.maximalIdeal R) (sRm R) (sRm_eq R)
    (pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r)) K GP hGP
    (G ≫ ProjSpace.π R r) r G rfl φ₁ φ₂ h₁ h₂ fun n => ?_
  set F := pullback.fst (pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r)) (sRm R n) with hF
  set τ := pullback.snd (pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r)) (sRm R n) with hτ
  have hX : (F ≫ pullback.fst _ _) ≫ (G ≫ ProjSpace.π R r) = τ ≫ sRm R n := by
    rw [Category.assoc]; exact pullback.condition
  have hY : (F ≫ pullback.snd _ _) ≫ (G ≫ ProjSpace.π R r) = τ ≫ sRm R n := by
    rw [Category.assoc, ← pullback.condition]; exact pullback.condition
  have hκ : F = pullback.lift ((hZ2 n).lift _ _ hX) ((hZ2 n).lift _ _ hY)
        (by rw [(hZ2 n).lift_snd, (hZ2 n).lift_snd]) ≫
      pullback.lift (pullback.fst (E n).f (E n).f ≫ jz n) (pullback.snd (E n).f (E n).f ≫ jz n) (j2_cond E Z G jz hZ2 n) := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, (hZ2 n).lift_fst]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, (hZ2 n).lift_fst]
  rw [hκ, Category.assoc, Category.assoc, hj n]

end IdentKit

namespace IdentKit

theorem comm_hom
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
      (∀ n, CategoryTheory.IsPullback (jz n) (E n).f (G ≫ ProjSpace.π R r) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1)))))))
    (m : pullback (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ⟶ Z) (hm : m ≫ (G ≫ ProjSpace.π R r) = pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r))
    (e : Spec (CommRingCat.of R) ⟶ Z) (he : e ≫ (G ≫ ProjSpace.π R r) = 𝟙 _)
    (ι : Z ⟶ Z) (hι : ι ≫ (G ≫ ProjSpace.π R r) = (G ≫ ProjSpace.π R r)) (act : ↥Λ → (Z ⟶ Z)) (act_over : ∀ x : ↥Λ, act x ≫ (G ≫ ProjSpace.π R r) = (G ≫ ProjSpace.π R r))
    (hmul : ∀ (n : ℕ) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1))))
        (P Q : SchemeHomOver t' (E n).f),
        ((E n).L.mul t' P Q).1 ≫ jz n =
          pullback.lift (P.1 ≫ jz n) (Q.1 ≫ jz n)
            (by simp only [Category.assoc]; rw [(hZ.2 n).w, ← Category.assoc, P.2, ← Category.assoc, Q.2]) ≫ m)
    (hone : ∀ (n : ℕ) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1)))),
        ((E n).L.one t').1 ≫ jz n = (t' ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1))))) ≫ e)
    (hinv : ∀ (n : ℕ) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1))))
        (P : SchemeHomOver t' (E n).f),
        ((E n).L.inv t' P).1 ≫ jz n = (P.1 ≫ jz n) ≫ ι)
    (hact : ∀ (n : ℕ) (x : ↥Λ), (E n).act x ≫ jz n = jz n ≫ act x) :
    pullback.lift (pullback.snd (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r)) (pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r))
        (pullback.condition).symm ≫ m = m := by

  obtain ⟨K, GP, hGPfin, hGP⟩ :=
    AlgebraicGeometry.exists_isFinite_projSpace_pullback_of_isFinite_projSpace
      (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) r G rfl r G rfl
  haveI := hGPfin
  refine IdentEngine.eq_of_forall_pullback_fst_truncation_comp_eq R (IsLocalRing.maximalIdeal R) (sRm R) (sRm_eq R)
    (pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r)) K GP hGP
    (G ≫ ProjSpace.π R r) r G rfl _ _ ?_ hm ?_
  · rw [Category.assoc, hm, pullback.lift_fst_assoc, pullback.condition]
  intro n

  set F := pullback.fst (pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r)) (sRm R n) with hF
  set τ := pullback.snd (pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r)) (sRm R n) with hτ
  have hX : (F ≫ pullback.fst _ _) ≫ (G ≫ ProjSpace.π R r) = τ ≫ sRm R n := by
    rw [Category.assoc]; exact pullback.condition
  have hY : (F ≫ pullback.snd _ _) ≫ (G ≫ ProjSpace.π R r) = τ ≫ sRm R n := by
    rw [Category.assoc, ← pullback.condition]; exact pullback.condition
  let P : SchemeHomOver τ (E n).f := ⟨(hZ.2 n).lift _ _ hX, (hZ.2 n).lift_snd _ _ hX⟩
  let Q : SchemeHomOver τ (E n).f := ⟨(hZ.2 n).lift _ _ hY, (hZ.2 n).lift_snd _ _ hY⟩
  have hP : P.1 ≫ jz n = F ≫ pullback.fst _ _ := (hZ.2 n).lift_fst _ _ hX
  have hQ : Q.1 ≫ jz n = F ≫ pullback.snd _ _ := (hZ.2 n).lift_fst _ _ hY

  have hF1 : F = pullback.lift (P.1 ≫ jz n) (Q.1 ≫ jz n) (by rw [hP, hQ]; exact hX.trans hY.symm) :=
    pullback.hom_ext (by rw [pullback.lift_fst, hP]) (by rw [pullback.lift_snd, hQ])
  have h1 : F ≫ m = ((E n).L.mul τ P Q).1 ≫ jz n := by
    rw [hmul n τ P Q, hF1]
  have hF2 : F ≫ pullback.lift (pullback.snd (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r))
      (pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r)) (pullback.condition).symm =
      pullback.lift (Q.1 ≫ jz n) (P.1 ≫ jz n) (by rw [hP, hQ]; exact hY.trans hX.symm) :=
    pullback.hom_ext (by rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, hQ])
      (by rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, hP])
  have h2 : F ≫ pullback.lift (pullback.snd (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r))
      (pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r)) (pullback.condition).symm ≫ m =
      ((E n).L.mul τ Q P).1 ≫ jz n := by
    rw [hmul n τ Q P, ← hF2, Category.assoc]
  rw [h2, h1, (E n).comm τ P Q]

end IdentKit

namespace IdentKit

abbrev idPt {S : Type} [CommRing S] {A : Scheme.{0}} (g : A ⟶ Spec (CommRingCat.of S)) : SchemeHomOver g g :=
  ⟨𝟙 A, Category.id_comp g⟩

theorem one_left_hom
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
      (∀ n, CategoryTheory.IsPullback (jz n) (E n).f (G ≫ ProjSpace.π R r) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1)))))))
    (m : pullback (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ⟶ Z) (hm : m ≫ (G ≫ ProjSpace.π R r) = pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r))
    (e : Spec (CommRingCat.of R) ⟶ Z) (he : e ≫ (G ≫ ProjSpace.π R r) = 𝟙 _)
    (ι : Z ⟶ Z) (hι : ι ≫ (G ≫ ProjSpace.π R r) = (G ≫ ProjSpace.π R r)) (act : ↥Λ → (Z ⟶ Z)) (act_over : ∀ x : ↥Λ, act x ≫ (G ≫ ProjSpace.π R r) = (G ≫ ProjSpace.π R r))
    (hmul : ∀ (n : ℕ) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1))))
        (P Q : SchemeHomOver t' (E n).f),
        ((E n).L.mul t' P Q).1 ≫ jz n =
          pullback.lift (P.1 ≫ jz n) (Q.1 ≫ jz n)
            (by simp only [Category.assoc]; rw [(hZ.2 n).w, ← Category.assoc, P.2, ← Category.assoc, Q.2]) ≫ m)
    (hone : ∀ (n : ℕ) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1)))),
        ((E n).L.one t').1 ≫ jz n = (t' ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1))))) ≫ e)
    (hinv : ∀ (n : ℕ) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1))))
        (P : SchemeHomOver t' (E n).f),
        ((E n).L.inv t' P).1 ≫ jz n = (P.1 ≫ jz n) ≫ ι)
    (hact : ∀ (n : ℕ) (x : ↥Λ), (E n).act x ≫ jz n = jz n ≫ act x) :
    pullback.lift ((G ≫ ProjSpace.π R r) ≫ e) (𝟙 Z) (by rw [Category.assoc, he, Category.comp_id, Category.id_comp]) ≫ m = 𝟙 Z := by
  refine eq1 E Z G jz hZ.2 _ _ ?_ (Category.id_comp _) fun n => ?_
  · rw [Category.assoc, hm, pullback.lift_fst_assoc, Category.assoc, he, Category.comp_id]
  rw [Category.comp_id (jz n)]
  have hw := (hZ.2 n).w
  have h1 : jz n ≫ pullback.lift ((G ≫ ProjSpace.π R r) ≫ e) (𝟙 Z)
      (by rw [Category.assoc, he, Category.comp_id, Category.id_comp]) =
      pullback.lift (((E n).L.one (E n).f).1 ≫ jz n) ((idPt (E n).f).1 ≫ jz n)
        (by rw [hone, Category.assoc, Category.assoc, he, Category.comp_id, Category.id_comp, ← hw]) := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, hone, ← Category.assoc, hw]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.comp_id]; exact (Category.id_comp _).symm
  rw [← Category.assoc, h1, ← hmul n (E n).f _ _, (E n).L.one_mul]
  exact Category.id_comp _

theorem one_right_hom
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
      (∀ n, CategoryTheory.IsPullback (jz n) (E n).f (G ≫ ProjSpace.π R r) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1)))))))
    (m : pullback (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ⟶ Z) (hm : m ≫ (G ≫ ProjSpace.π R r) = pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r))
    (e : Spec (CommRingCat.of R) ⟶ Z) (he : e ≫ (G ≫ ProjSpace.π R r) = 𝟙 _)
    (ι : Z ⟶ Z) (hι : ι ≫ (G ≫ ProjSpace.π R r) = (G ≫ ProjSpace.π R r)) (act : ↥Λ → (Z ⟶ Z)) (act_over : ∀ x : ↥Λ, act x ≫ (G ≫ ProjSpace.π R r) = (G ≫ ProjSpace.π R r))
    (hmul : ∀ (n : ℕ) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1))))
        (P Q : SchemeHomOver t' (E n).f),
        ((E n).L.mul t' P Q).1 ≫ jz n =
          pullback.lift (P.1 ≫ jz n) (Q.1 ≫ jz n)
            (by simp only [Category.assoc]; rw [(hZ.2 n).w, ← Category.assoc, P.2, ← Category.assoc, Q.2]) ≫ m)
    (hone : ∀ (n : ℕ) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1)))),
        ((E n).L.one t').1 ≫ jz n = (t' ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1))))) ≫ e)
    (hinv : ∀ (n : ℕ) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1))))
        (P : SchemeHomOver t' (E n).f),
        ((E n).L.inv t' P).1 ≫ jz n = (P.1 ≫ jz n) ≫ ι)
    (hact : ∀ (n : ℕ) (x : ↥Λ), (E n).act x ≫ jz n = jz n ≫ act x) :
    pullback.lift (𝟙 Z) ((G ≫ ProjSpace.π R r) ≫ e) (by rw [Category.assoc, he, Category.comp_id, Category.id_comp]) ≫ m = 𝟙 Z := by
  refine eq1 E Z G jz hZ.2 _ _ ?_ (Category.id_comp _) fun n => ?_
  · rw [Category.assoc, hm, pullback.lift_fst_assoc, Category.id_comp]
  rw [Category.comp_id (jz n)]
  have hw := (hZ.2 n).w
  have h1 : jz n ≫ pullback.lift (𝟙 Z) ((G ≫ ProjSpace.π R r) ≫ e)
      (by rw [Category.assoc, he, Category.comp_id, Category.id_comp]) =
      pullback.lift ((idPt (E n).f).1 ≫ jz n) (((E n).L.one (E n).f).1 ≫ jz n)
        (by rw [hone, Category.assoc, Category.assoc, he, Category.comp_id, Category.id_comp, ← hw]) := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.comp_id]; exact (Category.id_comp _).symm
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, hone, ← Category.assoc, hw]
  rw [← Category.assoc, h1, ← hmul n (E n).f _ _, (E n).L.mul_one]
  exact Category.id_comp _

theorem inv_left_hom
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
      (∀ n, CategoryTheory.IsPullback (jz n) (E n).f (G ≫ ProjSpace.π R r) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1)))))))
    (m : pullback (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ⟶ Z) (hm : m ≫ (G ≫ ProjSpace.π R r) = pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r))
    (e : Spec (CommRingCat.of R) ⟶ Z) (he : e ≫ (G ≫ ProjSpace.π R r) = 𝟙 _)
    (ι : Z ⟶ Z) (hι : ι ≫ (G ≫ ProjSpace.π R r) = (G ≫ ProjSpace.π R r)) (act : ↥Λ → (Z ⟶ Z)) (act_over : ∀ x : ↥Λ, act x ≫ (G ≫ ProjSpace.π R r) = (G ≫ ProjSpace.π R r))
    (hmul : ∀ (n : ℕ) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1))))
        (P Q : SchemeHomOver t' (E n).f),
        ((E n).L.mul t' P Q).1 ≫ jz n =
          pullback.lift (P.1 ≫ jz n) (Q.1 ≫ jz n)
            (by simp only [Category.assoc]; rw [(hZ.2 n).w, ← Category.assoc, P.2, ← Category.assoc, Q.2]) ≫ m)
    (hone : ∀ (n : ℕ) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1)))),
        ((E n).L.one t').1 ≫ jz n = (t' ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1))))) ≫ e)
    (hinv : ∀ (n : ℕ) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1))))
        (P : SchemeHomOver t' (E n).f),
        ((E n).L.inv t' P).1 ≫ jz n = (P.1 ≫ jz n) ≫ ι)
    (hact : ∀ (n : ℕ) (x : ↥Λ), (E n).act x ≫ jz n = jz n ≫ act x) :
    pullback.lift ι (𝟙 Z) (by rw [hι, Category.id_comp]) ≫ m = (G ≫ ProjSpace.π R r) ≫ e := by
  refine eq1 E Z G jz hZ.2 _ _ ?_ ?_ fun n => ?_
  · rw [Category.assoc, hm, pullback.lift_fst_assoc, hι]
  · rw [Category.assoc, he, Category.comp_id]
  have hw := (hZ.2 n).w
  have h1 : jz n ≫ pullback.lift ι (𝟙 Z) (by rw [hι, Category.id_comp]) =
      pullback.lift (((E n).L.inv (E n).f (idPt (E n).f)).1 ≫ jz n) ((idPt (E n).f).1 ≫ jz n)
        (by rw [hinv, Category.assoc, hι]) := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, hinv]
      show jz n ≫ ι = (𝟙 _ ≫ jz n) ≫ ι
      rw [Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.comp_id]; exact (Category.id_comp _).symm
  rw [← Category.assoc, h1, ← hmul n (E n).f _ _, (E n).L.inv_mul_cancel, hone, ← Category.assoc, hw]

end IdentKit

namespace IdentKit

section AssocAux
variable {R : Type} [CommRing R] {r : ℕ} {Z : Scheme.{0}} (G : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) R))
  (m : pullback (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ⟶ Z)
  (hm : m ≫ (G ≫ ProjSpace.π R r) = pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r))

include hm

theorem cφ1 : (pullback.fst (pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r)) (G ≫ ProjSpace.π R r) ≫ m) ≫ (G ≫ ProjSpace.π R r) =
    pullback.snd (pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r)) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r) := by
  simp only [Category.assoc, hm]; exact pullback.condition

omit hm in
theorem c23 : (pullback.fst (pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r)) (G ≫ ProjSpace.π R r) ≫ pullback.snd (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r)) ≫ (G ≫ ProjSpace.π R r) =
    pullback.snd (pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r)) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r) := by
  have h := pullback.condition (f := pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r)) (g := (G ≫ ProjSpace.π R r))
  have h2 := pullback.condition (f := (G ≫ ProjSpace.π R r)) (g := (G ≫ ProjSpace.π R r))
  simp only [Category.assoc] at h ⊢
  rw [← h2]; exact h

theorem cφ2 : (pullback.fst (pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r)) (G ≫ ProjSpace.π R r) ≫ pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r)) ≫ (G ≫ ProjSpace.π R r) =
    (pullback.lift (pullback.fst (pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r)) (G ≫ ProjSpace.π R r) ≫ pullback.snd (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r))
      (pullback.snd (pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r)) (G ≫ ProjSpace.π R r)) (c23 G) ≫ m) ≫ (G ≫ ProjSpace.π R r) := by
  simp only [Category.assoc, hm, pullback.lift_fst_assoc]
  exact congrArg (pullback.fst _ _ ≫ ·) pullback.condition

end AssocAux

set_option maxHeartbeats 3200000 in

theorem assoc_hom
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
      (∀ n, CategoryTheory.IsPullback (jz n) (E n).f (G ≫ ProjSpace.π R r) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1)))))))
    (m : pullback (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ⟶ Z) (hm : m ≫ (G ≫ ProjSpace.π R r) = pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r))
    (e : Spec (CommRingCat.of R) ⟶ Z) (he : e ≫ (G ≫ ProjSpace.π R r) = 𝟙 _)
    (ι : Z ⟶ Z) (hι : ι ≫ (G ≫ ProjSpace.π R r) = (G ≫ ProjSpace.π R r)) (act : ↥Λ → (Z ⟶ Z)) (act_over : ∀ x : ↥Λ, act x ≫ (G ≫ ProjSpace.π R r) = (G ≫ ProjSpace.π R r))
    (hmul : ∀ (n : ℕ) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1))))
        (P Q : SchemeHomOver t' (E n).f),
        ((E n).L.mul t' P Q).1 ≫ jz n =
          pullback.lift (P.1 ≫ jz n) (Q.1 ≫ jz n)
            (by simp only [Category.assoc]; rw [(hZ.2 n).w, ← Category.assoc, P.2, ← Category.assoc, Q.2]) ≫ m)
    (hone : ∀ (n : ℕ) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1)))),
        ((E n).L.one t').1 ≫ jz n = (t' ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1))))) ≫ e)
    (hinv : ∀ (n : ℕ) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1))))
        (P : SchemeHomOver t' (E n).f),
        ((E n).L.inv t' P).1 ≫ jz n = (P.1 ≫ jz n) ≫ ι)
    (hact : ∀ (n : ℕ) (x : ↥Λ), (E n).act x ≫ jz n = jz n ≫ act x) :
    pullback.lift (pullback.fst (pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r)) (G ≫ ProjSpace.π R r) ≫ m)
        (pullback.snd (pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r)) (G ≫ ProjSpace.π R r)) (cφ1 G m hm) ≫ m =
    pullback.lift (pullback.fst (pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r)) (G ≫ ProjSpace.π R r) ≫ pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r))
        (pullback.lift (pullback.fst (pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r)) (G ≫ ProjSpace.π R r) ≫ pullback.snd (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r))
          (pullback.snd (pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r)) (G ≫ ProjSpace.π R r)) (c23 G) ≫ m) (cφ2 G m hm) ≫ m := by

  obtain ⟨K, GP, hGPfin, hGP⟩ :=
    AlgebraicGeometry.exists_isFinite_projSpace_pullback_of_isFinite_projSpace (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) r G rfl r G rfl
  haveI := hGPfin
  obtain ⟨K', GP', hGP'fin, hGP'⟩ :=
    AlgebraicGeometry.exists_isFinite_projSpace_pullback_of_isFinite_projSpace
      (pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r)) (G ≫ ProjSpace.π R r) K GP hGP r G rfl
  haveI := hGP'fin
  refine IdentEngine.eq_of_forall_pullback_fst_truncation_comp_eq R (IsLocalRing.maximalIdeal R) (sRm R) (sRm_eq R)
    (pullback.fst (pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r)) (G ≫ ProjSpace.π R r) ≫ pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r)) K' GP' hGP'
    (G ≫ ProjSpace.π R r) r G rfl _ _ ?_ ?_ fun n => ?_
  · simp only [Category.assoc, hm, pullback.lift_fst_assoc]
  · simp only [Category.assoc, hm, pullback.lift_fst_assoc]

  set F := pullback.fst (pullback.fst (pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r)) (G ≫ ProjSpace.π R r) ≫ pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r)) (sRm R n) with hF
  set τ := pullback.snd (pullback.fst (pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r)) (G ≫ ProjSpace.π R r) ≫ pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r)) (sRm R n) with hτ
  have h1 : ((F ≫ pullback.fst _ _) ≫ pullback.fst _ _) ≫ (G ≫ ProjSpace.π R r) = τ ≫ sRm R n := by
    simp only [Category.assoc]; exact pullback.condition
  have h2 : ((F ≫ pullback.fst _ _) ≫ pullback.snd _ _) ≫ (G ≫ ProjSpace.π R r) = τ ≫ sRm R n := by
    rw [← h1]; simp only [Category.assoc]
    exact congrArg (F ≫ pullback.fst _ _ ≫ ·) (pullback.condition (f := (G ≫ ProjSpace.π R r)) (g := (G ≫ ProjSpace.π R r))).symm
  have h3 : (F ≫ pullback.snd _ _) ≫ (G ≫ ProjSpace.π R r) = τ ≫ sRm R n := by
    rw [← h1]; simp only [Category.assoc]
    exact congrArg (F ≫ ·) (pullback.condition (f := pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r)) (g := (G ≫ ProjSpace.π R r))).symm
  let P1 : SchemeHomOver τ (E n).f := ⟨(hZ.2 n).lift _ _ h1, (hZ.2 n).lift_snd _ _ h1⟩
  let P2 : SchemeHomOver τ (E n).f := ⟨(hZ.2 n).lift _ _ h2, (hZ.2 n).lift_snd _ _ h2⟩
  let P3 : SchemeHomOver τ (E n).f := ⟨(hZ.2 n).lift _ _ h3, (hZ.2 n).lift_snd _ _ h3⟩
  have e1 : P1.1 ≫ jz n = (F ≫ pullback.fst _ _) ≫ pullback.fst _ _ := (hZ.2 n).lift_fst _ _ h1
  have e2 : P2.1 ≫ jz n = (F ≫ pullback.fst _ _) ≫ pullback.snd _ _ := (hZ.2 n).lift_fst _ _ h2
  have e3 : P3.1 ≫ jz n = F ≫ pullback.snd _ _ := (hZ.2 n).lift_fst _ _ h3
  have c12 : (P1.1 ≫ jz n) ≫ (G ≫ ProjSpace.π R r) = (P2.1 ≫ jz n) ≫ (G ≫ ProjSpace.π R r) := by rw [e1, e2]; exact h1.trans h2.symm
  have c23' : (P2.1 ≫ jz n) ≫ (G ≫ ProjSpace.π R r) = (P3.1 ≫ jz n) ≫ (G ≫ ProjSpace.π R r) := by rw [e2, e3]; exact h2.trans h3.symm
  have hF12 : F ≫ pullback.fst _ _ = pullback.lift (P1.1 ≫ jz n) (P2.1 ≫ jz n) c12 :=
    pullback.hom_ext (by rw [pullback.lift_fst, e1]) (by rw [pullback.lift_snd, e2])
  have hm12 : (F ≫ pullback.fst _ _) ≫ m = ((E n).L.mul τ P1 P2).1 ≫ jz n := by rw [hmul n τ P1 P2, hF12]
  have cL : (((E n).L.mul τ P1 P2).1 ≫ jz n) ≫ (G ≫ ProjSpace.π R r) = (P3.1 ≫ jz n) ≫ (G ≫ ProjSpace.π R r) := by
    rw [← hm12, e3]
    have h := h1.trans h3.symm
    simp only [Category.assoc, hm] at h ⊢
    exact h
  have hL : F ≫ pullback.lift (pullback.fst (pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r)) (G ≫ ProjSpace.π R r) ≫ m)
        (pullback.snd (pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r)) (G ≫ ProjSpace.π R r)) (cφ1 G m hm) =
      pullback.lift (((E n).L.mul τ P1 P2).1 ≫ jz n) (P3.1 ≫ jz n) cL :=
    pullback.hom_ext (by rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, ← hm12, Category.assoc])
      (by rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, e3])
  have lhs : F ≫ pullback.lift (pullback.fst (pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r)) (G ≫ ProjSpace.π R r) ≫ m)
        (pullback.snd (pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r)) (G ≫ ProjSpace.π R r)) (cφ1 G m hm) ≫ m =
      ((E n).L.mul τ ((E n).L.mul τ P1 P2) P3).1 ≫ jz n := by
    rw [hmul n τ _ P3, ← hL, Category.assoc]
  have hF23 : F ≫ pullback.lift (pullback.fst (pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r)) (G ≫ ProjSpace.π R r) ≫ pullback.snd (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r))
        (pullback.snd (pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r)) (G ≫ ProjSpace.π R r)) (c23 G) =
      pullback.lift (P2.1 ≫ jz n) (P3.1 ≫ jz n) c23' :=
    pullback.hom_ext (by rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, e2, Category.assoc])
      (by rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, e3])
  have hm23 : F ≫ pullback.lift (pullback.fst (pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r)) (G ≫ ProjSpace.π R r) ≫ pullback.snd (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r))
        (pullback.snd (pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r)) (G ≫ ProjSpace.π R r)) (c23 G) ≫ m =
      ((E n).L.mul τ P2 P3).1 ≫ jz n := by rw [hmul n τ P2 P3, ← hF23]; try rw [Category.assoc]
  have cR : (P1.1 ≫ jz n) ≫ (G ≫ ProjSpace.π R r) = (((E n).L.mul τ P2 P3).1 ≫ jz n) ≫ (G ≫ ProjSpace.π R r) := by
    rw [← hm23, e1]; simp only [Category.assoc, hm, pullback.lift_fst_assoc]
    exact congrArg (F ≫ pullback.fst _ _ ≫ ·) pullback.condition
  have hR : F ≫ pullback.lift (pullback.fst (pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r)) (G ≫ ProjSpace.π R r) ≫ pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r))
        (pullback.lift (pullback.fst (pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r)) (G ≫ ProjSpace.π R r) ≫ pullback.snd (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r))
          (pullback.snd (pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r)) (G ≫ ProjSpace.π R r)) (c23 G) ≫ m) (cφ2 G m hm) =
      pullback.lift (P1.1 ≫ jz n) (((E n).L.mul τ P2 P3).1 ≫ jz n) cR :=
    pullback.hom_ext (by rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, e1, Category.assoc])
      (by rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, ← hm23])
  have rhs : F ≫ pullback.lift (pullback.fst (pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r)) (G ≫ ProjSpace.π R r) ≫ pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r))
        (pullback.lift (pullback.fst (pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r)) (G ≫ ProjSpace.π R r) ≫ pullback.snd (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r))
          (pullback.snd (pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r)) (G ≫ ProjSpace.π R r)) (c23 G) ≫ m) (cφ2 G m hm) ≫ m =
      ((E n).L.mul τ P1 ((E n).L.mul τ P2 P3)).1 ≫ jz n := by
    rw [hmul n τ P1 _, ← hR, Category.assoc]
  rw [lhs, rhs, (E n).L.mul_assoc]

end IdentKit

namespace IdentKit

theorem hact_assoc_aux {Λ' : Type} {A Z' W : Scheme.{0}} (actE : Λ' → (A ⟶ A)) (act' : Λ' → (Z' ⟶ Z')) (j : A ⟶ Z')
    (hact : ∀ x, actE x ≫ j = j ≫ act' x) (x : Λ') (h : Z' ⟶ W) :
    actE x ≫ j ≫ h = j ≫ act' x ≫ h := by
  rw [← Category.assoc, hact, Category.assoc]

theorem act_one_hom
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
      (∀ n, CategoryTheory.IsPullback (jz n) (E n).f (G ≫ ProjSpace.π R r) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1)))))))
    (m : pullback (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ⟶ Z) (hm : m ≫ (G ≫ ProjSpace.π R r) = pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r))
    (e : Spec (CommRingCat.of R) ⟶ Z) (he : e ≫ (G ≫ ProjSpace.π R r) = 𝟙 _)
    (ι : Z ⟶ Z) (hι : ι ≫ (G ≫ ProjSpace.π R r) = (G ≫ ProjSpace.π R r)) (act : ↥Λ → (Z ⟶ Z)) (act_over : ∀ x : ↥Λ, act x ≫ (G ≫ ProjSpace.π R r) = (G ≫ ProjSpace.π R r))
    (hmul : ∀ (n : ℕ) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1))))
        (P Q : SchemeHomOver t' (E n).f),
        ((E n).L.mul t' P Q).1 ≫ jz n =
          pullback.lift (P.1 ≫ jz n) (Q.1 ≫ jz n)
            (by simp only [Category.assoc]; rw [(hZ.2 n).w, ← Category.assoc, P.2, ← Category.assoc, Q.2]) ≫ m)
    (hone : ∀ (n : ℕ) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1)))),
        ((E n).L.one t').1 ≫ jz n = (t' ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1))))) ≫ e)
    (hinv : ∀ (n : ℕ) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1))))
        (P : SchemeHomOver t' (E n).f),
        ((E n).L.inv t' P).1 ≫ jz n = (P.1 ≫ jz n) ≫ ι)
    (hact : ∀ (n : ℕ) (x : ↥Λ), (E n).act x ≫ jz n = jz n ≫ act x)
    (h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ) : act ⟨1, h1⟩ = 𝟙 Z := by
  refine IdentEngine.eq_of_forall_pullback_fst_truncation_comp_eq R (IsLocalRing.maximalIdeal R) (sRm R) (sRm_eq R)
    (G ≫ ProjSpace.π R r) r G rfl (G ≫ ProjSpace.π R r) r G rfl _ _ (act_over _) (Category.id_comp _) ?_
  intro n
  set F := pullback.fst (G ≫ ProjSpace.π R r) (sRm R n) with hF
  set τ := pullback.snd (G ≫ ProjSpace.π R r) (sRm R n) with hτ
  have hX : F ≫ (G ≫ ProjSpace.π R r) = τ ≫ sRm R n := pullback.condition
  let P : SchemeHomOver τ (E n).f := ⟨(hZ.2 n).lift _ _ hX, (hZ.2 n).lift_snd _ _ hX⟩
  have hP : P.1 ≫ jz n = F := (hZ.2 n).lift_fst _ _ hX
  rw [← hP, Category.assoc, Category.assoc, ← hact n, (E n).act_one h1, Category.id_comp, Category.comp_id]

theorem act_mul_hom
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
      (∀ n, CategoryTheory.IsPullback (jz n) (E n).f (G ≫ ProjSpace.π R r) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1)))))))
    (m : pullback (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ⟶ Z) (hm : m ≫ (G ≫ ProjSpace.π R r) = pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r))
    (e : Spec (CommRingCat.of R) ⟶ Z) (he : e ≫ (G ≫ ProjSpace.π R r) = 𝟙 _)
    (ι : Z ⟶ Z) (hι : ι ≫ (G ≫ ProjSpace.π R r) = (G ≫ ProjSpace.π R r)) (act : ↥Λ → (Z ⟶ Z)) (act_over : ∀ x : ↥Λ, act x ≫ (G ≫ ProjSpace.π R r) = (G ≫ ProjSpace.π R r))
    (hmul : ∀ (n : ℕ) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1))))
        (P Q : SchemeHomOver t' (E n).f),
        ((E n).L.mul t' P Q).1 ≫ jz n =
          pullback.lift (P.1 ≫ jz n) (Q.1 ≫ jz n)
            (by simp only [Category.assoc]; rw [(hZ.2 n).w, ← Category.assoc, P.2, ← Category.assoc, Q.2]) ≫ m)
    (hone : ∀ (n : ℕ) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1)))),
        ((E n).L.one t').1 ≫ jz n = (t' ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1))))) ≫ e)
    (hinv : ∀ (n : ℕ) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1))))
        (P : SchemeHomOver t' (E n).f),
        ((E n).L.inv t' P).1 ≫ jz n = (P.1 ≫ jz n) ≫ ι)
    (hact : ∀ (n : ℕ) (x : ↥Λ), (E n).act x ≫ jz n = jz n ≫ act x)
    (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ) :
    act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = act y ≫ act x := by
  refine IdentEngine.eq_of_forall_pullback_fst_truncation_comp_eq R (IsLocalRing.maximalIdeal R) (sRm R) (sRm_eq R)
    (G ≫ ProjSpace.π R r) r G rfl (G ≫ ProjSpace.π R r) r G rfl _ _ (act_over _) (by rw [Category.assoc, act_over, act_over]) ?_
  intro n
  set F := pullback.fst (G ≫ ProjSpace.π R r) (sRm R n) with hF
  set τ := pullback.snd (G ≫ ProjSpace.π R r) (sRm R n) with hτ
  have hX : F ≫ (G ≫ ProjSpace.π R r) = τ ≫ sRm R n := pullback.condition
  let P : SchemeHomOver τ (E n).f := ⟨(hZ.2 n).lift _ _ hX, (hZ.2 n).lift_snd _ _ hX⟩
  have hP : P.1 ≫ jz n = F := (hZ.2 n).lift_fst _ _ hX
  rw [← hP, Category.assoc, Category.assoc, ← hact n, (E n).act_mul x y h, Category.assoc, hact n x,
    hact_assoc_aux (fun z => (E n).act z) act (jz n) (hact n)]

theorem act_add_hom_aux
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
      (∀ n, CategoryTheory.IsPullback (jz n) (E n).f (G ≫ ProjSpace.π R r) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1)))))))
    (m : pullback (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ⟶ Z) (hm : m ≫ (G ≫ ProjSpace.π R r) = pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r))
    (e : Spec (CommRingCat.of R) ⟶ Z) (he : e ≫ (G ≫ ProjSpace.π R r) = 𝟙 _)
    (ι : Z ⟶ Z) (hι : ι ≫ (G ≫ ProjSpace.π R r) = (G ≫ ProjSpace.π R r)) (act : ↥Λ → (Z ⟶ Z)) (act_over : ∀ x : ↥Λ, act x ≫ (G ≫ ProjSpace.π R r) = (G ≫ ProjSpace.π R r))
    (hmul : ∀ (n : ℕ) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1))))
        (P Q : SchemeHomOver t' (E n).f),
        ((E n).L.mul t' P Q).1 ≫ jz n =
          pullback.lift (P.1 ≫ jz n) (Q.1 ≫ jz n)
            (by simp only [Category.assoc]; rw [(hZ.2 n).w, ← Category.assoc, P.2, ← Category.assoc, Q.2]) ≫ m)
    (hone : ∀ (n : ℕ) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1)))),
        ((E n).L.one t').1 ≫ jz n = (t' ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1))))) ≫ e)
    (hinv : ∀ (n : ℕ) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1))))
        (P : SchemeHomOver t' (E n).f),
        ((E n).L.inv t' P).1 ≫ jz n = (P.1 ≫ jz n) ≫ ι)
    (hact : ∀ (n : ℕ) (x : ↥Λ), (E n).act x ≫ jz n = jz n ≫ act x)
    (x y : ↥Λ) :
    act (x + y) = pullback.lift (act x) (act y) (by rw [act_over, act_over]) ≫ m := by
  refine IdentEngine.eq_of_forall_pullback_fst_truncation_comp_eq R (IsLocalRing.maximalIdeal R) (sRm R) (sRm_eq R)
    (G ≫ ProjSpace.π R r) r G rfl (G ≫ ProjSpace.π R r) r G rfl _ _ (act_over _)
    (by rw [Category.assoc, hm, pullback.lift_fst_assoc, act_over]) ?_
  intro n
  set F := pullback.fst (G ≫ ProjSpace.π R r) (sRm R n) with hF
  set τ := pullback.snd (G ≫ ProjSpace.π R r) (sRm R n) with hτ
  have hX : F ≫ (G ≫ ProjSpace.π R r) = τ ≫ sRm R n := pullback.condition
  let P : SchemeHomOver τ (E n).f := ⟨(hZ.2 n).lift _ _ hX, (hZ.2 n).lift_snd _ _ hX⟩
  have hP : P.1 ≫ jz n = F := (hZ.2 n).lift_fst _ _ hX

  have h1 : F ≫ act (x + y) = ((E n).L.mul τ (pushPt ((E n).act x) ((E n).act_over x) P)
      (pushPt ((E n).act y) ((E n).act_over y) P)).1 ≫ jz n := by
    rw [← (E n).act_add x y τ P]
    show F ≫ act (x + y) = (P.1 ≫ (E n).act (x + y)) ≫ jz n
    rw [← hP, Category.assoc, Category.assoc, hact n]

  have h2 : F ≫ pullback.lift (act x) (act y) (by rw [act_over, act_over]) =
      pullback.lift ((pushPt ((E n).act x) ((E n).act_over x) P).1 ≫ jz n)
        ((pushPt ((E n).act y) ((E n).act_over y) P).1 ≫ jz n)
        (by simp only [Category.assoc]; rw [(hZ.2 n).w, ← Category.assoc, (pushPt ((E n).act x) ((E n).act_over x) P).2,
              ← Category.assoc, (pushPt ((E n).act y) ((E n).act_over y) P).2]) := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
      show F ≫ act x = (P.1 ≫ (E n).act x) ≫ jz n
      rw [← hP, Category.assoc, Category.assoc, hact n]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]
      show F ≫ act y = (P.1 ≫ (E n).act y) ≫ jz n
      rw [← hP, Category.assoc, Category.assoc, hact n]
  have h2' := congrArg (· ≫ m) h2
  simp only [Category.assoc] at h2'
  rw [h1, h2', hmul n τ]

theorem act_hom_hom_aux
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
      (∀ n, CategoryTheory.IsPullback (jz n) (E n).f (G ≫ ProjSpace.π R r) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1)))))))
    (m : pullback (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ⟶ Z) (hm : m ≫ (G ≫ ProjSpace.π R r) = pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r))
    (e : Spec (CommRingCat.of R) ⟶ Z) (he : e ≫ (G ≫ ProjSpace.π R r) = 𝟙 _)
    (ι : Z ⟶ Z) (hι : ι ≫ (G ≫ ProjSpace.π R r) = (G ≫ ProjSpace.π R r)) (act : ↥Λ → (Z ⟶ Z)) (act_over : ∀ x : ↥Λ, act x ≫ (G ≫ ProjSpace.π R r) = (G ≫ ProjSpace.π R r))
    (hmul : ∀ (n : ℕ) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1))))
        (P Q : SchemeHomOver t' (E n).f),
        ((E n).L.mul t' P Q).1 ≫ jz n =
          pullback.lift (P.1 ≫ jz n) (Q.1 ≫ jz n)
            (by simp only [Category.assoc]; rw [(hZ.2 n).w, ← Category.assoc, P.2, ← Category.assoc, Q.2]) ≫ m)
    (hone : ∀ (n : ℕ) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1)))),
        ((E n).L.one t').1 ≫ jz n = (t' ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1))))) ≫ e)
    (hinv : ∀ (n : ℕ) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1))))
        (P : SchemeHomOver t' (E n).f),
        ((E n).L.inv t' P).1 ≫ jz n = (P.1 ≫ jz n) ≫ ι)
    (hact : ∀ (n : ℕ) (x : ↥Λ), (E n).act x ≫ jz n = jz n ≫ act x)
    (x : ↥Λ) :
    pullback.lift (pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ act x) (pullback.snd (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ act x)
        (by rw [Category.assoc, act_over, Category.assoc, act_over, pullback.condition]) ≫ m =
      m ≫ act x := by
  obtain ⟨K, GP, hGPfin, hGP⟩ :=
    AlgebraicGeometry.exists_isFinite_projSpace_pullback_of_isFinite_projSpace
      (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) r G rfl r G rfl
  haveI := hGPfin
  refine IdentEngine.eq_of_forall_pullback_fst_truncation_comp_eq R (IsLocalRing.maximalIdeal R) (sRm R) (sRm_eq R)
    (pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r)) K GP hGP
    (G ≫ ProjSpace.π R r) r G rfl _ _ ?_ ?_ ?_
  · rw [Category.assoc, hm, pullback.lift_fst_assoc, Category.assoc, act_over]
  · rw [Category.assoc, act_over, hm]
  intro n
  set F := pullback.fst (pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r)) (sRm R n) with hF
  set τ := pullback.snd (pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r)) (sRm R n) with hτ
  have hX : (F ≫ pullback.fst _ _) ≫ (G ≫ ProjSpace.π R r) = τ ≫ sRm R n := by
    rw [Category.assoc]; exact pullback.condition
  have hY : (F ≫ pullback.snd _ _) ≫ (G ≫ ProjSpace.π R r) = τ ≫ sRm R n := by
    rw [Category.assoc, ← pullback.condition]; exact pullback.condition
  let P : SchemeHomOver τ (E n).f := ⟨(hZ.2 n).lift _ _ hX, (hZ.2 n).lift_snd _ _ hX⟩
  let Q : SchemeHomOver τ (E n).f := ⟨(hZ.2 n).lift _ _ hY, (hZ.2 n).lift_snd _ _ hY⟩
  have hP : P.1 ≫ jz n = F ≫ pullback.fst _ _ := (hZ.2 n).lift_fst _ _ hX
  have hQ : Q.1 ≫ jz n = F ≫ pullback.snd _ _ := (hZ.2 n).lift_fst _ _ hY
  have hF1 : F = pullback.lift (P.1 ≫ jz n) (Q.1 ≫ jz n) (by rw [hP, hQ]; exact hX.trans hY.symm) :=
    pullback.hom_ext (by rw [pullback.lift_fst, hP]) (by rw [pullback.lift_snd, hQ])

  have hPh : ∀ {W : Scheme.{0}} (h : Z ⟶ W), P.1 ≫ jz n ≫ h = F ≫ pullback.fst _ _ ≫ h := fun h => by
    simpa only [Category.assoc] using congrArg (· ≫ h) hP
  have hQh : ∀ {W : Scheme.{0}} (h : Z ⟶ W), Q.1 ≫ jz n ≫ h = F ≫ pullback.snd _ _ ≫ h := fun h => by
    simpa only [Category.assoc] using congrArg (· ≫ h) hQ
  have h0 : F ≫ m = ((E n).L.mul τ P Q).1 ≫ jz n := by rw [hmul n τ P Q, hF1]

  have h1 : F ≫ m ≫ act x = ((E n).L.mul τ (pushPt ((E n).act x) ((E n).act_over x) P)
      (pushPt ((E n).act x) ((E n).act_over x) Q)).1 ≫ jz n := by
    rw [← (E n).act_hom x τ P Q]
    show F ≫ m ≫ act x = (((E n).L.mul τ P Q).1 ≫ (E n).act x) ≫ jz n
    have h0' := congrArg (· ≫ act x) h0
    simp only [Category.assoc] at h0'
    rw [h0']
    simp only [Category.assoc, hact n x]

  have h2 : F ≫ pullback.lift (pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ act x) (pullback.snd (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ act x)
        (by rw [Category.assoc, act_over, Category.assoc, act_over, pullback.condition]) =
      pullback.lift ((pushPt ((E n).act x) ((E n).act_over x) P).1 ≫ jz n)
        ((pushPt ((E n).act x) ((E n).act_over x) Q).1 ≫ jz n)
        (by simp only [Category.assoc, (hZ.2 n).w, reassoc_of% (pushPt ((E n).act x) ((E n).act_over x) P).2,
              reassoc_of% (pushPt ((E n).act x) ((E n).act_over x) Q).2]) := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
      show F ≫ pullback.fst _ _ ≫ act x = (P.1 ≫ (E n).act x) ≫ jz n
      simp only [Category.assoc, hact n x, hPh]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]
      show F ≫ pullback.snd _ _ ≫ act x = (Q.1 ≫ (E n).act x) ≫ jz n
      simp only [Category.assoc, hact n x, hQh]
  rw [h1, hmul n τ]
  refine (Category.assoc _ _ _).symm.trans ?_
  congr 1

theorem act_hom_hom
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
      (∀ n, CategoryTheory.IsPullback (jz n) (E n).f (G ≫ ProjSpace.π R r) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1)))))))
    (m : pullback (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ⟶ Z) (hm : m ≫ (G ≫ ProjSpace.π R r) = pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r))
    (e : Spec (CommRingCat.of R) ⟶ Z) (he : e ≫ (G ≫ ProjSpace.π R r) = 𝟙 _)
    (ι : Z ⟶ Z) (hι : ι ≫ (G ≫ ProjSpace.π R r) = (G ≫ ProjSpace.π R r)) (act : ↥Λ → (Z ⟶ Z)) (act_over : ∀ x : ↥Λ, act x ≫ (G ≫ ProjSpace.π R r) = (G ≫ ProjSpace.π R r))
    (hmul : ∀ (n : ℕ) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1))))
        (P Q : SchemeHomOver t' (E n).f),
        ((E n).L.mul t' P Q).1 ≫ jz n =
          pullback.lift (P.1 ≫ jz n) (Q.1 ≫ jz n)
            (by simp only [Category.assoc]; rw [(hZ.2 n).w, ← Category.assoc, P.2, ← Category.assoc, Q.2]) ≫ m)
    (hone : ∀ (n : ℕ) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1)))),
        ((E n).L.one t').1 ≫ jz n = (t' ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1))))) ≫ e)
    (hinv : ∀ (n : ℕ) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1))))
        (P : SchemeHomOver t' (E n).f),
        ((E n).L.inv t' P).1 ≫ jz n = (P.1 ≫ jz n) ≫ ι)
    (hact : ∀ (n : ℕ) (x : ↥Λ), (E n).act x ≫ jz n = jz n ≫ act x)
    (x : ↥Λ) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t' (G ≫ ProjSpace.π R r)) :
    pullback.lift (P.1 ≫ act x) (Q.1 ≫ act x) (by rw [Category.assoc, act_over, Category.assoc, act_over, P.2, Q.2]) ≫ m =
      (pullback.lift P.1 Q.1 (P.2.trans Q.2.symm) ≫ m) ≫ act x := by
  have hmor := act_hom_hom_aux hqq' hB Λ hΛ μ hμ star hstar R π hπ E t ht Z G jz hZ m hm e he ι hι act act_over hmul hone hinv hact x
  have hL : pullback.lift P.1 Q.1 (P.2.trans Q.2.symm) ≫
      pullback.lift (pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ act x) (pullback.snd (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ act x)
        (by rw [Category.assoc, act_over, Category.assoc, act_over, pullback.condition]) =
      pullback.lift (P.1 ≫ act x) (Q.1 ≫ act x) (by rw [Category.assoc, act_over, Category.assoc, act_over, P.2, Q.2]) :=
    pullback.hom_ext (by rw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_fst])
      (by rw [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, pullback.lift_snd])
  rw [← hL, Category.assoc, hmor, Category.assoc]

theorem act_add_hom
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
      (∀ n, CategoryTheory.IsPullback (jz n) (E n).f (G ≫ ProjSpace.π R r) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1)))))))
    (m : pullback (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ⟶ Z) (hm : m ≫ (G ≫ ProjSpace.π R r) = pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r))
    (e : Spec (CommRingCat.of R) ⟶ Z) (he : e ≫ (G ≫ ProjSpace.π R r) = 𝟙 _)
    (ι : Z ⟶ Z) (hι : ι ≫ (G ≫ ProjSpace.π R r) = (G ≫ ProjSpace.π R r)) (act : ↥Λ → (Z ⟶ Z)) (act_over : ∀ x : ↥Λ, act x ≫ (G ≫ ProjSpace.π R r) = (G ≫ ProjSpace.π R r))
    (hmul : ∀ (n : ℕ) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1))))
        (P Q : SchemeHomOver t' (E n).f),
        ((E n).L.mul t' P Q).1 ≫ jz n =
          pullback.lift (P.1 ≫ jz n) (Q.1 ≫ jz n)
            (by simp only [Category.assoc]; rw [(hZ.2 n).w, ← Category.assoc, P.2, ← Category.assoc, Q.2]) ≫ m)
    (hone : ∀ (n : ℕ) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1)))),
        ((E n).L.one t').1 ≫ jz n = (t' ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1))))) ≫ e)
    (hinv : ∀ (n : ℕ) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1))))
        (P : SchemeHomOver t' (E n).f),
        ((E n).L.inv t' P).1 ≫ jz n = (P.1 ≫ jz n) ≫ ι)
    (hact : ∀ (n : ℕ) (x : ↥Λ), (E n).act x ≫ jz n = jz n ≫ act x)
    (x y : ↥Λ) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t' (G ≫ ProjSpace.π R r)) :
    P.1 ≫ act (x + y) =
      pullback.lift (P.1 ≫ act x) (P.1 ≫ act y) (by rw [Category.assoc, act_over, Category.assoc, act_over]) ≫ m := by
  have hmor := act_add_hom_aux hqq' hB Λ hΛ μ hμ star hstar R π hπ E t ht Z G jz hZ m hm e he ι hι act act_over hmul hone hinv hact x y
  have hL : P.1 ≫ pullback.lift (act x) (act y) (by rw [act_over, act_over]) =
      pullback.lift (P.1 ≫ act x) (P.1 ≫ act y) (by rw [Category.assoc, act_over, Category.assoc, act_over]) :=
    pullback.hom_ext (by rw [Category.assoc, pullback.lift_fst, pullback.lift_fst])
      (by rw [Category.assoc, pullback.lift_snd, pullback.lift_snd])
  rw [hmor, ← Category.assoc, hL]

end IdentKit

open IdentKit in
set_option maxHeartbeats 3200000 in
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
      (∀ n, CategoryTheory.IsPullback (jz n) (E n).f (G ≫ ProjSpace.π R r) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1)))))))
    (m : pullback (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ⟶ Z) (hm : m ≫ (G ≫ ProjSpace.π R r) = pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r))
    (e : Spec (CommRingCat.of R) ⟶ Z) (he : e ≫ (G ≫ ProjSpace.π R r) = 𝟙 _)
    (ι : Z ⟶ Z) (hι : ι ≫ (G ≫ ProjSpace.π R r) = (G ≫ ProjSpace.π R r)) (act : ↥Λ → (Z ⟶ Z)) (act_over : ∀ x : ↥Λ, act x ≫ (G ≫ ProjSpace.π R r) = (G ≫ ProjSpace.π R r))
    (hmul : ∀ (n : ℕ) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1))))
        (P Q : SchemeHomOver t' (E n).f),
        ((E n).L.mul t' P Q).1 ≫ jz n =
          pullback.lift (P.1 ≫ jz n) (Q.1 ≫ jz n)
            (by simp only [Category.assoc]; rw [(hZ.2 n).w, ← Category.assoc, P.2, ← Category.assoc, Q.2]) ≫ m)
    (hone : ∀ (n : ℕ) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1)))),
        ((E n).L.one t').1 ≫ jz n = (t' ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1))))) ≫ e)
    (hinv : ∀ (n : ℕ) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1))))
        (P : SchemeHomOver t' (E n).f),
        ((E n).L.inv t' P).1 ≫ jz n = (P.1 ≫ jz n) ≫ ι)
    (hact : ∀ (n : ℕ) (x : ↥Λ), (E n).act x ≫ jz n = jz n ≫ act x)
 :
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
          pullback.lift (P.1 ≫ act x) (P.1 ≫ act y) (by rw [Category.assoc, act_over, Category.assoc, act_over]) ≫ m) := by
  have Hassoc := IdentKit.assoc_hom hqq' hB Λ hΛ μ hμ star hstar R π hπ E t ht Z G jz hZ m hm e he ι hι act act_over hmul hone hinv hact
  have Hl := IdentKit.one_left_hom hqq' hB Λ hΛ μ hμ star hstar R π hπ E t ht Z G jz hZ m hm e he ι hι act act_over hmul hone hinv hact
  have Hr := IdentKit.one_right_hom hqq' hB Λ hΛ μ hμ star hstar R π hπ E t ht Z G jz hZ m hm e he ι hι act act_over hmul hone hinv hact
  have Hi := IdentKit.inv_left_hom hqq' hB Λ hΛ μ hμ star hstar R π hπ E t ht Z G jz hZ m hm e he ι hι act act_over hmul hone hinv hact
  have Hc := IdentKit.comm_hom hqq' hB Λ hΛ μ hμ star hstar R π hπ E t ht Z G jz hZ m hm e he ι hι act act_over hmul hone hinv hact
  refine ⟨?_, ?_, ?_, ?_, ?_, IdentKit.act_one_hom hqq' hB Λ hΛ μ hμ star hstar R π hπ E t ht Z G jz hZ m hm e he ι hι act act_over hmul hone hinv hact, IdentKit.act_mul_hom hqq' hB Λ hΛ μ hμ star hstar R π hπ E t ht Z G jz hZ m hm e he ι hι act act_over hmul hone hinv hact, IdentKit.act_hom_hom hqq' hB Λ hΛ μ hμ star hstar R π hπ E t ht Z G jz hZ m hm e he ι hι act act_over hmul hone hinv hact, IdentKit.act_add_hom hqq' hB Λ hΛ μ hμ star hstar R π hπ E t ht Z G jz hZ m hm e he ι hι act act_over hmul hone hinv hact⟩
  ·
    intro T t' x y z
    have pxy : x.1 ≫ (G ≫ ProjSpace.π R r) = y.1 ≫ (G ≫ ProjSpace.π R r) := x.2.trans y.2.symm
    have pξ : pullback.lift x.1 y.1 pxy ≫ (pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r)) = z.1 ≫ (G ≫ ProjSpace.π R r) := by
      rw [pullback.lift_fst_assoc, x.2, z.2]
    have h1 : pullback.lift (pullback.lift x.1 y.1 pxy) z.1 pξ ≫
        pullback.lift (pullback.fst (pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r)) (G ≫ ProjSpace.π R r) ≫ m)
          (pullback.snd (pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r)) (G ≫ ProjSpace.π R r)) (cφ1 G m hm) =
        pullback.lift (pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ m) z.1
          (by rw [Category.assoc, hm, pullback.lift_fst_assoc, x.2, z.2]) :=
      pullback.hom_ext (by rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, pullback.lift_fst_assoc])
        (by rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, pullback.lift_snd])
    have h2a : pullback.lift (pullback.lift x.1 y.1 pxy) z.1 pξ ≫
        pullback.lift (pullback.fst (pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r)) (G ≫ ProjSpace.π R r) ≫ pullback.snd (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r))
          (pullback.snd (pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r)) (G ≫ ProjSpace.π R r)) (c23 G) =
        pullback.lift y.1 z.1 (y.2.trans z.2.symm) :=
      pullback.hom_ext (by rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_snd])
        (by rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, pullback.lift_snd])
    have h2 : pullback.lift (pullback.lift x.1 y.1 pxy) z.1 pξ ≫
        pullback.lift (pullback.fst (pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r)) (G ≫ ProjSpace.π R r) ≫ pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r))
          (pullback.lift (pullback.fst (pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r)) (G ≫ ProjSpace.π R r) ≫ pullback.snd (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r))
            (pullback.snd (pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r) ≫ (G ≫ ProjSpace.π R r)) (G ≫ ProjSpace.π R r)) (c23 G) ≫ m) (cφ2 G m hm) =
        pullback.lift x.1 (pullback.lift y.1 z.1 (y.2.trans z.2.symm) ≫ m)
          (by rw [Category.assoc, hm, pullback.lift_fst_assoc, y.2, x.2]) :=
      pullback.hom_ext (by rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_fst])
        (by rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, ← Category.assoc, h2a])
    rw [← h1, ← h2, Category.assoc, Category.assoc, Hassoc]
  ·
    intro T t' x
    have h : x.1 ≫ pullback.lift ((G ≫ ProjSpace.π R r) ≫ e) (𝟙 Z) (by rw [Category.assoc, he, Category.comp_id, Category.id_comp]) =
        pullback.lift (t' ≫ e) x.1 (by rw [Category.assoc, he, Category.comp_id, x.2]) :=
      pullback.hom_ext (by rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, ← Category.assoc, x.2])
        (by rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.comp_id])
    rw [← h, Category.assoc, Hl, Category.comp_id]
  ·
    intro T t' x
    have h : x.1 ≫ pullback.lift (𝟙 Z) ((G ≫ ProjSpace.π R r) ≫ e) (by rw [Category.assoc, he, Category.comp_id, Category.id_comp]) =
        pullback.lift x.1 (t' ≫ e) (by rw [Category.assoc, he, Category.comp_id, x.2]) :=
      pullback.hom_ext (by rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.comp_id])
        (by rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, ← Category.assoc, x.2])
    rw [← h, Category.assoc, Hr, Category.comp_id]
  ·
    intro T t' x
    have h : x.1 ≫ pullback.lift ι (𝟙 Z) (by rw [hι, Category.id_comp]) =
        pullback.lift (x.1 ≫ ι) x.1 (by rw [Category.assoc, hι]) :=
      pullback.hom_ext (by rw [Category.assoc, pullback.lift_fst, pullback.lift_fst])
        (by rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.comp_id])
    rw [← h, Category.assoc, Hi, ← Category.assoc, x.2]
  ·
    intro T t' x y
    have h : pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫
        pullback.lift (pullback.snd (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r)) (pullback.fst (G ≫ ProjSpace.π R r) (G ≫ ProjSpace.π R r)) (pullback.condition).symm =
        pullback.lift y.1 x.1 (y.2.trans x.2.symm) :=
      pullback.hom_ext (by rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, pullback.lift_snd])
        (by rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, pullback.lift_fst])
    rw [← h, Category.assoc, Hc]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_mul_assoc_comm_and_act_identities_of_forall_comp_eq_of_tower_of_forall_isPullback
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_mul_assoc_comm_and_act_identities_of_forall_comp_eq_of_tower_of_forall_isPullback (solution)
