-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_inv_act_forall_comp_eq_of_tower_of_forall_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/7c7770ef-cf5e-554a-afba-3a8f026a6488

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Theorems.Thm_AlgebraicGeometry_exists_hom_comp_eq_forall_pullback_fst_comp_eq_of_forall_truncation_of_isFinite_proj_of_isAdicComplete
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_inv_act_forall_comp_eq_of_tower_of_forall_isPullback
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

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace S2Mul

theorem mul_coe_congr {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of S)} (ht : t₁ = t₂)
    (P₁ Q₁ : SchemeHomOver t₁ f) (P₂ Q₂ : SchemeHomOver t₂ f) (hP : P₁.1 = P₂.1) (hQ : Q₁.1 = Q₂.1) :
    (L.mul t₁ P₁ Q₁).1 = (L.mul t₂ P₂ Q₂).1 := by
  subst ht
  rw [Subtype.ext hP, Subtype.ext hQ]

theorem mul_coe_comp {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    {T T' : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (ψ : T' ⟶ T) (P Q : SchemeHomOver t f) :
    ψ ≫ (L.mul t P Q).1 =
      (L.mul (ψ ≫ t) ⟨ψ ≫ P.1, by rw [Category.assoc, P.2]⟩ ⟨ψ ≫ Q.1, by rw [Category.assoc, Q.2]⟩).1 := by
  have h := congrArg Subtype.val (L.mul_natural t (ψ ≫ t) ψ rfl P Q)
  simp only [schemeHomOverComp_coe] at h
  rw [h]
  rfl

section trunc

variable (R : Type) [CommRing R] [IsLocalRing R]

noncomputable abbrev sR (n : ℕ) :
    Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1))) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1))))

variable (π : ∀ n : ℕ, (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1 + 1)) →+* (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1)))
  (hπ : ∀ n, (π n).comp (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1 + 1))) =
    Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1)))

noncomputable abbrev tR (n : ℕ) :
    Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1))) ⟶
      Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1 + 1))) :=
  Spec.map (CommRingCat.ofHom (π n))

include hπ in
theorem tR_sR (n : ℕ) : tR R π n ≫ sR R (n + 1) = sR R n := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hπ]

private noncomputable def _root_.S2Mul.trans {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) (n : ℕ) :
    pullback f (sR R n) ⟶ pullback f (sR R (n + 1)) :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ tR R π n)
    (by rw [Category.assoc, tR_sR R π hπ, pullback.condition])

p2m_export "S2Mul" "trans"
theorem trans_fst {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) (n : ℕ) :
    trans R π hπ f n ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _

theorem trans_snd {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) (n : ℕ) :
    trans R π hπ f n ≫ pullback.snd _ _ = pullback.snd _ _ ≫ tR R π n := pullback.lift_snd _ _ _

end trunc

section edata

variable {R : Type} [CommRing R] [IsLocalRing R] {Z : Scheme.{0}} (fZ : Z ⟶ Spec (CommRingCat.of R)) (n : ℕ)
  {A : Scheme.{0}} (fA : A ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1))))
  (L : RelativeGroupLaw (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1)) fA) (j : A ⟶ Z)
  (h : CategoryTheory.IsPullback j fA fZ (sR R n))

noncomputable def P₁ : pullback (pullback.fst fZ fZ ≫ fZ) (sR R n) ⟶ A :=
  h.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _) (by rw [Category.assoc]; exact pullback.condition)

noncomputable def P₂ : pullback (pullback.fst fZ fZ ≫ fZ) (sR R n) ⟶ A :=
  h.lift (pullback.fst _ _ ≫ pullback.snd _ _) (pullback.snd _ _)
    (by
      have hc : pullback.fst fZ fZ ≫ fZ = pullback.snd fZ fZ ≫ fZ := pullback.condition
      rw [Category.assoc, ← hc]; exact pullback.condition)

theorem P₁_j : P₁ fZ n fA j h ≫ j = pullback.fst _ _ ≫ pullback.fst _ _ := IsPullback.lift_fst _ _ _ _
theorem P₁_f : P₁ fZ n fA j h ≫ fA = pullback.snd _ _ := IsPullback.lift_snd _ _ _ _
theorem P₂_j : P₂ fZ n fA j h ≫ j = pullback.fst _ _ ≫ pullback.snd _ _ := IsPullback.lift_fst _ _ _ _
theorem P₂_f : P₂ fZ n fA j h ≫ fA = pullback.snd _ _ := IsPullback.lift_snd _ _ _ _

noncomputable def M : pullback (pullback.fst fZ fZ ≫ fZ) (sR R n) ⟶ A :=
  (L.mul (pullback.snd _ _) ⟨P₁ fZ n fA j h, P₁_f fZ n fA j h⟩ ⟨P₂ fZ n fA j h, P₂_f fZ n fA j h⟩).1

theorem M_f : M fZ n fA L j h ≫ fA = pullback.snd _ _ := (L.mul _ _ _).2

noncomputable def φ : pullback (pullback.fst fZ fZ ≫ fZ) (sR R n) ⟶ pullback fZ (sR R n) :=
  pullback.lift (M fZ n fA L j h ≫ j) (pullback.snd _ _) (by rw [Category.assoc, h.w, ← Category.assoc, M_f])

theorem φ_fst : φ fZ n fA L j h ≫ pullback.fst _ _ = M fZ n fA L j h ≫ j := pullback.lift_fst _ _ _
theorem φ_snd : φ fZ n fA L j h ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _

theorem lift_φ_fst {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1))))
    (P Q : SchemeHomOver t' fA) :
    pullback.lift (pullback.lift (P.1 ≫ j) (Q.1 ≫ j) (by rw [Category.assoc, h.w, ← Category.assoc, P.2, Category.assoc, h.w,
        ← Category.assoc, Q.2])) t'
        (by rw [pullback.lift_fst_assoc, Category.assoc, h.w, ← Category.assoc, P.2]) ≫
      φ fZ n fA L j h ≫ pullback.fst _ _ = (L.mul t' P Q).1 ≫ j := by
  rw [φ_fst, ← Category.assoc]
  congr 1
  rw [M, mul_coe_comp]
  refine mul_coe_congr L (pullback.lift_snd _ _ _) _ _ _ _ ?_ ?_
  · apply h.hom_ext
    · rw [Category.assoc, P₁_j, ← Category.assoc, pullback.lift_fst, pullback.lift_fst]
    · rw [Category.assoc, P₁_f, pullback.lift_snd, P.2]
  · apply h.hom_ext
    · rw [Category.assoc, P₂_j, ← Category.assoc, pullback.lift_fst, pullback.lift_snd]
    · rw [Category.assoc, P₂_f, pullback.lift_snd, Q.2]

end edata

section endo

variable {R : Type} [CommRing R] [IsLocalRing R] {Z : Scheme.{0}} (fZ : Z ⟶ Spec (CommRingCat.of R)) (n : ℕ)
  {A : Scheme.{0}} (fA : A ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1)))) (j : A ⟶ Z)
  (h : CategoryTheory.IsPullback j fA fZ (sR R n)) (ψ : A ⟶ A) (hψ : ψ ≫ fA = fA)

noncomputable def Pt : pullback fZ (sR R n) ⟶ A := h.lift (pullback.fst _ _) (pullback.snd _ _) pullback.condition

theorem Pt_j : Pt fZ n fA j h ≫ j = pullback.fst _ _ := IsPullback.lift_fst _ _ _ _
theorem Pt_f : Pt fZ n fA j h ≫ fA = pullback.snd _ _ := IsPullback.lift_snd _ _ _ _

noncomputable def φe : pullback fZ (sR R n) ⟶ pullback fZ (sR R n) :=
  pullback.lift (Pt fZ n fA j h ≫ ψ ≫ j) (pullback.snd _ _)
    (by
      simp only [Category.assoc]
      rw [h.w, ← Category.assoc ψ fA, hψ, ← Category.assoc, Pt_f])

theorem φe_fst : φe fZ n fA j h ψ hψ ≫ pullback.fst _ _ = Pt fZ n fA j h ≫ ψ ≫ j := pullback.lift_fst _ _ _
theorem φe_snd : φe fZ n fA j h ψ hψ ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _

theorem lift_φe_fst {T : Scheme.{0}} (x : T ⟶ A) :
    pullback.lift (x ≫ j) (x ≫ fA) (by rw [Category.assoc, h.w, Category.assoc]) ≫ φe fZ n fA j h ψ hψ ≫ pullback.fst _ _ =
      x ≫ ψ ≫ j := by
  rw [φe_fst, ← Category.assoc]
  congr 1
  apply h.hom_ext
  · rw [Category.assoc, Pt_j, pullback.lift_fst]
  · rw [Category.assoc, Pt_f, pullback.lift_snd]

end endo

section endocompat

variable {R : Type} [CommRing R] [IsLocalRing R]
  (π : ∀ n : ℕ, (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1 + 1)) →+* (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1)))
  (hπ : ∀ n, (π n).comp (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1 + 1))) =
    Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1)))
  {Z : Scheme.{0}} (fZ : Z ⟶ Spec (CommRingCat.of R)) (n : ℕ)
  {A : Scheme.{0}} (fA : A ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1)))) (j : A ⟶ Z)
  (h : CategoryTheory.IsPullback j fA fZ (sR R n)) (ψ : A ⟶ A) (hψ : ψ ≫ fA = fA)
  {A' : Scheme.{0}} (fA' : A' ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1 + 1)))) (j' : A' ⟶ Z)
  (h' : CategoryTheory.IsPullback j' fA' fZ (sR R (n + 1))) (ψ' : A' ⟶ A') (hψ' : ψ' ≫ fA' = fA')
  (tt : A ⟶ A') (htj : tt ≫ j' = j) (htf : tt ≫ fA' = fA ≫ Spec.map (CommRingCat.ofHom (π n)))
  (hcomp : ψ ≫ tt = tt ≫ ψ')

include hπ htj htf in
theorem trans_Pt : trans R π hπ fZ n ≫ Pt fZ (n + 1) fA' j' h' = Pt fZ n fA j h ≫ tt := by
  apply h'.hom_ext
  · rw [Category.assoc, Pt_j, trans_fst, Category.assoc, htj, Pt_j]
  · rw [Category.assoc, Pt_f, trans_snd, Category.assoc, htf, ← Category.assoc, Pt_f]

include hπ htj htf hcomp in
theorem trans_φe :
    trans R π hπ fZ n ≫ φe fZ (n + 1) fA' j' h' ψ' hψ' = φe fZ n fA j h ψ hψ ≫ trans R π hπ fZ n := by
  apply pullback.hom_ext
  · rw [Category.assoc, φe_fst, ← Category.assoc, trans_Pt π hπ fZ n fA j h fA' j' h' tt htj htf, Category.assoc,
      ← Category.assoc tt, ← hcomp, Category.assoc, htj, Category.assoc, trans_fst, φe_fst]
  · rw [Category.assoc, φe_snd, trans_snd, Category.assoc, trans_snd, ← Category.assoc, φe_snd]

end endocompat

section ptgroup

theorem inv_coe_congr {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of S)} (ht : t₁ = t₂)
    (P₁ : SchemeHomOver t₁ f) (P₂ : SchemeHomOver t₂ f) (hP : P₁.1 = P₂.1) :
    (L.inv t₁ P₁).1 = (L.inv t₂ P₂).1 := by
  subst ht
  rw [Subtype.ext hP]

theorem one_coe_congr {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of S)} (ht : t₁ = t₂) :
    (L.one t₁).1 = (L.one t₂).1 := by
  subst ht; rfl

theorem inv_natural {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    {T T' : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (t' : T' ⟶ Spec (CommRingCat.of S)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (x : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (L.inv t x) = L.inv t' (schemeHomOverComp ψ hψ x) := by
  have h1 : L.mul t' (schemeHomOverComp ψ hψ (L.inv t x)) (schemeHomOverComp ψ hψ x) = L.one t' := by
    rw [← L.mul_natural, L.inv_mul_cancel, L.one_natural]
  letI := L.pointGroup t'
  exact eq_inv_of_mul_eq_one_left h1

theorem inv_coe_eq_comp {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver t f) :
    (L.inv t x).1 = x.1 ≫ (L.inv f ⟨𝟙 A, Category.id_comp _⟩).1 := by
  have h := congrArg Subtype.val (inv_natural L f t x.1 x.2 ⟨𝟙 A, Category.id_comp _⟩)
  rw [schemeHomOverComp_coe] at h
  rw [h]
  exact inv_coe_congr L rfl _ _ (by rw [schemeHomOverComp_coe, Category.comp_id])

variable {S S' : Type} [CommRing S] [CommRing S'] {A A' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
  {f' : A' ⟶ Spec (CommRingCat.of S')} (L : RelativeGroupLaw S f) (L' : RelativeGroupLaw S' f')
  (σ : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of S')) (g : A ⟶ A') (hg : g ≫ f' = f ≫ σ)
  (hmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
    (L.mul t P Q).1 ≫ g =
      (L'.mul (t ≫ σ) ⟨P.1 ≫ g, by rw [Category.assoc, hg, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ g, by rw [Category.assoc, hg, ← Category.assoc, Q.2]⟩).1)

include hmul in

theorem one_comp_hom {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) : (L.one t).1 ≫ g = (L'.one (t ≫ σ)).1 := by
  let u : SchemeHomOver (t ≫ σ) f' := ⟨(L.one t).1 ≫ g, by rw [Category.assoc, hg, ← Category.assoc, (L.one t).2]⟩
  have h1 : L'.mul (t ≫ σ) u u = u := by
    apply Subtype.ext
    show (L'.mul (t ≫ σ) u u).1 = (L.one t).1 ≫ g
    rw [← L.one_mul t (L.one t), hmul]
  letI := L'.pointGroup (t ≫ σ)
  have h2 : u = 1 := mul_left_cancel (a := u) (h1.trans (mul_one u).symm)
  exact congrArg Subtype.val h2

include hmul in

theorem inv_comp_hom {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t f) :
    (L.inv t P).1 ≫ g =
      (L'.inv (t ≫ σ) ⟨P.1 ≫ g, by rw [Category.assoc, hg, ← Category.assoc, P.2]⟩).1 := by
  let v : SchemeHomOver (t ≫ σ) f' := ⟨(L.inv t P).1 ≫ g, by rw [Category.assoc, hg, ← Category.assoc, (L.inv t P).2]⟩
  let p : SchemeHomOver (t ≫ σ) f' := ⟨P.1 ≫ g, by rw [Category.assoc, hg, ← Category.assoc, P.2]⟩
  have h1 : L'.mul (t ≫ σ) v p = L'.one (t ≫ σ) := by
    apply Subtype.ext
    show (L'.mul (t ≫ σ) v p).1 = (L'.one (t ≫ σ)).1
    rw [← one_comp_hom L L' σ g hg hmul t, ← L.inv_mul_cancel t P, hmul]
  letI := L'.pointGroup (t ≫ σ)
  have h2 : v = p⁻¹ := eq_inv_of_mul_eq_one_left h1
  exact congrArg Subtype.val h2

end ptgroup

end S2Mul

open S2Mul in
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
    ∃ (ι : Z ⟶ Z) (hι : ι ≫ (G ≫ ProjSpace.π R r) = (G ≫ ProjSpace.π R r)) (act : ↥Λ → (Z ⟶ Z)) (act_over : ∀ x : ↥Λ, act x ≫ (G ≫ ProjSpace.π R r) = (G ≫ ProjSpace.π R r)),
      (∀ (n : ℕ) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1))))
        (P : SchemeHomOver t' (E n).f),
        ((E n).L.inv t' P).1 ≫ jz n = (P.1 ≫ jz n) ≫ ι) ∧
      (∀ (n : ℕ) (x : ↥Λ), (E n).act x ≫ jz n = jz n ≫ act x) := by
  classical

  have alg : ∀ (ψ : ∀ n : ℕ, (E n).A ⟶ (E n).A) (hψ : ∀ n, ψ n ≫ (E n).f = (E n).f)
      (hc : ∀ n, ψ n ≫ t n = t n ≫ ψ (n + 1)),
      ∃ Ψ : Z ⟶ Z, Ψ ≫ (G ≫ ProjSpace.π R r) = (G ≫ ProjSpace.π R r) ∧ ∀ n, ψ n ≫ jz n = jz n ≫ Ψ := by
    intro ψ hψ hc
    obtain ⟨F, hF, hFn, -⟩ :=
      AlgebraicGeometry.exists_hom_comp_eq_forall_pullback_fst_comp_eq_of_forall_truncation_of_isFinite_proj_of_isAdicComplete
        R (IsLocalRing.maximalIdeal R) Z (G ≫ ProjSpace.π R r) r G rfl Z (G ≫ ProjSpace.π R r) r G rfl
        (sR R) (fun n => by rw [Ideal.Quotient.algebraMap_eq]) (tR R π) (tR_sR R π hπ)
        (trans R π hπ (G ≫ ProjSpace.π R r)) (trans_fst R π hπ _) (trans_snd R π hπ _)
        (trans R π hπ (G ≫ ProjSpace.π R r)) (trans_fst R π hπ _) (trans_snd R π hπ _)
        (fun n => φe (G ≫ ProjSpace.π R r) n (E n).f (jz n) (hZ.2 n) (ψ n) (hψ n))
        (fun n => φe_snd (G ≫ ProjSpace.π R r) n (E n).f (jz n) (hZ.2 n) (ψ n) (hψ n))
        (fun n => by
          obtain ⟨hg, -, -, -⟩ := ht n
          exact trans_φe π hπ (G ≫ ProjSpace.π R r) n (E n).f (jz n) (hZ.2 n) (ψ n) (hψ n) (E (n + 1)).f (jz (n + 1)) (hZ.2 (n + 1))
            (ψ (n + 1)) (hψ (n + 1)) (t n) (hZ.1 n) hg.w (hc n))
    refine ⟨F, hF, fun n => ?_⟩
    have hn : pullback.fst _ _ ≫ F = φe (G ≫ ProjSpace.π R r) n (E n).f (jz n) (hZ.2 n) (ψ n) (hψ n) ≫ pullback.fst _ _ := hFn n
    have h1 := lift_φe_fst (G ≫ ProjSpace.π R r) n (E n).f (jz n) (hZ.2 n) (ψ n) (hψ n) (𝟙 _)
    rw [← hn, pullback.lift_fst_assoc, Category.id_comp, Category.id_comp] at h1
    exact h1.symm

  obtain ⟨ι, hι, hιn⟩ := alg (fun n => ((E n).L.inv (E n).f ⟨𝟙 _, Category.id_comp _⟩).1) (fun n => ((E n).L.inv _ _).2)
    (fun n => by
      obtain ⟨hg, hmul, -, -⟩ := ht n
      rw [inv_comp_hom (E n).L (E (n + 1)).L (Spec.map (CommRingCat.ofHom (π n))) (t n) hg.w hmul,
        inv_coe_eq_comp (E (n + 1)).L]
      show (𝟙 _ ≫ t n) ≫ _ = t n ≫ _
      rw [Category.id_comp])

  have hact : ∀ x : ↥Λ, ∃ Ψ : Z ⟶ Z, Ψ ≫ (G ≫ ProjSpace.π R r) = (G ≫ ProjSpace.π R r) ∧ ∀ n, (E n).act x ≫ jz n = jz n ≫ Ψ := fun x =>
    alg (fun n => (E n).act x) (fun n => (E n).act_over x)
      (fun n => by obtain ⟨hg, -, hact, -⟩ := ht n; exact hact x)
  choose act hact_over hact_n using hact
  refine ⟨ι, hι, act, hact_over, fun n T t' P => ?_, fun n x => hact_n x n⟩
  have hιn' : ((E n).L.inv (E n).f ⟨𝟙 _, Category.id_comp _⟩).1 ≫ jz n = jz n ≫ ι := hιn n
  rw [inv_coe_eq_comp (E n).L t' P, Category.assoc, hιn', Category.assoc]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_inv_act_forall_comp_eq_of_tower_of_forall_isPullback
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_inv_act_forall_comp_eq_of_tower_of_forall_isPullback (solution)
