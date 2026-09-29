-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_fg_subalgebra_abelianScheme_act_level_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/77fe9af4-aa3a-5b79-a59c-2f8a74e96843

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_abelianScheme_act_levelData_isPullback
import Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation
import Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_pullback_fst_comp_eq_of_locallyOfFiniteType
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_abelianScheme_act_level_isPullback
p2m_attr_erase "instance" "IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing"
p2m_attr_erase "instance" "TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec"
p2m_attr_erase "simp" "TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq"
p2m_attr_erase "simp" "DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace PkgDesc18

universe u

variable {R : Type u} [CommRing R]

abbrev ι (A : Type u) [CommRing A] [Algebra R A] : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R A))

theorem specMap_comp_ι {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] (φ : A →ₐ[R] B) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ ι (R := R) A = ι B := by
  rw [ι, ι, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact φ.comp_algebraMap

variable {X Y Z : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))

def q {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] (φ : A →ₐ[R] B) :
    pullback f (ι B) ⟶ pullback f (ι A) :=
  pullback.lift (pullback.fst f (ι B)) (pullback.snd f (ι B) ≫ Spec.map (CommRingCat.ofHom φ.toRingHom))
    (by rw [Category.assoc, specMap_comp_ι, pullback.condition])

@[scoped simp] theorem q_fst {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] (φ : A →ₐ[R] B) :
    q f φ ≫ pullback.fst f (ι A) = pullback.fst f (ι B) := pullback.lift_fst _ _ _

@[scoped simp] theorem q_snd {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] (φ : A →ₐ[R] B) :
    q f φ ≫ pullback.snd f (ι A) = pullback.snd f (ι B) ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) :=
  pullback.lift_snd _ _ _

theorem q_comp {A B C : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] [CommRing C] [Algebra R C]
    (φ : A →ₐ[R] B) (ψ : B →ₐ[R] C) : q f ψ ≫ q f φ = q f (ψ.comp φ) := by
  apply pullback.hom_ext
  · simp only [q, Category.assoc, pullback.lift_fst]
  · simp only [q, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
    rw [← Spec.map_comp]; rfl

def restage {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] (φ : A →ₐ[R] B)
    (a : pullback f (ι A) ⟶ pullback g (ι A)) (ha : a ≫ pullback.snd g (ι A) = pullback.snd f (ι A)) :
    pullback f (ι B) ⟶ pullback g (ι B) :=
  pullback.lift (q f φ ≫ a ≫ pullback.fst g (ι A)) (pullback.snd f (ι B))
    (by rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc a, ha, ← Category.assoc, q_snd,
      Category.assoc, specMap_comp_ι])

@[scoped simp] theorem restage_fst {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] (φ : A →ₐ[R] B)
    (a : pullback f (ι A) ⟶ pullback g (ι A)) (ha : a ≫ pullback.snd g (ι A) = pullback.snd f (ι A)) :
    restage f g φ a ha ≫ pullback.fst g (ι B) = q f φ ≫ a ≫ pullback.fst g (ι A) := pullback.lift_fst _ _ _

@[scoped simp] theorem restage_snd {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] (φ : A →ₐ[R] B)
    (a : pullback f (ι A) ⟶ pullback g (ι A)) (ha : a ≫ pullback.snd g (ι A) = pullback.snd f (ι A)) :
    restage f g φ a ha ≫ pullback.snd g (ι B) = pullback.snd f (ι B) := pullback.lift_snd _ _ _

theorem restage_q {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] (φ : A →ₐ[R] B)
    (a : pullback f (ι A) ⟶ pullback g (ι A)) (ha : a ≫ pullback.snd g (ι A) = pullback.snd f (ι A)) :
    restage f g φ a ha ≫ q g φ = q f φ ≫ a := by
  apply pullback.hom_ext
  · simp only [Category.assoc, q_fst, restage_fst]
  · rw [Category.assoc, q_snd, ← Category.assoc, restage_snd, Category.assoc, ha, q_snd]

theorem eq_restage {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] (φ : A →ₐ[R] B)
    (a : pullback f (ι A) ⟶ pullback g (ι A)) (ha : a ≫ pullback.snd g (ι A) = pullback.snd f (ι A))
    (α : pullback f (ι B) ⟶ pullback g (ι B)) (hα : α ≫ pullback.snd g (ι B) = pullback.snd f (ι B))
    (h : α ≫ q g φ = q f φ ≫ a) : α = restage f g φ a ha := by
  apply pullback.hom_ext
  · rw [restage_fst, ← Category.assoc, ← h, Category.assoc, q_fst]
  · rw [restage_snd, hα]

theorem restage_id {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] (φ : A →ₐ[R] B) :
    restage f f φ (𝟙 _) (Category.id_comp _) = 𝟙 _ :=
  (eq_restage f f φ _ _ _ (Category.id_comp _) (by simp)).symm

theorem restage_comp (h : Z ⟶ Spec (CommRingCat.of R)) {A B : Type u} [CommRing A] [Algebra R A] [CommRing B]
    [Algebra R B] (φ : A →ₐ[R] B)
    (a : pullback f (ι A) ⟶ pullback g (ι A)) (ha : a ≫ pullback.snd g (ι A) = pullback.snd f (ι A))
    (b : pullback g (ι A) ⟶ pullback h (ι A)) (hb : b ≫ pullback.snd h (ι A) = pullback.snd g (ι A)) :
    restage f h φ (a ≫ b) (by rw [Category.assoc, hb, ha]) = restage f g φ a ha ≫ restage g h φ b hb :=
  (eq_restage f h φ _ _ _ (by rw [Category.assoc, restage_snd, restage_snd])
    (by rw [Category.assoc, restage_q, ← Category.assoc, restage_q, Category.assoc])).symm

theorem restage_restage {A B C : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] [CommRing C]
    [Algebra R C] (φ : A →ₐ[R] B) (ψ : B →ₐ[R] C)
    (a : pullback f (ι A) ⟶ pullback g (ι A)) (ha : a ≫ pullback.snd g (ι A) = pullback.snd f (ι A)) :
    restage f g ψ (restage f g φ a ha) (restage_snd f g φ a ha) = restage f g (ψ.comp φ) a ha :=
  eq_restage f g (ψ.comp φ) _ _ _ (restage_snd _ _ _ _ _)
    (by rw [← q_comp, ← q_comp, ← Category.assoc, restage_q, Category.assoc, restage_q, Category.assoc])

theorem exists_fg_restage_eq {L : Type u} [CommRing L] [Algebra R L] (T₁ : Subalgebra R L) (hT₁ : T₁.FG)
    [QuasiCompact f] [LocallyOfFiniteType g]
    (a b : pullback f (ι ↥T₁) ⟶ pullback g (ι ↥T₁))
    (ha : a ≫ pullback.snd g (ι ↥T₁) = pullback.snd f (ι ↥T₁)) (hb : b ≫ pullback.snd g (ι ↥T₁) = pullback.snd f (ι ↥T₁))
    (hab : q f T₁.val ≫ a = q f T₁.val ≫ b) (s : Finset L) :
    ∃ (T₂ : Subalgebra R L) (h₁₂ : T₁ ≤ T₂), T₂.FG ∧ (↑s : Set L) ⊆ T₂ ∧
      restage f g (Subalgebra.inclusion h₁₂) a ha = restage f g (Subalgebra.inclusion h₁₂) b hb := by
  classical

  have hsc : Spec.map (CommRingCat.ofHom (algebraMap ↥T₁ L)) ≫ ι (R := R) ↥T₁ = ι L := specMap_comp_ι T₁.val
  let D := pullback (pullback.snd f (ι ↥T₁)) (Spec.map (CommRingCat.ofHom (algebraMap ↥T₁ L)))
  let κ : D ⟶ pullback f (ι L) :=
    pullback.lift (pullback.fst _ _ ≫ pullback.fst f (ι ↥T₁)) (pullback.snd _ _)
      (by rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc, hsc])
  have hκ : pullback.fst (pullback.snd f (ι ↥T₁)) (Spec.map (CommRingCat.ofHom (algebraMap ↥T₁ L))) = κ ≫ q f T₁.val := by
    apply pullback.hom_ext
    · simp only [Category.assoc, q_fst, κ, pullback.lift_fst]
    · simp only [Category.assoc, q_snd, κ, pullback.lift_snd_assoc]
      exact pullback.condition
  have hab' : pullback.fst (pullback.snd f (ι ↥T₁)) (Spec.map (CommRingCat.ofHom (algebraMap ↥T₁ L))) ≫ a =
      pullback.fst (pullback.snd f (ι ↥T₁)) (Spec.map (CommRingCat.ofHom (algebraMap ↥T₁ L))) ≫ b := by
    rw [hκ, Category.assoc, hab, Category.assoc]
  obtain ⟨T₂', hT₂'fg, hsT₂', heq⟩ :=
    AlgebraicGeometry.exists_fg_subalgebra_pullback_fst_comp_eq_of_locallyOfFiniteType
      (pullback.snd f (ι ↥T₁)) (pullback.snd g (ι ↥T₁)) a b ha hb hab' s

  refine ⟨T₂'.restrictScalars R, fun x hx => ?_, ?_, hsT₂', ?_⟩
  · show x ∈ T₂'
    have : algebraMap ↥T₁ L ⟨x, hx⟩ ∈ T₂' := T₂'.algebraMap_mem _
    exact this
  · have h1 : (⊤ : Subalgebra R ↥T₁).FG := (Subalgebra.fg_top T₁).2 hT₁
    have h2 : (⊤ : Subalgebra ↥T₁ ↥T₂').FG := (Subalgebra.fg_top T₂').2 hT₂'fg
    have h3 : (⊤ : Subalgebra R ↥T₂').FG := Algebra.fg_trans' h1 h2
    have h4 : T₂'.restrictScalars R = (⊤ : Subalgebra R ↥T₂').map (T₂'.val.restrictScalars R) := by
      ext x
      rw [Subalgebra.mem_restrictScalars, Subalgebra.mem_map]
      constructor
      · intro hx'; exact ⟨⟨x, hx'⟩, Algebra.mem_top, rfl⟩
      · rintro ⟨y, -, rfl⟩; exact y.2
    rw [h4]; exact h3.map _
  ·
    set h₁₂ : T₁ ≤ T₂'.restrictScalars R := fun x hx =>
      show x ∈ T₂' from (T₂'.algebraMap_mem (⟨x, hx⟩ : ↥T₁) : algebraMap ↥T₁ L ⟨x, hx⟩ ∈ T₂') with hh
    let j : ↥(T₂'.restrictScalars R) →+* ↥T₂' :=
      { toFun := fun x => ⟨x.1, x.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl,
        map_add' := fun _ _ => rfl }
    have hj : (CommRingCat.ofHom (algebraMap ↥T₁ ↥T₂')) ≫ CommRingCat.ofHom j =
        CommRingCat.ofHom (Subalgebra.inclusion h₁₂).toRingHom := by
      rw [← CommRingCat.ofHom_comp]; rfl
    let r : pullback f (ι ↥(T₂'.restrictScalars R)) ⟶
        pullback (pullback.snd f (ι ↥T₁)) (Spec.map (CommRingCat.ofHom (algebraMap ↥T₁ ↥T₂'))) :=
      pullback.lift (q f (Subalgebra.inclusion h₁₂)) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom j))
        (by rw [q_snd, Category.assoc, ← Spec.map_comp]; erw [hj])
    have hr : r ≫ pullback.fst _ _ = q f (Subalgebra.inclusion h₁₂) := pullback.lift_fst _ _ _
    apply pullback.hom_ext
    · rw [restage_fst, restage_fst, ← hr, Category.assoc, Category.assoc, reassoc_of% heq]
    · rw [restage_snd, restage_snd]

end PkgDesc18
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_abelianScheme_act_level_isPullback.PkgDesc18"

attribute [reassoc] PkgDesc18.q_fst PkgDesc18.q_snd

namespace LevDesc21

open PkgDesc18 GoodReductionJacobian CerednikDrinfeld.QM
open NeronModelInfra (SchemeHomOver)

universe u

section Group

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)

theorem eq_one_of_mul_self {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f)
    (h : G.mul t x x = x) : x = G.one t := by
  calc x = G.mul t (G.one t) x := (G.one_mul t x).symm
    _ = G.mul t (G.mul t (G.inv t x) x) x := by rw [G.inv_mul_cancel]
    _ = G.mul t (G.inv t x) (G.mul t x x) := G.mul_assoc t _ _ _
    _ = G.mul t (G.inv t x) x := by rw [h]
    _ = G.one t := G.inv_mul_cancel t x

theorem eq_inv_of_mul_eq_one {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f)
    (h : G.mul t x y = G.one t) : y = G.inv t x := by
  calc y = G.mul t (G.one t) y := (G.one_mul t y).symm
    _ = G.mul t (G.mul t (G.inv t x) x) y := by rw [G.inv_mul_cancel]
    _ = G.mul t (G.inv t x) (G.mul t x y) := G.mul_assoc t _ _ _
    _ = G.mul t (G.inv t x) (G.one t) := by rw [h]
    _ = G.inv t x := G.mul_one t _

theorem inv_natural {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (G.inv t x) =
      G.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by
  apply eq_inv_of_mul_eq_one
  rw [← G.mul_natural, G.mul_inv_cancel, G.one_natural]

theorem nsmul_natural {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (n : ℕ) (x : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (nsmulPt G t n x) =
      nsmulPt G t' n (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by
  induction n with
  | zero => exact G.one_natural t t' ψ hψ
  | succ n ih => simp only [nsmulPt]; rw [G.mul_natural, ih]

end Group
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_abelianScheme_act_level_isPullback.PkgDesc18"

section Yoneda

variable {R : Type u} [CommRing R] {A C : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)
  (lev : C ⟶ A)

def uPt : SchemeHomOver (lev ≫ f) f := ⟨lev, rfl⟩

def uPt₁ : SchemeHomOver (pullback.fst (lev ≫ f) (lev ≫ f) ≫ lev ≫ f) f :=
  ⟨pullback.fst (lev ≫ f) (lev ≫ f) ≫ lev, Category.assoc _ _ _⟩

def uPt₂ : SchemeHomOver (pullback.fst (lev ≫ f) (lev ≫ f) ≫ lev ≫ f) f :=
  ⟨pullback.snd (lev ≫ f) (lev ≫ f) ≫ lev, by rw [Category.assoc]; exact pullback.condition.symm⟩

@[scoped simp] theorem uPt_coe : (uPt lev (f := f)).1 = lev := rfl
@[scoped simp] theorem uPt₁_coe : (uPt₁ lev (f := f)).1 = pullback.fst (lev ≫ f) (lev ≫ f) ≫ lev := rfl
@[scoped simp] theorem uPt₂_coe : (uPt₂ lev (f := f)).1 = pullback.snd (lev ≫ f) (lev ≫ f) ≫ lev := rfl

theorem mul_coe_eq {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (P Q : SchemeHomOver t f)
    (ψ : T ⟶ pullback (lev ≫ f) (lev ≫ f))
    (hP : ψ ≫ pullback.fst _ _ ≫ lev = P.1) (hQ : ψ ≫ pullback.snd _ _ ≫ lev = Q.1) :
    (G.mul t P Q).1 = ψ ≫ (G.mul _ (uPt₁ lev) (uPt₂ lev)).1 := by
  have hψ : ψ ≫ (pullback.fst (lev ≫ f) (lev ≫ f) ≫ lev ≫ f) = t := by
    rw [reassoc_of% hP]; exact P.2
  have h := congrArg Subtype.val (G.mul_natural _ t ψ hψ (uPt₁ lev) (uPt₂ lev))
  rw [schemeHomOverComp_coe] at h
  have hP' : P = GoodReductionJacobian.schemeHomOverComp ψ hψ (uPt₁ lev) :=
    Subtype.ext (by rw [schemeHomOverComp_coe, uPt₁_coe]; exact hP.symm)
  have hQ' : Q = GoodReductionJacobian.schemeHomOverComp ψ hψ (uPt₂ lev) :=
    Subtype.ext (by rw [schemeHomOverComp_coe, uPt₂_coe]; exact hQ.symm)
  rw [h, hP', hQ']

theorem inv_coe_eq {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f)
    (P₀ : T ⟶ C) (hP : P₀ ≫ lev = P.1) :
    (G.inv t P).1 = P₀ ≫ (G.inv _ (uPt lev)).1 := by
  have hψ : P₀ ≫ (lev ≫ f) = t := by rw [← Category.assoc, hP]; exact P.2
  have h := congrArg Subtype.val (inv_natural G _ t P₀ hψ (uPt lev))
  rw [schemeHomOverComp_coe] at h
  have hP' : P = GoodReductionJacobian.schemeHomOverComp P₀ hψ (uPt lev) :=
    Subtype.ext (by rw [schemeHomOverComp_coe, uPt_coe]; exact hP.symm)
  rw [h, hP']

theorem one_coe_eq {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    (G.one t).1 = t ≫ (G.one (𝟙 _)).1 := by
  have h := congrArg Subtype.val (G.one_natural (𝟙 _) t t (Category.comp_id t))
  rw [schemeHomOverComp_coe] at h
  exact h.symm

theorem one_coe_eq' {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P₀ : T ⟶ C) (h₀ : P₀ ≫ lev ≫ f = t) :
    (G.one t).1 = P₀ ≫ (G.one (lev ≫ f)).1 := by
  have h := congrArg Subtype.val (G.one_natural (lev ≫ f) t P₀ h₀)
  rw [schemeHomOverComp_coe] at h
  exact h.symm

theorem nsmul_coe_eq {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f)
    (P₀ : T ⟶ C) (hP : P₀ ≫ lev = P.1) (n : ℕ) :
    (nsmulPt G t n P).1 = P₀ ≫ (nsmulPt G _ n (uPt lev)).1 := by
  have hψ : P₀ ≫ (lev ≫ f) = t := by rw [← Category.assoc, hP]; exact P.2
  have h := congrArg Subtype.val (nsmul_natural G _ t P₀ hψ n (uPt lev))
  rw [schemeHomOverComp_coe] at h
  have hP' : P = GoodReductionJacobian.schemeHomOverComp P₀ hψ (uPt lev) :=
    Subtype.ext (by rw [schemeHomOverComp_coe, uPt_coe]; exact hP.symm)
  rw [h, hP']

variable {B : Scheme.{u}} (j : B ⟶ Spec (CommRingCat.of R))

theorem levSub_of
    (φm : pullback (pullback.fst (lev ≫ f) (lev ≫ f) ≫ lev ≫ f) j ⟶ C)
    (hφm : φm ≫ lev = pullback.fst _ j ≫ (G.mul _ (uPt₁ lev) (uPt₂ lev)).1)
    (φi : pullback (lev ≫ f) j ⟶ C) (hφi : φi ≫ lev = pullback.fst _ j ≫ (G.inv _ (uPt lev)).1)
    {T : Scheme.{u}} (t : T ⟶ B) (P Q : SchemeHomOver (t ≫ j) f)
    (hP : FactorsThrough lev P) (hQ : FactorsThrough lev Q) :
    FactorsThrough lev (G.mul _ P Q) ∧ FactorsThrough lev (G.inv _ P) := by
  obtain ⟨P₀, hP₀⟩ := hP
  obtain ⟨Q₀, hQ₀⟩ := hQ
  have hPf : P₀ ≫ lev ≫ f = t ≫ j := by rw [← Category.assoc, hP₀]; exact P.2
  have hQf : Q₀ ≫ lev ≫ f = t ≫ j := by rw [← Category.assoc, hQ₀]; exact Q.2
  refine ⟨⟨pullback.lift (pullback.lift P₀ Q₀ (hPf.trans hQf.symm)) t
      (by rw [pullback.lift_fst_assoc, hPf]) ≫ φm, ?_⟩, ⟨pullback.lift P₀ t hPf ≫ φi, ?_⟩⟩
  · rw [Category.assoc, hφm, pullback.lift_fst_assoc,
      mul_coe_eq G lev P Q (pullback.lift P₀ Q₀ (hPf.trans hQf.symm)) (by rw [pullback.lift_fst_assoc, hP₀])
        (by rw [pullback.lift_snd_assoc, hQ₀])]
  · rw [Category.assoc, hφi, pullback.lift_fst_assoc, inv_coe_eq G lev P P₀ hP₀]

theorem levOne_of (φ : pullback (𝟙 (Spec (CommRingCat.of R))) j ⟶ C)
    (hφ : φ ≫ lev = pullback.fst _ j ≫ (G.one (𝟙 _)).1) {T : Scheme.{u}} (t : T ⟶ B) :
    FactorsThrough lev (G.one (t ≫ j)) :=
  ⟨pullback.lift (t ≫ j) t (Category.comp_id _) ≫ φ, by
    rw [Category.assoc, hφ, pullback.lift_fst_assoc, one_coe_eq G (t ≫ j)]⟩

theorem levTorsion_of (n : ℕ)
    (h : pullback.fst (lev ≫ f) j ≫ (nsmulPt G _ n (uPt lev)).1 = pullback.fst (lev ≫ f) j ≫ (G.one (lev ≫ f)).1)
    {T : Scheme.{u}} (t : T ⟶ B) (P : SchemeHomOver (t ≫ j) f) (hP : FactorsThrough lev P) :
    nsmulPt G _ n P = G.one _ := by
  obtain ⟨P₀, hP₀⟩ := hP
  have hPf : P₀ ≫ lev ≫ f = t ≫ j := by rw [← Category.assoc, hP₀]; exact P.2
  apply Subtype.ext
  rw [nsmul_coe_eq G lev P P₀ hP₀ n, one_coe_eq' G lev (t ≫ j) P₀ hPf, ← pullback.lift_fst P₀ t hPf,
    Category.assoc, Category.assoc, h]

include G in
theorem levStable_of (φ : A ⟶ A) (hφ : φ ≫ f = f) (σ : pullback (lev ≫ f) j ⟶ C)
    (hσ : σ ≫ lev = pullback.fst (lev ≫ f) j ≫ lev ≫ φ) {T : Scheme.{u}} (t : T ⟶ B) (P : SchemeHomOver (t ≫ j) f)
    (hP : FactorsThrough lev P) : FactorsThrough lev (pushPt φ hφ P) := by
  obtain ⟨P₀, hP₀⟩ := hP
  have hPf : P₀ ≫ lev ≫ f = t ≫ j := by rw [← Category.assoc, hP₀]; exact P.2
  exact ⟨pullback.lift P₀ t hPf ≫ σ, by
    rw [Category.assoc, hσ, pullback.lift_fst_assoc, mapPt_coe, ← hP₀, Category.assoc]⟩

theorem factor_mul_of
    (H : ∀ {T : Scheme.{u}} (t : T ⟶ B) (P Q : SchemeHomOver (t ≫ j) f),
      FactorsThrough lev P → FactorsThrough lev Q → FactorsThrough lev (G.mul _ P Q)) :
    ∃ φm : pullback (pullback.fst (lev ≫ f) (lev ≫ f) ≫ lev ≫ f) j ⟶ C,
      φm ≫ lev = pullback.fst _ j ≫ (G.mul _ (uPt₁ lev) (uPt₂ lev)).1 := by
  have c₁ : pullback.fst (pullback.fst (lev ≫ f) (lev ≫ f) ≫ lev ≫ f) j ≫ pullback.fst (lev ≫ f) (lev ≫ f) ≫ lev ≫ f =
      pullback.snd _ j ≫ j := pullback.condition
  have c₂ : pullback.fst (pullback.fst (lev ≫ f) (lev ≫ f) ≫ lev ≫ f) j ≫ pullback.snd (lev ≫ f) (lev ≫ f) ≫ lev ≫ f =
      pullback.snd _ j ≫ j := by
    rw [← c₁, ← (pullback.condition : pullback.fst (lev ≫ f) (lev ≫ f) ≫ lev ≫ f = _)]
  let P : SchemeHomOver (pullback.snd _ j ≫ j) f :=
    ⟨pullback.fst (pullback.fst (lev ≫ f) (lev ≫ f) ≫ lev ≫ f) j ≫ pullback.fst _ _ ≫ lev, by
      simp only [Category.assoc]; exact c₁⟩
  let Q : SchemeHomOver (pullback.snd _ j ≫ j) f :=
    ⟨pullback.fst (pullback.fst (lev ≫ f) (lev ≫ f) ≫ lev ≫ f) j ≫ pullback.snd _ _ ≫ lev, by
      simp only [Category.assoc]; exact c₂⟩
  obtain ⟨φ, hφ⟩ := H _ P Q ⟨pullback.fst _ j ≫ pullback.fst _ _, by simp only [Category.assoc]; rfl⟩
    ⟨pullback.fst _ j ≫ pullback.snd _ _, by simp only [Category.assoc]; rfl⟩
  exact ⟨φ, by rw [hφ, mul_coe_eq G lev P Q (pullback.fst _ j) rfl rfl]⟩

theorem factor_inv_of
    (H : ∀ {T : Scheme.{u}} (t : T ⟶ B) (P : SchemeHomOver (t ≫ j) f),
      FactorsThrough lev P → FactorsThrough lev (G.inv _ P)) :
    ∃ φi : pullback (lev ≫ f) j ⟶ C, φi ≫ lev = pullback.fst _ j ≫ (G.inv _ (uPt lev)).1 := by
  let P : SchemeHomOver (pullback.snd (lev ≫ f) j ≫ j) f :=
    ⟨pullback.fst (lev ≫ f) j ≫ lev, by rw [Category.assoc]; exact pullback.condition⟩
  obtain ⟨φ, hφ⟩ := H _ P ⟨pullback.fst _ j, rfl⟩
  exact ⟨φ, by rw [hφ, inv_coe_eq G lev P (pullback.fst _ j) rfl]⟩

theorem factor_one_of (H : ∀ {T : Scheme.{u}} (t : T ⟶ B), FactorsThrough lev (G.one (t ≫ j))) :
    ∃ φ : pullback (𝟙 (Spec (CommRingCat.of R))) j ⟶ C, φ ≫ lev = pullback.fst _ j ≫ (G.one (𝟙 _)).1 := by
  obtain ⟨φ, hφ⟩ := H (pullback.snd (𝟙 (Spec (CommRingCat.of R))) j)
  refine ⟨φ, ?_⟩
  rw [hφ, one_coe_eq G, ← (pullback.condition : pullback.fst (𝟙 (Spec (CommRingCat.of R))) j ≫ 𝟙 _ = _),
    Category.comp_id]

theorem eq_torsion_of (n : ℕ)
    (H : ∀ {T : Scheme.{u}} (t : T ⟶ B) (P : SchemeHomOver (t ≫ j) f),
      FactorsThrough lev P → nsmulPt G _ n P = G.one _) :
    pullback.fst (lev ≫ f) j ≫ (nsmulPt G _ n (uPt lev)).1 = pullback.fst (lev ≫ f) j ≫ (G.one (lev ≫ f)).1 := by
  let P : SchemeHomOver (pullback.snd (lev ≫ f) j ≫ j) f :=
    ⟨pullback.fst (lev ≫ f) j ≫ lev, by rw [Category.assoc]; exact pullback.condition⟩
  have h := congrArg Subtype.val (H _ P ⟨pullback.fst _ j, rfl⟩)
  rwa [nsmul_coe_eq G lev P (pullback.fst _ j) rfl, one_coe_eq' G lev _ (pullback.fst _ j) pullback.condition] at h

include G in
theorem factor_act_of (φ : A ⟶ A) (hφ : φ ≫ f = f)
    (H : ∀ {T : Scheme.{u}} (t : T ⟶ B) (P : SchemeHomOver (t ≫ j) f),
      FactorsThrough lev P → FactorsThrough lev (pushPt φ hφ P)) :
    ∃ σ : pullback (lev ≫ f) j ⟶ C, σ ≫ lev = pullback.fst (lev ≫ f) j ≫ lev ≫ φ := by
  let P : SchemeHomOver (pullback.snd (lev ≫ f) j ≫ j) f :=
    ⟨pullback.fst (lev ≫ f) j ≫ lev, by rw [Category.assoc]; exact pullback.condition⟩
  obtain ⟨σ, hσ⟩ := H _ P ⟨pullback.fst _ j, rfl⟩
  exact ⟨σ, by rw [hσ, mapPt_coe, Category.assoc]⟩

end Yoneda
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_abelianScheme_act_level_isPullback.PkgDesc18"

section Descend

variable {R : Type u} [CommRing R] {L : Type u} [CommRing L] [Algebra R L]

theorem factor_mono {X C A : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of R)) (lev : C ⟶ A) (m : X ⟶ A)
    {T T' : Subalgebra R L} (h : T ≤ T')
    (φ : pullback p (ι ↥T) ⟶ C) (hφ : φ ≫ lev = pullback.fst p (ι ↥T) ≫ m) :
    ∃ φ' : pullback p (ι ↥T') ⟶ C, φ' ≫ lev = pullback.fst p (ι ↥T') ≫ m :=
  ⟨q p (Subalgebra.inclusion h) ≫ φ, by rw [Category.assoc, hφ, q_fst_assoc]⟩

theorem eq_mono {X A : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of R)) (m m' : X ⟶ A)
    {T T' : Subalgebra R L} (h : T ≤ T')
    (he : pullback.fst p (ι ↥T) ≫ m = pullback.fst p (ι ↥T) ≫ m') :
    pullback.fst p (ι ↥T') ≫ m = pullback.fst p (ι ↥T') ≫ m' := by
  rw [← q_fst p (Subalgebra.inclusion h), Category.assoc, he, Category.assoc]

theorem exists_fg_factor {X C A : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of R)) (fA : A ⟶ Spec (CommRingCat.of R))
    (lev : C ⟶ A) (m : X ⟶ A) (hm : m ≫ fA = p)
    [QuasiCompact p] [QuasiSeparated p] [LocallyOfFinitePresentation (lev ≫ fA)] [LocallyOfFiniteType fA]
    (φ : pullback p (ι L) ⟶ C) (hφ : φ ≫ lev = pullback.fst p (ι L) ≫ m) (s : Finset L) :
    ∃ T : Subalgebra R L, T.FG ∧ (↑s : Set L) ⊆ T ∧
      ∃ φ₀ : pullback p (ι ↥T) ⟶ C, φ₀ ≫ lev = pullback.fst p (ι ↥T) ≫ m := by
  classical
  have hφf : φ ≫ lev ≫ fA = pullback.snd p (ι L) ≫ ι L := by
    rw [← Category.assoc, hφ, Category.assoc, hm]; exact pullback.condition
  obtain ⟨T₁, hT₁, -, g₀, hg₀, hcompat⟩ :=
    AlgebraicGeometry.exists_fg_subalgebra_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation
      (A₀ := R) (A := L) p (lev ≫ fA) (pullback.lift φ (pullback.snd p (ι L)) hφf) (pullback.lift_snd _ _ _) ∅
  have hc := hcompat (q p T₁.val) (q (lev ≫ fA) T₁.val) (q_fst _ _) (q_snd _ _) (q_fst _ _) (q_snd _ _)
  have ha' : (g₀ ≫ pullback.fst (lev ≫ fA) (ι ↥T₁) ≫ lev) ≫ fA = pullback.snd p (ι ↥T₁) ≫ ι ↥T₁ := by
    simp only [Category.assoc]
    rw [(pullback.condition : pullback.fst (lev ≫ fA) (ι ↥T₁) ≫ lev ≫ fA = _), ← Category.assoc, hg₀]
  have hb' : (pullback.fst p (ι ↥T₁) ≫ m) ≫ fA = pullback.snd p (ι ↥T₁) ≫ ι ↥T₁ := by
    rw [Category.assoc, hm]; exact pullback.condition
  obtain ⟨T₂, h₁₂, hT₂, hsT₂, heq⟩ := exists_fg_restage_eq p fA T₁ hT₁
    (pullback.lift (g₀ ≫ pullback.fst (lev ≫ fA) (ι ↥T₁) ≫ lev) (pullback.snd p (ι ↥T₁)) ha')
    (pullback.lift (pullback.fst p (ι ↥T₁) ≫ m) (pullback.snd p (ι ↥T₁)) hb')
    (pullback.lift_snd _ _ _) (pullback.lift_snd _ _ _)
    (by
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst]
        rw [reassoc_of% hc, q_fst_assoc, pullback.lift_fst_assoc, hφ, q_fst_assoc]
      · simp only [Category.assoc, pullback.lift_snd]) s
  refine ⟨T₂, hT₂, hsT₂, q p (Subalgebra.inclusion h₁₂) ≫ g₀ ≫ pullback.fst (lev ≫ fA) (ι ↥T₁), ?_⟩
  have h1 := congrArg (· ≫ pullback.fst fA (ι ↥T₂)) heq
  simp only [restage_fst, pullback.lift_fst] at h1
  simp only [Category.assoc]
  rw [h1, q_fst_assoc]

end Descend
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_abelianScheme_act_level_isPullback.PkgDesc18"

section Dict

variable {R : Type u} [CommRing R] {L : Type u} [CommRing L]
  {A C : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) (lev : C ⟶ A)
  {EA EC : Scheme.{u}} {Ef : EA ⟶ Spec (CommRingCat.of L)} (EG : RelativeGroupLaw L Ef) (Elev : EC ⟶ EA)
  (j : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of R))
  (g : EA ⟶ A) (hg : IsPullback g Ef f j) (gC : EC ⟶ C) (hgC : IsPullback gC Elev lev g)

def ofE {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of L)} (P : SchemeHomOver t Ef) : SchemeHomOver (t ≫ j) f :=
  ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩

@[scoped simp] theorem ofE_coe {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of L)} (P : SchemeHomOver t Ef) :
    (ofE j g hg P).1 = P.1 ≫ g := rfl

def toE {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of L)} (Q : SchemeHomOver (t ≫ j) f) : SchemeHomOver t Ef :=
  ⟨hg.lift Q.1 t Q.2, hg.lift_snd _ _ _⟩

theorem ofE_toE {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of L)} (Q : SchemeHomOver (t ≫ j) f) :
    ofE j g hg (toE j g hg Q) = Q :=
  Subtype.ext (hg.lift_fst _ _ _)

def MulCompat : Prop :=
  ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of L)) (P Q : SchemeHomOver t Ef),
    (EG.mul t P Q).1 ≫ g = (G.mul (t ≫ j) (ofE j g hg P) (ofE j g hg Q)).1

theorem ofE_mul (hmul : MulCompat G EG j g hg) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of L))
    (P Q : SchemeHomOver t Ef) : ofE j g hg (EG.mul t P Q) = G.mul _ (ofE j g hg P) (ofE j g hg Q) :=
  Subtype.ext (hmul t P Q)

theorem ofE_one (hmul : MulCompat G EG j g hg) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of L)) :
    ofE j g hg (EG.one t) = G.one _ := by
  apply eq_one_of_mul_self
  rw [← ofE_mul G EG j g hg hmul, EG.one_mul]

theorem ofE_inv (hmul : MulCompat G EG j g hg) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of L))
    (P : SchemeHomOver t Ef) : ofE j g hg (EG.inv t P) = G.inv _ (ofE j g hg P) := by
  apply eq_inv_of_mul_eq_one
  rw [← ofE_mul G EG j g hg hmul, EG.mul_inv_cancel, ofE_one G EG j g hg hmul]

theorem ofE_nsmul (hmul : MulCompat G EG j g hg) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of L)) (n : ℕ)
    (P : SchemeHomOver t Ef) : ofE j g hg (nsmulPt EG t n P) = nsmulPt G _ n (ofE j g hg P) := by
  induction n with
  | zero => exact ofE_one G EG j g hg hmul t
  | succ n ih => simp only [nsmulPt]; rw [ofE_mul G EG j g hg hmul, ih]

theorem ofE_push {φ : A ⟶ A} (hφ : φ ≫ f = f) {Eφ : EA ⟶ EA} (hEφ : Eφ ≫ Ef = Ef) (hact : Eφ ≫ g = g ≫ φ)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of L)} (P : SchemeHomOver t Ef) :
    ofE j g hg (pushPt Eφ hEφ P) = pushPt φ hφ (ofE j g hg P) :=
  Subtype.ext (by simp only [ofE_coe, mapPt_coe, Category.assoc, hact])

include hgC in
theorem ft_ofE_iff {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of L)} (P : SchemeHomOver t Ef) :
    FactorsThrough lev (ofE j g hg P) ↔ FactorsThrough Elev P := by
  constructor
  · rintro ⟨Q₀, hQ₀⟩
    rw [ofE_coe] at hQ₀
    exact ⟨hgC.lift Q₀ P.1 hQ₀, hgC.lift_snd _ _ _⟩
  · rintro ⟨P₀, hP₀⟩
    exact ⟨P₀ ≫ gC, by rw [Category.assoc, hgC.w, ← Category.assoc, hP₀, ofE_coe]⟩

include hgC in

theorem levSub_L (hmul : MulCompat G EG j g hg)
    (H : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of L)) (P Q : SchemeHomOver t Ef),
      FactorsThrough Elev P → FactorsThrough Elev Q → FactorsThrough Elev (EG.mul t P Q) ∧ FactorsThrough Elev (EG.inv t P))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of L)) (Q Q' : SchemeHomOver (t ≫ j) f)
    (hQ : FactorsThrough lev Q) (hQ' : FactorsThrough lev Q') :
    FactorsThrough lev (G.mul _ Q Q') ∧ FactorsThrough lev (G.inv _ Q) := by
  obtain ⟨P, rfl⟩ : ∃ P, ofE j g hg P = Q := ⟨_, ofE_toE j g hg Q⟩
  obtain ⟨P', rfl⟩ : ∃ P', ofE j g hg P' = Q' := ⟨_, ofE_toE j g hg Q'⟩
  rw [ft_ofE_iff lev Elev j g hg gC hgC] at hQ hQ'
  rw [← ofE_mul G EG j g hg hmul, ← ofE_inv G EG j g hg hmul, ft_ofE_iff lev Elev j g hg gC hgC, ft_ofE_iff lev Elev j g hg gC hgC]
  exact H t P P' hQ hQ'

include hgC in
theorem levOne_L (hmul : MulCompat G EG j g hg)
    (H : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of L)), FactorsThrough Elev (EG.one t))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of L)) : FactorsThrough lev (G.one (t ≫ j)) := by
  rw [← ofE_one G EG j g hg hmul, ft_ofE_iff lev Elev j g hg gC hgC]
  exact H t

include hgC in
theorem levTorsion_L (hmul : MulCompat G EG j g hg) (n : ℕ)
    (H : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of L)) (P : SchemeHomOver t Ef),
      FactorsThrough Elev P → nsmulPt EG t n P = EG.one t)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of L)) (Q : SchemeHomOver (t ≫ j) f)
    (hQ : FactorsThrough lev Q) : nsmulPt G _ n Q = G.one _ := by
  obtain ⟨P, rfl⟩ : ∃ P, ofE j g hg P = Q := ⟨_, ofE_toE j g hg Q⟩
  rw [ft_ofE_iff lev Elev j g hg gC hgC] at hQ
  rw [← ofE_nsmul G EG j g hg hmul, H t P hQ, ofE_one G EG j g hg hmul]

include G EG hg hgC in
theorem levStable_L {φ : A ⟶ A} (hφ : φ ≫ f = f) {Eφ : EA ⟶ EA} (hEφ : Eφ ≫ Ef = Ef)
    (hact : Eφ ≫ g = g ≫ φ)
    (H : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of L)) (P : SchemeHomOver t Ef),
      FactorsThrough Elev P → FactorsThrough Elev (pushPt Eφ hEφ P))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of L)) (Q : SchemeHomOver (t ≫ j) f)
    (hQ : FactorsThrough lev Q) : FactorsThrough lev (pushPt φ hφ Q) := by
  obtain ⟨P, rfl⟩ : ∃ P, ofE j g hg P = Q := ⟨_, ofE_toE j g hg Q⟩
  rw [ft_ofE_iff lev Elev j g hg gC hgC] at hQ
  rw [← ofE_push j g hg hφ hEφ hact, ft_ofE_iff lev Elev j g hg gC hgC]
  exact H t P hQ

end Dict
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_abelianScheme_act_level_isPullback.PkgDesc18"

section Closure

open scoped Quaternion

variable {R : Type u} [CommRing R] {A C B : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)
  (lev : C ⟶ A) (j : B ⟶ Spec (CommRingCat.of R))
  {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (act : ↥Λ → (A ⟶ A)) (hover : ∀ x : ↥Λ, act x ≫ f = f)
  (hadd : ∀ (x y : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f),
    pushPt (act (x + y)) (hover (x + y)) P = G.mul t (pushPt (act x) (hover x) P) (pushPt (act y) (hover y) P))

include hadd in
theorem pushPt_act_zero {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f) :
    pushPt (act 0) (hover 0) P = G.one t := by
  apply eq_one_of_mul_self
  have h := hadd 0 0 t P
  rw [add_zero] at h
  exact h.symm

include hadd in
theorem pushPt_act_neg {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (y : ↥Λ) (P : SchemeHomOver t f) :
    pushPt (act (-y)) (hover (-y)) P = G.inv t (pushPt (act y) (hover y) P) := by
  apply eq_inv_of_mul_eq_one
  rw [← hadd y (-y) t P]
  have : y + -y = 0 := add_neg_cancel y
  rw [this]
  exact pushPt_act_zero G act hover hadd t P

def Stable (x : ↥Λ) : Prop :=
  ∀ (T : Scheme.{u}) (t : T ⟶ B) (P : SchemeHomOver (t ≫ j) f),
    FactorsThrough lev P → FactorsThrough lev (pushPt (act x) (hover x) P)

variable
  (hone : ∀ {T : Scheme.{u}} (t : T ⟶ B), FactorsThrough lev (G.one (t ≫ j)))
  (hsub : ∀ {T : Scheme.{u}} (t : T ⟶ B) (P Q : SchemeHomOver (t ≫ j) f),
    FactorsThrough lev P → FactorsThrough lev Q → FactorsThrough lev (G.mul _ P Q) ∧ FactorsThrough lev (G.inv _ P))

include hadd hone in
theorem stable_zero : Stable lev j act hover 0 := by
  intro T t P _
  rw [pushPt_act_zero G act hover hadd]
  exact hone t

include hadd hsub in
theorem stable_add (x y : ↥Λ) (hx : Stable lev j act hover x) (hy : Stable lev j act hover y) :
    Stable lev j act hover (x + y) := by
  intro T t P hP
  rw [hadd]
  exact (hsub t _ _ (hx T t P hP) (hy T t P hP)).1

include hadd hsub in
theorem stable_neg (y : ↥Λ) (hy : Stable lev j act hover y) : Stable lev j act hover (-y) := by
  intro T t P hP
  rw [pushPt_act_neg G act hover hadd]
  exact (hsub t _ _ (hy T t P hP) (hy T t P hP)).2

include hadd hone hsub in

theorem stable_closure (Gs : Set ℍ[ℚ, a, b]) (hG : Submodule.span ℤ Gs = Λ)
    (hgen : ∀ (g : ℍ[ℚ, a, b]) (_ : g ∈ Gs) (hg : g ∈ Λ), Stable lev j act hover ⟨g, hg⟩) (x : ↥Λ) :
    Stable lev j act hover x := by
  have hx : (x : ℍ[ℚ, a, b]) ∈ Submodule.span ℤ Gs := by rw [hG]; exact x.2
  have key : ∀ (y : ℍ[ℚ, a, b]) (hy : y ∈ Submodule.span ℤ Gs), ∀ hy' : y ∈ Λ, Stable lev j act hover ⟨y, hy'⟩ := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hyG => intro hy'; exact hgen y hyG hy'
    | zero => intro hy'; exact stable_zero G lev j act hover hadd hone
    | add y z hy hz ihy ihz =>
      intro hyz
      have hy' : y ∈ Λ := hG ▸ hy
      have hz' : z ∈ Λ := hG ▸ hz
      exact stable_add G lev j act hover hadd hsub ⟨y, hy'⟩ ⟨z, hz'⟩ (ihy hy') (ihz hz')
    | smul n y hy ihy =>
      intro hny
      have hy' : y ∈ Λ := hG ▸ hy
      have : (⟨n • y, hny⟩ : ↥Λ) = n • ⟨y, hy'⟩ := rfl
      rw [this]
      clear hny this
      induction n using Int.induction_on with
      | zero => rw [zero_smul]; exact stable_zero G lev j act hover hadd hone
      | succ k ih => rw [add_smul, one_smul]; exact stable_add G lev j act hover hadd hsub _ _ ih (ihy hy')
      | pred k ih =>
        rw [sub_smul, one_smul, sub_eq_add_neg]
        exact stable_add G lev j act hover hadd hsub _ _ ih (stable_neg G lev j act hover hadd hsub _ (ihy hy'))
  exact key x.1 hx x.2

end Closure
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_abelianScheme_act_level_isPullback.PkgDesc18"

end LevDesc21
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_abelianScheme_act_level_isPullback.PkgDesc18 P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_abelianScheme_act_level_isPullback.LevDesc21"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_abelianScheme_act_level_isPullback.PkgDesc18 P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_abelianScheme_act_level_isPullback.LevDesc21"

noncomputable section E20Block

universe u

open scoped Quaternion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian GoodReductionJacobian.RelativeGroupLaw CerednikDrinfeld.QM

namespace NoethBC20

variable {R : Type u} [CommRing R] {R' : Type u} [CommRing R']
variable (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
variable {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem mul_coe_congr (G : RelativeGroupLaw R f) {T : Scheme.{u}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)}
    (h : t₁ = t₂) (P₁ Q₁ : SchemeHomOver t₁ f) (P₂ Q₂ : SchemeHomOver t₂ f)
    (hP : P₁.1 = P₂.1) (hQ : Q₁.1 = Q₂.1) :
    (G.mul t₁ P₁ Q₁).1 = (G.mul t₂ P₂ Q₂).1 := by
  subst h
  obtain rfl : P₁ = P₂ := Subtype.ext hP
  obtain rfl : Q₁ = Q₂ := Subtype.ext hQ
  rfl

theorem one_coe_congr (G : RelativeGroupLaw R f) {T : Scheme.{u}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)}
    (h : t₁ = t₂) : (G.one t₁).1 = (G.one t₂).1 := by
  subst h; rfl

theorem inv_coe_congr (G : RelativeGroupLaw R f) {T : Scheme.{u}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)}
    (h : t₁ = t₂) (P₁ : SchemeHomOver t₁ f) (P₂ : SchemeHomOver t₂ f) (hP : P₁.1 = P₂.1) :
    (G.inv t₁ P₁).1 = (G.inv t₂ P₂).1 := by
  subst h
  obtain rfl : P₁ = P₂ := Subtype.ext hP
  rfl

theorem toBase_injective {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) :
    Function.Injective
      (baseChangePointToBase ι : SchemeHomOver t' (baseChangeStr ι f) → SchemeHomOver (t' ≫ ι) f) :=
  (baseChangePointEquiv ι t').injective

section Endo

variable (φ : A ⟶ A) (hφ : φ ≫ f = f)

def bcEndo : baseChangeScheme ι f ⟶ baseChangeScheme ι f :=
  pullback.lift (pullback.fst f ι ≫ φ) (pullback.snd f ι) (by rw [Category.assoc, hφ, pullback.condition])

@[reassoc (attr := simp)]
theorem bcEndo_fst : bcEndo ι φ hφ ≫ pullback.fst f ι = pullback.fst f ι ≫ φ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem bcEndo_snd : bcEndo ι φ hφ ≫ pullback.snd f ι = pullback.snd f ι :=
  pullback.lift_snd _ _ _

theorem bcEndo_over : bcEndo ι φ hφ ≫ baseChangeStr ι f = baseChangeStr ι f :=
  pullback.lift_snd _ _ _

theorem bcEndo_congr {φ ψ : A ⟶ A} (h : φ = ψ) (hφ : φ ≫ f = f) (hψ : ψ ≫ f = f) :
    bcEndo ι φ hφ = bcEndo ι ψ hψ := by
  subst h; rfl

theorem bcEndo_eq_id {φ : A ⟶ A} (h : φ = 𝟙 A) (hφ : φ ≫ f = f) : bcEndo ι φ hφ = 𝟙 _ := by
  subst h
  apply pullback.hom_ext
  · rw [bcEndo_fst, Category.id_comp, Category.comp_id]
  · rw [bcEndo_snd, Category.id_comp]

theorem bcEndo_eq_comp {χ ψ φ : A ⟶ A} (h : χ = ψ ≫ φ) (hχ : χ ≫ f = f) (hψ : ψ ≫ f = f) (hφ : φ ≫ f = f) :
    bcEndo ι χ hχ = bcEndo ι ψ hψ ≫ bcEndo ι φ hφ := by
  subst h
  apply pullback.hom_ext
  · simp only [bcEndo_fst, Category.assoc, bcEndo_fst_assoc]
  · simp only [bcEndo_snd, Category.assoc]

theorem toBase_pushPt {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')}
    (h' : bcEndo ι φ hφ ≫ baseChangeStr ι f = baseChangeStr ι f)
    (P : SchemeHomOver t' (baseChangeStr ι f)) :
    baseChangePointToBase ι (pushPt (bcEndo ι φ hφ) h' P) = pushPt φ hφ (baseChangePointToBase ι P) := by
  apply Subtype.ext
  simp only [baseChangePointToBase_coe, mapPt_coe, Category.assoc, bcEndo_fst]

theorem pushPt_bcEndo_mul (G : RelativeGroupLaw R f)
    (H : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      pushPt φ hφ (G.mul t P Q) = G.mul t (pushPt φ hφ P) (pushPt φ hφ Q))
    (h' : bcEndo ι φ hφ ≫ baseChangeStr ι f = baseChangeStr ι f)
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) (P Q : SchemeHomOver t' (baseChangeStr ι f)) :
    pushPt (bcEndo ι φ hφ) h' ((G.baseChange ι).mul t' P Q) =
      (G.baseChange ι).mul t' (pushPt (bcEndo ι φ hφ) h' P) (pushPt (bcEndo ι φ hφ) h' Q) := by
  apply toBase_injective ι t'
  rw [toBase_pushPt, baseChangePointToBase_mul, baseChangePointToBase_mul, H, toBase_pushPt, toBase_pushPt]

theorem pushPt_bcEndo_add (G : RelativeGroupLaw R f) {χ ψ : A ⟶ A} (hχ : χ ≫ f = f) (hψ : ψ ≫ f = f)
    (H : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f),
      pushPt χ hχ P = G.mul t (pushPt φ hφ P) (pushPt ψ hψ P))
    (hχ' : bcEndo ι χ hχ ≫ baseChangeStr ι f = baseChangeStr ι f)
    (hφ' : bcEndo ι φ hφ ≫ baseChangeStr ι f = baseChangeStr ι f)
    (hψ' : bcEndo ι ψ hψ ≫ baseChangeStr ι f = baseChangeStr ι f)
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) (P : SchemeHomOver t' (baseChangeStr ι f)) :
    pushPt (bcEndo ι χ hχ) hχ' P =
      (G.baseChange ι).mul t' (pushPt (bcEndo ι φ hφ) hφ' P) (pushPt (bcEndo ι ψ hψ) hψ' P) := by
  apply toBase_injective ι t'
  rw [toBase_pushPt, baseChangePointToBase_mul, H, toBase_pushPt, toBase_pushPt]

end Endo
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_abelianScheme_act_level_isPullback.PkgDesc18 P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_abelianScheme_act_level_isPullback.LevDesc21"

section Lev

variable (f) {C : Scheme.{u}} (lev : C ⟶ A)

abbrev bcLevScheme : Scheme.{u} :=
  pullback (lev ≫ f) ι

def bcLev : bcLevScheme ι f lev ⟶ baseChangeScheme ι f :=
  pullback.lift (pullback.fst (lev ≫ f) ι ≫ lev) (pullback.snd (lev ≫ f) ι)
    (by rw [Category.assoc]; exact pullback.condition)

@[reassoc (attr := simp)]
theorem bcLev_fst : bcLev ι f lev ≫ pullback.fst f ι = pullback.fst (lev ≫ f) ι ≫ lev :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem bcLev_snd : bcLev ι f lev ≫ pullback.snd f ι = pullback.snd (lev ≫ f) ι :=
  pullback.lift_snd _ _ _

theorem bcLev_comp_baseChangeStr : bcLev ι f lev ≫ baseChangeStr ι f = pullback.snd (lev ≫ f) ι :=
  pullback.lift_snd _ _ _

theorem isPullback_fst_bcLev :
    IsPullback (pullback.fst (lev ≫ f) ι) (bcLev ι f lev) lev (pullback.fst f ι) := by
  refine IsPullback.of_bot ?_ (bcLev_fst ι f lev).symm (IsPullback.of_hasPullback f ι)
  rw [bcLev_snd]
  exact IsPullback.of_hasPullback (lev ≫ f) ι

theorem isClosedImmersion_bcLev [IsClosedImmersion lev] : IsClosedImmersion (bcLev ι f lev) :=
  MorphismProperty.of_isPullback (isPullback_fst_bcLev ι f lev) ‹_›

theorem isFinite_bcLev_comp [IsFinite (lev ≫ f)] : IsFinite (bcLev ι f lev ≫ baseChangeStr ι f) := by
  rw [bcLev_comp_baseChangeStr]; infer_instance

theorem flat_bcLev_comp [Flat (lev ≫ f)] : Flat (bcLev ι f lev ≫ baseChangeStr ι f) := by
  rw [bcLev_comp_baseChangeStr]; infer_instance

theorem locallyOfFinitePresentation_bcLev_comp [LocallyOfFinitePresentation (lev ≫ f)] :
    LocallyOfFinitePresentation (bcLev ι f lev ≫ baseChangeStr ι f) := by
  rw [bcLev_comp_baseChangeStr]; infer_instance

theorem factorsThrough_bcLev_iff {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')}
    (P : SchemeHomOver t' (baseChangeStr ι f)) :
    FactorsThrough (bcLev ι f lev) P ↔ FactorsThrough lev (baseChangePointToBase ι P) := by
  constructor
  · rintro ⟨P₀, hP₀⟩
    refine ⟨P₀ ≫ pullback.fst (lev ≫ f) ι, ?_⟩
    rw [baseChangePointToBase_coe, ← hP₀, Category.assoc, Category.assoc, bcLev_fst]
  · rintro ⟨Q₀, hQ₀⟩
    rw [baseChangePointToBase_coe] at hQ₀
    refine ⟨pullback.lift Q₀ (P.1 ≫ pullback.snd f ι) ?_, ?_⟩
    · rw [← Category.assoc, hQ₀, Category.assoc, Category.assoc, pullback.condition]
    · apply pullback.hom_ext
      · rw [Category.assoc, bcLev_fst, ← Category.assoc, pullback.lift_fst, hQ₀]
      · rw [Category.assoc, bcLev_snd, pullback.lift_snd]

theorem toBase_nsmulPt (G : RelativeGroupLaw R f) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R'))
    (n : ℕ) (P : SchemeHomOver t' (baseChangeStr ι f)) :
    baseChangePointToBase ι (nsmulPt (G.baseChange ι) t' n P) =
      nsmulPt G (t' ≫ ι) n (baseChangePointToBase ι P) := by
  induction n with
  | zero => exact baseChangePointToBase_one ι G t'
  | succ n ih => simp only [nsmulPt, baseChangePointToBase_mul, ih]

theorem lev_sub_bc (G : RelativeGroupLaw R f)
    (H : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      FactorsThrough lev P → FactorsThrough lev Q → FactorsThrough lev (G.mul t P Q) ∧ FactorsThrough lev (G.inv t P))
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) (P Q : SchemeHomOver t' (baseChangeStr ι f)) :
    FactorsThrough (bcLev ι f lev) P → FactorsThrough (bcLev ι f lev) Q →
      FactorsThrough (bcLev ι f lev) ((G.baseChange ι).mul t' P Q) ∧
        FactorsThrough (bcLev ι f lev) ((G.baseChange ι).inv t' P) := by
  intro hP hQ
  rw [factorsThrough_bcLev_iff] at hP hQ
  rw [factorsThrough_bcLev_iff, factorsThrough_bcLev_iff, baseChangePointToBase_mul, baseChangePointToBase_inv]
  exact H _ _ _ hP hQ

theorem lev_one_bc (G : RelativeGroupLaw R f)
    (H : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), FactorsThrough lev (G.one t))
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) :
    FactorsThrough (bcLev ι f lev) ((G.baseChange ι).one t') := by
  rw [factorsThrough_bcLev_iff, baseChangePointToBase_one]
  exact H _

theorem lev_torsion_bc (G : RelativeGroupLaw R f) (N : ℕ)
    (H : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f),
      FactorsThrough lev P → nsmulPt G t N P = G.one t)
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) (P : SchemeHomOver t' (baseChangeStr ι f)) :
    FactorsThrough (bcLev ι f lev) P → nsmulPt (G.baseChange ι) t' N P = (G.baseChange ι).one t' := by
  intro hP
  rw [factorsThrough_bcLev_iff] at hP
  apply toBase_injective ι t'
  rw [toBase_nsmulPt, baseChangePointToBase_one]
  exact H _ _ hP

theorem lev_stable_bc (φ : A ⟶ A) (hφ : φ ≫ f = f)
    (H : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f),
      FactorsThrough lev P → FactorsThrough lev (pushPt φ hφ P))
    (h' : bcEndo ι φ hφ ≫ baseChangeStr ι f = baseChangeStr ι f)
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) (P : SchemeHomOver t' (baseChangeStr ι f)) :
    FactorsThrough (bcLev ι f lev) P → FactorsThrough (bcLev ι f lev) (pushPt (bcEndo ι φ hφ) h' P) := by
  intro hP
  rw [factorsThrough_bcLev_iff] at hP
  rw [factorsThrough_bcLev_iff, toBase_pushPt]
  exact H _ _ hP

end Lev
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_abelianScheme_act_level_isPullback.PkgDesc18 P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_abelianScheme_act_level_isPullback.LevDesc21"

theorem geometricallyConnected_baseChangeStr [GeometricallyConnected f] :
    GeometricallyConnected (baseChangeStr ι f) :=
  inferInstance

theorem abelianSchemePropertyBundle_bc (hb : AbelianSchemePropertyBundle R f) [GeometricallyConnected f]
    (G' : RelativeGroupLaw R' (baseChangeStr ι f)) :
    AbelianSchemePropertyBundle R' (baseChangeStr ι f) where
  smooth := have := hb.smooth; inferInstance
  proper := have := hb.proper; inferInstance
  connectedFibres s := (baseChangeStr ι f).isConnected_preimage_singleton s
  hasGroupLaw := ⟨G'⟩

section Comparison

variable {S : Type u} [CommRing S] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of S))
variable (j : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R)) (j' : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R'))
variable (hj : j' ≫ ι = j) (g : X ⟶ A) (hg : IsPullback g p f j)

def bcComparison : X ⟶ baseChangeScheme ι f :=
  pullback.lift g (p ≫ j') (by rw [Category.assoc, hj]; exact hg.w)

@[reassoc (attr := simp)]
theorem bcComparison_fst : bcComparison ι p j j' hj g hg ≫ pullback.fst f ι = g :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem bcComparison_snd : bcComparison ι p j j' hj g hg ≫ pullback.snd f ι = p ≫ j' :=
  pullback.lift_snd _ _ _

theorem isPullback_bcComparison :
    IsPullback (bcComparison ι p j j' hj g hg) p (baseChangeStr ι f) j' := by
  refine IsPullback.of_right ?_ (bcComparison_snd ι p j j' hj g hg) (IsPullback.of_hasPullback f ι)
  rw [bcComparison_fst, hj]
  exact hg

theorem comp_bcComparison_eq_bcComparison_comp_bcEndo (φ : A ⟶ A) (hφ : φ ≫ f = f)
    (actX : X ⟶ X) (hactX : actX ≫ p = p) (H : actX ≫ g = g ≫ φ) :
    actX ≫ bcComparison ι p j j' hj g hg = bcComparison ι p j j' hj g hg ≫ bcEndo ι φ hφ := by
  apply pullback.hom_ext
  · simp only [Category.assoc, bcComparison_fst, bcEndo_fst, bcComparison_fst_assoc, H]
  · simp only [Category.assoc, bcComparison_snd, bcEndo_snd]
    rw [← Category.assoc, hactX]

theorem mul_coe_comp_bcComparison (GX : RelativeGroupLaw S p) (G : RelativeGroupLaw R f)
    (H : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t p),
      (GX.mul t P Q).1 ≫ g =
        (G.mul (t ≫ j) ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t p) :
    (GX.mul t P Q).1 ≫ bcComparison ι p j j' hj g hg =
      ((G.baseChange ι).mul (t ≫ j')
        ⟨P.1 ≫ bcComparison ι p j j' hj g hg, by
          rw [Category.assoc, (isPullback_bcComparison ι p j j' hj g hg).w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ bcComparison ι p j j' hj g hg, by
          rw [Category.assoc, (isPullback_bcComparison ι p j j' hj g hg).w, ← Category.assoc, Q.2]⟩).1 := by
  apply pullback.hom_ext
  · rw [Category.assoc, bcComparison_fst, H, baseChange_mul, baseChangePointOfBase_coe, pullback.lift_fst]
    apply mul_coe_congr G
    · rw [Category.assoc, hj]
    · simp only [baseChangePointToBase_coe, Category.assoc, bcComparison_fst]
    · simp only [baseChangePointToBase_coe, Category.assoc, bcComparison_fst]
  · have e1 : ∀ x : SchemeHomOver (t ≫ j') (baseChangeStr ι f), x.1 ≫ pullback.snd f ι = t ≫ j' :=
      fun x => x.2
    rw [e1]
    simp only [Category.assoc, bcComparison_snd]
    rw [← Category.assoc, (GX.mul t P Q).2]

section Sub

variable {C : Scheme.{u}} (lev : C ⟶ A) {XC : Scheme.{u}} (pC : XC ⟶ X) (gC : XC ⟶ C)
variable (hgC : IsPullback gC pC lev g)

def bcComparisonSub : XC ⟶ bcLevScheme ι f lev :=
  pullback.lift gC (pC ≫ p ≫ j') (by
    rw [← Category.assoc gC, hgC.w, Category.assoc, hg.w, Category.assoc, Category.assoc, hj])

@[reassoc (attr := simp)]
theorem bcComparisonSub_fst : bcComparisonSub ι p j j' hj g hg lev pC gC hgC ≫ pullback.fst (lev ≫ f) ι = gC :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem bcComparisonSub_snd :
    bcComparisonSub ι p j j' hj g hg lev pC gC hgC ≫ pullback.snd (lev ≫ f) ι = pC ≫ p ≫ j' :=
  pullback.lift_snd _ _ _

theorem bcComparisonSub_bcLev :
    bcComparisonSub ι p j j' hj g hg lev pC gC hgC ≫ bcLev ι f lev = pC ≫ bcComparison ι p j j' hj g hg := by
  apply pullback.hom_ext
  · simp only [Category.assoc, bcLev_fst, bcComparisonSub_fst_assoc, bcComparison_fst]
    exact hgC.w
  · simp only [Category.assoc, bcLev_snd, bcComparisonSub_snd, bcComparison_snd]

theorem isPullback_bcComparisonSub :
    IsPullback (bcComparisonSub ι p j j' hj g hg lev pC gC hgC) pC (bcLev ι f lev)
      (bcComparison ι p j j' hj g hg) := by
  refine IsPullback.of_right ?_ (bcComparisonSub_bcLev ι p j j' hj g hg lev pC gC hgC) (isPullback_fst_bcLev ι f lev)
  rw [bcComparisonSub_fst, bcComparison_fst]
  exact hgC

end Sub
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_abelianScheme_act_level_isPullback.PkgDesc18 P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_abelianScheme_act_level_isPullback.LevDesc21"

end Comparison
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_abelianScheme_act_level_isPullback.PkgDesc18 P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_abelianScheme_act_level_isPullback.LevDesc21"

end NoethBC20
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_abelianScheme_act_level_isPullback.PkgDesc18 P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_abelianScheme_act_level_isPullback.LevDesc21"

namespace NoethBC20

variable {R : Type u} [CommRing R] {R' : Type u} [CommRing R']
variable (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
variable {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R)) {C : Scheme.{u}} (lev : C ⟶ A)

theorem lev_sub_bc' (G : RelativeGroupLaw R f)
    (H : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) (P Q : SchemeHomOver (t' ≫ ι) f),
      FactorsThrough lev P → FactorsThrough lev Q →
        FactorsThrough lev (G.mul (t' ≫ ι) P Q) ∧ FactorsThrough lev (G.inv (t' ≫ ι) P))
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) (P Q : SchemeHomOver t' (baseChangeStr ι f)) :
    FactorsThrough (bcLev ι f lev) P → FactorsThrough (bcLev ι f lev) Q →
      FactorsThrough (bcLev ι f lev) ((G.baseChange ι).mul t' P Q) ∧
        FactorsThrough (bcLev ι f lev) ((G.baseChange ι).inv t' P) := by
  intro hP hQ
  rw [factorsThrough_bcLev_iff] at hP hQ
  rw [factorsThrough_bcLev_iff, factorsThrough_bcLev_iff, baseChangePointToBase_mul, baseChangePointToBase_inv]
  exact H _ _ _ hP hQ

theorem lev_one_bc' (G : RelativeGroupLaw R f)
    (H : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')), FactorsThrough lev (G.one (t' ≫ ι)))
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) :
    FactorsThrough (bcLev ι f lev) ((G.baseChange ι).one t') := by
  rw [factorsThrough_bcLev_iff, baseChangePointToBase_one]
  exact H _

theorem lev_torsion_bc' (G : RelativeGroupLaw R f) (N : ℕ)
    (H : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) (P : SchemeHomOver (t' ≫ ι) f),
      FactorsThrough lev P → nsmulPt G (t' ≫ ι) N P = G.one (t' ≫ ι))
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) (P : SchemeHomOver t' (baseChangeStr ι f)) :
    FactorsThrough (bcLev ι f lev) P → nsmulPt (G.baseChange ι) t' N P = (G.baseChange ι).one t' := by
  intro hP
  rw [factorsThrough_bcLev_iff] at hP
  apply toBase_injective ι t'
  rw [toBase_nsmulPt, baseChangePointToBase_one]
  exact H _ _ hP

theorem lev_stable_bc' (φ : A ⟶ A) (hφ : φ ≫ f = f)
    (H : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) (P : SchemeHomOver (t' ≫ ι) f),
      FactorsThrough lev P → FactorsThrough lev (pushPt φ hφ P))
    (h' : bcEndo ι φ hφ ≫ baseChangeStr ι f = baseChangeStr ι f)
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) (P : SchemeHomOver t' (baseChangeStr ι f)) :
    FactorsThrough (bcLev ι f lev) P → FactorsThrough (bcLev ι f lev) (pushPt (bcEndo ι φ hφ) h' P) := by
  intro hP
  rw [factorsThrough_bcLev_iff] at hP
  rw [factorsThrough_bcLev_iff, toBase_pushPt]
  exact H _ _ hP

end NoethBC20
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_abelianScheme_act_level_isPullback.PkgDesc18 P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_abelianScheme_act_level_isPullback.LevDesc21"

namespace RawLev20

open NoethBC20

section Packages

variable {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b])
variable {R : Type} [CommRing R] {R' : Type} [CommRing R'] {S : Type} [CommRing S]
variable (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
variable {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (L₀ : RelativeGroupLaw R f)
variable (act : ↥Λ → (A ⟶ A)) (hover : ∀ x : ↥Λ, act x ≫ f = f)

theorem actLaws_bc
    (hhom : ∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      pushPt (act x) (hover x) (L₀.mul t P Q) = L₀.mul t (pushPt (act x) (hover x) P) (pushPt (act x) (hover x) Q))
    (hone : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, act ⟨1, h⟩ = 𝟙 A)
    (hmul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = act y ≫ act x)
    (hadd : ∀ (x y : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f),
      pushPt (act (x + y)) (hover (x + y)) P = L₀.mul t (pushPt (act x) (hover x) P) (pushPt (act y) (hover y) P)) :
    ∃ (hover' : ∀ x : ↥Λ, bcEndo ι (act x) (hover x) ≫ baseChangeStr ι f = baseChangeStr ι f),
      (∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R')) (P Q : SchemeHomOver t (baseChangeStr ι f)),
        pushPt (bcEndo ι (act x) (hover x)) (hover' x) ((L₀.baseChange ι).mul t P Q) =
          (L₀.baseChange ι).mul t (pushPt (bcEndo ι (act x) (hover x)) (hover' x) P)
            (pushPt (bcEndo ι (act x) (hover x)) (hover' x) Q)) ∧
      (∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, bcEndo ι (act ⟨1, h⟩) (hover ⟨1, h⟩) = 𝟙 _) ∧
      (∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
        bcEndo ι (act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩) (hover _) =
          bcEndo ι (act y) (hover y) ≫ bcEndo ι (act x) (hover x)) ∧
      (∀ (x y : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R')) (P : SchemeHomOver t (baseChangeStr ι f)),
        pushPt (bcEndo ι (act (x + y)) (hover (x + y))) (hover' (x + y)) P =
          (L₀.baseChange ι).mul t (pushPt (bcEndo ι (act x) (hover x)) (hover' x) P)
            (pushPt (bcEndo ι (act y) (hover y)) (hover' y) P)) :=
  ⟨fun x => bcEndo_over ι (act x) (hover x),
    fun x _ t P Q => pushPt_bcEndo_mul ι (act x) (hover x) L₀ (hhom x) _ t P Q,
    fun h => bcEndo_eq_id ι (hone h) _,
    fun x y h => bcEndo_eq_comp ι (hmul x y h) _ _ _,
    fun x y _ t P => pushPt_bcEndo_add ι (act x) (hover x) L₀ (hover (x + y)) (hover y) (hadd x y) _ _ _ t P⟩

variable {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of S)) (LX : RelativeGroupLaw S p) (actX : ↥Λ → (X ⟶ X))
variable (j : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R)) (j' : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R'))
variable (hj : j' ≫ ι = j) (g : X ⟶ A) (hg : IsPullback g p f j)

theorem cmp_bc (hactX : ∀ x : ↥Λ, actX x ≫ p = p)
    (hmulc : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t' p),
      (LX.mul t' P Q).1 ≫ g =
        (L₀.mul (t' ≫ j) ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)
    (hactc : ∀ x : ↥Λ, actX x ≫ g = g ≫ act x) :
    ∃ (hg' : IsPullback (bcComparison ι p j j' hj g hg) p (baseChangeStr ι f) j'),
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t' p),
        (LX.mul t' P Q).1 ≫ bcComparison ι p j j' hj g hg =
          ((L₀.baseChange ι).mul (t' ≫ j')
            ⟨P.1 ≫ bcComparison ι p j j' hj g hg, by rw [Category.assoc, hg'.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ bcComparison ι p j j' hj g hg, by rw [Category.assoc, hg'.w, ← Category.assoc, Q.2]⟩).1) ∧
      (∀ x : ↥Λ, actX x ≫ bcComparison ι p j j' hj g hg = bcComparison ι p j j' hj g hg ≫ bcEndo ι (act x) (hover x)) :=
  ⟨isPullback_bcComparison ι p j j' hj g hg,
    fun t' P Q => mul_coe_comp_bcComparison ι p j j' hj g hg LX L₀ hmulc t' P Q,
    fun x => comp_bcComparison_eq_bcComparison_comp_bcEndo ι p j j' hj g hg (act x) (hover x) (actX x) (hactX x)
      (hactc x)⟩

end Packages
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_abelianScheme_act_level_isPullback.PkgDesc18 P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_abelianScheme_act_level_isPullback.LevDesc21"

end RawLev20
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_abelianScheme_act_level_isPullback.PkgDesc18 P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_abelianScheme_act_level_isPullback.LevDesc21"

end E20Block
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_abelianScheme_act_level_isPullback.PkgDesc18 P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_abelianScheme_act_level_isPullback.LevDesc21"

section FinalBC
open scoped TensorProduct Quaternion NumberField
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM GoodReductionJacobian

open NeronModelInfra (SchemeHomOver)

theorem LevDesc21.final_bc
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N : ℕ)
    (L : Type) [CommRing L] (E : FakeEllipticCurve Λ N L) (s : Finset L)
    (R₁ : Subalgebra ℤ L) (hR₁fg : R₁.FG) (hsR₁ : (↑s : Set L) ⊆ R₁)
    (A₁ : Scheme.{0}) (f₁ : A₁ ⟶ Spec (CommRingCat.of ↥R₁)) (L₁ : RelativeGroupLaw ↥R₁ f₁) (hcomm₁ : L₁.IsCommutative)
    (hb₁ : AbelianSchemePropertyBundle ↥R₁ f₁) (hgc₁ : GeometricallyConnected f₁)
    (act₁ : ↥Λ → (A₁ ⟶ A₁)) (hover₁ : ∀ x : ↥Λ, act₁ x ≫ f₁ = f₁)
    (hhom₁ : ∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥R₁)) (P Q : SchemeHomOver t f₁),
      pushPt (act₁ x) (hover₁ x) (L₁.mul t P Q) = L₁.mul t (pushPt (act₁ x) (hover₁ x) P) (pushPt (act₁ x) (hover₁ x) Q))
    (hone₁ : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, act₁ ⟨1, h⟩ = 𝟙 A₁)
    (hmul₁ : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      act₁ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = act₁ y ≫ act₁ x)
    (hadd₁ : ∀ (x y : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥R₁)) (P : SchemeHomOver t f₁),
      pushPt (act₁ (x + y)) (hover₁ (x + y)) P =
        L₁.mul t (pushPt (act₁ x) (hover₁ x) P) (pushPt (act₁ y) (hover₁ y) P))
    (C₁ : Scheme.{0}) (lev₁ : C₁ ⟶ A₁) (hci₁ : IsClosedImmersion lev₁)
    (hfin₁ : IsFinite (lev₁ ≫ f₁)) (hflat₁ : Flat (lev₁ ≫ f₁)) (hlfp₁ : LocallyOfFinitePresentation (lev₁ ≫ f₁))
    (g₁ : E.A ⟶ A₁) (hg₁ : CategoryTheory.IsPullback g₁ E.f f₁ (Spec.map (CommRingCat.ofHom R₁.val.toRingHom)))
    (gC₁ : E.C ⟶ C₁) (hgC₁ : CategoryTheory.IsPullback gC₁ E.lev lev₁ g₁)
    (hmulg₁ : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of L)) (P Q : SchemeHomOver t' E.f),
        (E.L.mul t' P Q).1 ≫ g₁ =
          (L₁.mul (t' ≫ Spec.map (CommRingCat.ofHom R₁.val.toRingHom))
            ⟨P.1 ≫ g₁, by rw [Category.assoc, hg₁.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ g₁, by rw [Category.assoc, hg₁.w, ← Category.assoc, Q.2]⟩).1)
    (hactg₁ : ∀ x : ↥Λ, E.act x ≫ g₁ = g₁ ≫ act₁ x)

    (T : Subalgebra ↥R₁ L) (hT : T.FG)
    (Hsub : ∀ {T' : Scheme.{0}} (t : T' ⟶ Spec (CommRingCat.of ↥T))
      (P Q : SchemeHomOver (t ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥R₁ ↥T))) f₁),
      FactorsThrough lev₁ P → FactorsThrough lev₁ Q → FactorsThrough lev₁ (L₁.mul _ P Q) ∧ FactorsThrough lev₁ (L₁.inv _ P))
    (Hone : ∀ {T' : Scheme.{0}} (t : T' ⟶ Spec (CommRingCat.of ↥T)),
      FactorsThrough lev₁ (L₁.one (t ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥R₁ ↥T)))))
    (Htor : ∀ {T' : Scheme.{0}} (t : T' ⟶ Spec (CommRingCat.of ↥T))
      (P : SchemeHomOver (t ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥R₁ ↥T))) f₁),
      FactorsThrough lev₁ P → nsmulPt L₁ _ N P = L₁.one _)
    (Hst : ∀ (x : ↥Λ) {T' : Scheme.{0}} (t : T' ⟶ Spec (CommRingCat.of ↥T))
      (P : SchemeHomOver (t ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥R₁ ↥T))) f₁),
      FactorsThrough lev₁ P → FactorsThrough lev₁ (pushPt (act₁ x) (hover₁ x) P)) :
    ∃ (R : Subalgebra ℤ L) (_ : R.FG) (_ : (↑s : Set L) ⊆ R)
      (A₀ : Scheme.{0}) (f₀ : A₀ ⟶ Spec (CommRingCat.of ↥R)) (L₀ : RelativeGroupLaw ↥R f₀) (_ : L₀.IsCommutative)
      (_ : AbelianSchemePropertyBundle ↥R f₀)
      (_ : GeometricallyConnected f₀)
      (act₀ : ↥Λ → (A₀ ⟶ A₀)) (hact_over₀ : ∀ x : ↥Λ, act₀ x ≫ f₀ = f₀)
      (_ : ∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥R)) (P Q : SchemeHomOver t f₀),
        pushPt (act₀ x) (hact_over₀ x) (L₀.mul t P Q) = L₀.mul t (pushPt (act₀ x) (hact_over₀ x) P) (pushPt (act₀ x) (hact_over₀ x) Q))
      (_ : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, act₀ ⟨1, h⟩ = 𝟙 A₀)
      (_ : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
        act₀ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = act₀ y ≫ act₀ x)
      (_ : ∀ (x y : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥R)) (P : SchemeHomOver t f₀),
        pushPt (act₀ (x + y)) (hact_over₀ (x + y)) P =
          L₀.mul t (pushPt (act₀ x) (hact_over₀ x) P) (pushPt (act₀ y) (hact_over₀ y) P))
      (C₀ : Scheme.{0}) (lev₀ : C₀ ⟶ A₀) (_ : IsClosedImmersion lev₀)
      (_ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥R)) (P Q : SchemeHomOver t f₀),
        FactorsThrough lev₀ P → FactorsThrough lev₀ Q → FactorsThrough lev₀ (L₀.mul t P Q) ∧ FactorsThrough lev₀ (L₀.inv t P))
      (_ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥R)), FactorsThrough lev₀ (L₀.one t))
      (_ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥R)) (P : SchemeHomOver t f₀),
        FactorsThrough lev₀ P → nsmulPt L₀ t N P = L₀.one t)
      (_ : ∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥R)) (P : SchemeHomOver t f₀),
        FactorsThrough lev₀ P → FactorsThrough lev₀ (pushPt (act₀ x) (hact_over₀ x) P))
      (_ : IsFinite (lev₀ ≫ f₀)) (_ : Flat (lev₀ ≫ f₀)) (_ : LocallyOfFinitePresentation (lev₀ ≫ f₀))
      (g : E.A ⟶ A₀) (hg : CategoryTheory.IsPullback g E.f f₀ (Spec.map (CommRingCat.ofHom R.val.toRingHom)))
      (gC : E.C ⟶ C₀) (_ : CategoryTheory.IsPullback gC E.lev lev₀ g),
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of L)) (P Q : SchemeHomOver t' E.f),
        (E.L.mul t' P Q).1 ≫ g =
          (L₀.mul (t' ≫ Spec.map (CommRingCat.ofHom R.val.toRingHom))
            ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1) ∧
      (∀ x : ↥Λ, E.act x ≫ g = g ≫ act₀ x) := by
  haveI := hgc₁
  haveI := hci₁
  haveI := hfin₁
  haveI := hflat₁
  haveI := hlfp₁
  have hj : Spec.map (CommRingCat.ofHom T.val.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥R₁ ↥T)) =
      Spec.map (CommRingCat.ofHom R₁.val.toRingHom) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; rfl
  have hfg : (T.restrictScalars ℤ).FG := by
    have i1 : Algebra.FiniteType ℤ ↥R₁ := (Subalgebra.fg_iff_finiteType _).1 hR₁fg
    have i2 : Algebra.FiniteType ↥R₁ ↥T := (Subalgebra.fg_iff_finiteType _).1 hT
    have i3 : Algebra.FiniteType ℤ ↥T := Algebra.FiniteType.trans i1 i2
    exact (Subalgebra.fg_iff_finiteType (T.restrictScalars ℤ)).2 i3
  obtain ⟨hover', hhom', hone', hmul', hadd'⟩ :=
    RawLev20.actLaws_bc Λ (Spec.map (CommRingCat.ofHom (algebraMap ↥R₁ ↥T))) L₁ act₁ hover₁ hhom₁ hone₁ hmul₁ hadd₁
  obtain ⟨hg', hmulc', hactc'⟩ :=
    RawLev20.cmp_bc Λ (Spec.map (CommRingCat.ofHom (algebraMap ↥R₁ ↥T))) L₁ act₁ hover₁ E.f E.L E.act _ _ hj g₁ hg₁ E.act_over hmulg₁ hactg₁
  refine ⟨T.restrictScalars ℤ, hfg, fun x hx => T.algebraMap_mem ⟨x, hsR₁ hx⟩,
    pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥R₁ ↥T))), pullback.snd f₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥R₁ ↥T))), L₁.baseChange (Spec.map (CommRingCat.ofHom (algebraMap ↥R₁ ↥T))),
    GoodReductionJacobian.RelativeGroupLaw.IsCommutative.baseChange (Spec.map (CommRingCat.ofHom (algebraMap ↥R₁ ↥T))) hcomm₁,
    NoethBC20.abelianSchemePropertyBundle_bc (Spec.map (CommRingCat.ofHom (algebraMap ↥R₁ ↥T))) hb₁ (L₁.baseChange _),
    NoethBC20.geometricallyConnected_baseChangeStr (Spec.map (CommRingCat.ofHom (algebraMap ↥R₁ ↥T))),
    _, hover', hhom', hone', hmul', hadd',
    pullback (lev₁ ≫ f₁) (Spec.map (CommRingCat.ofHom (algebraMap ↥R₁ ↥T))), NoethBC20.bcLev (Spec.map (CommRingCat.ofHom (algebraMap ↥R₁ ↥T))) f₁ lev₁,
    NoethBC20.isClosedImmersion_bcLev (Spec.map (CommRingCat.ofHom (algebraMap ↥R₁ ↥T))) f₁ lev₁,
    fun t P Q => NoethBC20.lev_sub_bc' (Spec.map (CommRingCat.ofHom (algebraMap ↥R₁ ↥T))) f₁ lev₁ L₁ Hsub t P Q,
    fun t => NoethBC20.lev_one_bc' (Spec.map (CommRingCat.ofHom (algebraMap ↥R₁ ↥T))) f₁ lev₁ L₁ Hone t,
    fun t P => NoethBC20.lev_torsion_bc' (Spec.map (CommRingCat.ofHom (algebraMap ↥R₁ ↥T))) f₁ lev₁ L₁ N Htor t P,
    fun x {T₀} t P => NoethBC20.lev_stable_bc' (Spec.map (CommRingCat.ofHom (algebraMap ↥R₁ ↥T))) f₁ lev₁ (act₁ x) (hover₁ x) (Hst x) (hover' x) t P,
    NoethBC20.isFinite_bcLev_comp (Spec.map (CommRingCat.ofHom (algebraMap ↥R₁ ↥T))) f₁ lev₁,
    NoethBC20.flat_bcLev_comp (Spec.map (CommRingCat.ofHom (algebraMap ↥R₁ ↥T))) f₁ lev₁,
    NoethBC20.locallyOfFinitePresentation_bcLev_comp (Spec.map (CommRingCat.ofHom (algebraMap ↥R₁ ↥T))) f₁ lev₁,
    _, hg',
    NoethBC20.bcComparisonSub (Spec.map (CommRingCat.ofHom (algebraMap ↥R₁ ↥T))) E.f _ _ hj g₁ hg₁ lev₁ E.lev gC₁ hgC₁,
    NoethBC20.isPullback_bcComparisonSub (Spec.map (CommRingCat.ofHom (algebraMap ↥R₁ ↥T))) E.f _ _ hj g₁ hg₁ lev₁ E.lev gC₁ hgC₁,
    hmulc', hactc'⟩

end FinalBC
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_abelianScheme_act_level_isPullback.PkgDesc18 P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_abelianScheme_act_level_isPullback.LevDesc21"

noncomputable section

namespace LevDesc21

open scoped TensorProduct Quaternion NumberField
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM GoodReductionJacobian PkgDesc18

open NeronModelInfra (SchemeHomOver)

theorem fg_finset_sup {R L : Type} [CommRing R] [CommRing L] [Algebra R L] {ι' : Type} (Gs : Finset ι')
    (T : ι' → Subalgebra R L) (h : ∀ i ∈ Gs, (T i).FG) : (Gs.sup T).FG := by
  classical
  induction Gs using Finset.induction_on with
  | empty => simpa using Subalgebra.fg_bot
  | insert i G hi ih =>
    rw [Finset.sup_insert]
    exact (h i (Finset.mem_insert_self i G)).sup (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

theorem exists_stage
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsMaximalOrder Λ) {N : ℕ}
    {L : Type} [CommRing L] (E : FakeEllipticCurve Λ N L) (R₁ : Subalgebra ℤ L)
    {A₁ C₁ : Scheme.{0}} (f₁ : A₁ ⟶ Spec (CommRingCat.of ↥R₁)) (L₁ : RelativeGroupLaw ↥R₁ f₁)
    (act₁ : ↥Λ → (A₁ ⟶ A₁)) (hover₁ : ∀ x : ↥Λ, act₁ x ≫ f₁ = f₁)
    (hadd₁ : ∀ (x y : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥R₁)) (P : SchemeHomOver t f₁),
      pushPt (act₁ (x + y)) (hover₁ (x + y)) P =
        L₁.mul t (pushPt (act₁ x) (hover₁ x) P) (pushPt (act₁ y) (hover₁ y) P))
    (lev₁ : C₁ ⟶ A₁) [IsFinite (lev₁ ≫ f₁)] [LocallyOfFinitePresentation (lev₁ ≫ f₁)] [LocallyOfFiniteType f₁]
    (g₁ : E.A ⟶ A₁) (hg₁ : IsPullback g₁ E.f f₁ (ι L))
    (gC₁ : E.C ⟶ C₁) (hgC₁ : IsPullback gC₁ E.lev lev₁ g₁)
    (hmul : MulCompat L₁ E.L (ι L) g₁ hg₁) (hact : ∀ x : ↥Λ, E.act x ≫ g₁ = g₁ ≫ act₁ x) :
    ∃ T : Subalgebra ↥R₁ L, T.FG ∧
      (∀ {T' : Scheme.{0}} (t : T' ⟶ Spec (CommRingCat.of ↥T)) (P Q : SchemeHomOver (t ≫ ι ↥T) f₁),
        FactorsThrough lev₁ P → FactorsThrough lev₁ Q →
          FactorsThrough lev₁ (L₁.mul _ P Q) ∧ FactorsThrough lev₁ (L₁.inv _ P)) ∧
      (∀ {T' : Scheme.{0}} (t : T' ⟶ Spec (CommRingCat.of ↥T)), FactorsThrough lev₁ (L₁.one (t ≫ ι ↥T))) ∧
      (∀ {T' : Scheme.{0}} (t : T' ⟶ Spec (CommRingCat.of ↥T)) (P : SchemeHomOver (t ≫ ι ↥T) f₁),
        FactorsThrough lev₁ P → nsmulPt L₁ _ N P = L₁.one _) ∧
      (∀ (x : ↥Λ) {T' : Scheme.{0}} (t : T' ⟶ Spec (CommRingCat.of ↥T)) (P : SchemeHomOver (t ≫ ι ↥T) f₁),
        FactorsThrough lev₁ P → FactorsThrough lev₁ (pushPt (act₁ x) (hover₁ x) P)) := by
  classical

  obtain ⟨φm, hφm⟩ := factor_mul_of L₁ lev₁ (ι L)
    (fun t P Q hP hQ => (levSub_L L₁ lev₁ E.L E.lev (ι L) g₁ hg₁ gC₁ hgC₁ hmul E.lev_sub t P Q hP hQ).1)
  obtain ⟨φi, hφi⟩ := factor_inv_of L₁ lev₁ (ι L)
    (fun t P hP => (levSub_L L₁ lev₁ E.L E.lev (ι L) g₁ hg₁ gC₁ hgC₁ hmul E.lev_sub t P P hP hP).2)
  obtain ⟨φo, hφo⟩ := factor_one_of L₁ lev₁ (ι L)
    (fun t => levOne_L L₁ lev₁ E.L E.lev (ι L) g₁ hg₁ gC₁ hgC₁ hmul E.lev_one t)
  have htor := eq_torsion_of L₁ lev₁ (ι L) N
    (fun t P hP => levTorsion_L L₁ lev₁ E.L E.lev (ι L) g₁ hg₁ gC₁ hgC₁ hmul N E.lev_torsion t P hP)
  have hst : ∀ x : ↥Λ, ∃ σ : pullback (lev₁ ≫ f₁) (ι L) ⟶ C₁,
      σ ≫ lev₁ = pullback.fst (lev₁ ≫ f₁) (ι L) ≫ lev₁ ≫ act₁ x := fun x =>
    factor_act_of L₁ lev₁ (ι L) (act₁ x) (hover₁ x)
      (fun t P hP => levStable_L L₁ lev₁ E.L E.lev (ι L) g₁ hg₁ gC₁ hgC₁ (hover₁ x) (E.act_over x) (hact x)
        (E.lev_stable x) t P hP)

  obtain ⟨Tm, hTm, -, φm₀, hφm₀⟩ := exists_fg_factor (pullback.fst (lev₁ ≫ f₁) (lev₁ ≫ f₁) ≫ lev₁ ≫ f₁) f₁ lev₁
    (L₁.mul _ (uPt₁ lev₁) (uPt₂ lev₁)).1 (L₁.mul _ (uPt₁ lev₁) (uPt₂ lev₁)).2 φm hφm ∅
  obtain ⟨Ti, hTi, -, φi₀, hφi₀⟩ := exists_fg_factor (lev₁ ≫ f₁) f₁ lev₁
    (L₁.inv _ (uPt lev₁)).1 (L₁.inv _ (uPt lev₁)).2 φi hφi ∅
  obtain ⟨To, hTo, -, φo₀, hφo₀⟩ := exists_fg_factor (𝟙 _) f₁ lev₁
    (L₁.one (𝟙 _)).1 (L₁.one (𝟙 _)).2 φo hφo ∅
  obtain ⟨Tt, hTt, -, htor₀⟩ :=
    AlgebraicGeometry.exists_fg_subalgebra_pullback_fst_comp_eq_of_locallyOfFiniteType (A₀ := ↥R₁) (A := L)
      (lev₁ ≫ f₁) f₁ (nsmulPt L₁ _ N (uPt lev₁)).1 (L₁.one (lev₁ ≫ f₁)).1 (nsmulPt L₁ _ N (uPt lev₁)).2
      (L₁.one _).2 htor ∅
  have hx : ∀ x : ↥Λ, ∃ Tx : Subalgebra ↥R₁ L, Tx.FG ∧ ∃ σ₀ : pullback (lev₁ ≫ f₁) (ι ↥Tx) ⟶ C₁,
      σ₀ ≫ lev₁ = pullback.fst (lev₁ ≫ f₁) (ι ↥Tx) ≫ lev₁ ≫ act₁ x := fun x => by
    obtain ⟨σ, hσ⟩ := hst x
    obtain ⟨Tx, h1, -, σ₀, h2⟩ := exists_fg_factor (lev₁ ≫ f₁) f₁ lev₁ (lev₁ ≫ act₁ x)
      (by rw [Category.assoc, hover₁]) σ hσ ∅
    exact ⟨Tx, h1, σ₀, h2⟩
  choose Tx hTx σ₀ hσ₀ using hx

  obtain ⟨Gs, hGs⟩ := hΛ.isOrder.fg
  have hGsΛ : ∀ g ∈ Gs, g ∈ Λ := fun g hg => hGs ▸ Submodule.subset_span hg
  let GΛ : Finset ↥Λ := Gs.attach.image fun g => ⟨g.1, hGsΛ g.1 g.2⟩

  obtain ⟨T, hmT, hiT, hoT, htT, hxT, hTfg⟩ : ∃ T : Subalgebra ↥R₁ L, Tm ≤ T ∧ Ti ≤ T ∧ To ≤ T ∧ Tt ≤ T ∧
      (∀ x ∈ GΛ, Tx x ≤ T) ∧ T.FG :=
    ⟨Tm ⊔ Ti ⊔ To ⊔ Tt ⊔ GΛ.sup Tx,
      le_sup_left.trans (le_sup_left.trans (le_sup_left.trans le_sup_left)),
      le_sup_right.trans (le_sup_left.trans (le_sup_left.trans le_sup_left)),
      le_sup_right.trans (le_sup_left.trans le_sup_left),
      le_sup_right.trans le_sup_left,
      fun x hx' => (Finset.le_sup hx').trans le_sup_right,
      (((hTm.sup hTi).sup hTo).sup hTt).sup (fg_finset_sup GΛ Tx fun x _ => hTx x)⟩

  obtain ⟨φmT, hφmT⟩ := factor_mono _ lev₁ _ hmT φm₀ hφm₀
  obtain ⟨φiT, hφiT⟩ := factor_mono _ lev₁ _ hiT φi₀ hφi₀
  obtain ⟨φoT, hφoT⟩ := factor_mono _ lev₁ _ hoT φo₀ hφo₀
  have htorT := eq_mono _ _ _ htT htor₀
  have Hsub : ∀ {T' : Scheme.{0}} (t : T' ⟶ Spec (CommRingCat.of ↥T)) (P Q : SchemeHomOver (t ≫ ι ↥T) f₁),
      FactorsThrough lev₁ P → FactorsThrough lev₁ Q →
        FactorsThrough lev₁ (L₁.mul _ P Q) ∧ FactorsThrough lev₁ (L₁.inv _ P) :=
    fun t P Q hP hQ => levSub_of L₁ lev₁ (ι ↥T) φmT hφmT φiT hφiT t P Q hP hQ
  have Hone : ∀ {T' : Scheme.{0}} (t : T' ⟶ Spec (CommRingCat.of ↥T)), FactorsThrough lev₁ (L₁.one (t ≫ ι ↥T)) :=
    fun t => levOne_of L₁ lev₁ (ι ↥T) φoT hφoT t
  refine ⟨T, hTfg, Hsub, Hone, fun t P hP => levTorsion_of L₁ lev₁ (ι ↥T) N htorT t P hP, ?_⟩

  intro x T' t P hP
  refine stable_closure L₁ lev₁ (ι ↥T) act₁ hover₁ hadd₁ Hone Hsub (↑Gs) hGs ?_ x T' t P hP
  intro g hgG hg T'' t' P' hP'
  have hmem : (⟨g, hg⟩ : ↥Λ) ∈ GΛ := Finset.mem_image.2 ⟨⟨g, hgG⟩, Finset.mem_attach _ _, rfl⟩
  obtain ⟨σT, hσT⟩ := factor_mono _ lev₁ _ (hxT _ hmem) (σ₀ ⟨g, hg⟩) (hσ₀ ⟨g, hg⟩)
  exact levStable_of L₁ lev₁ (ι ↥T) (act₁ ⟨g, hg⟩) (hover₁ ⟨g, hg⟩) σT hσT t' P' hP'

end LevDesc21
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_abelianScheme_act_level_isPullback.PkgDesc18 P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_abelianScheme_act_level_isPullback.LevDesc21"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_abelianScheme_act_level_isPullback.PkgDesc18 P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_abelianScheme_act_level_isPullback.LevDesc21"

open scoped TensorProduct Quaternion NumberField
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

theorem solution
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (N : ℕ)
    (L : Type) [CommRing L] (E : FakeEllipticCurve Λ N L) (s : Finset L) :
    ∃ (R : Subalgebra ℤ L) (_ : R.FG) (_ : (↑s : Set L) ⊆ R)
      (A₀ : Scheme.{0}) (f₀ : A₀ ⟶ Spec (CommRingCat.of ↥R)) (L₀ : RelativeGroupLaw ↥R f₀) (_ : L₀.IsCommutative)
      (_ : AbelianSchemePropertyBundle ↥R f₀)
      (_ : GeometricallyConnected f₀)
      (act₀ : ↥Λ → (A₀ ⟶ A₀)) (hact_over₀ : ∀ x : ↥Λ, act₀ x ≫ f₀ = f₀)
      (_ : ∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥R)) (P Q : SchemeHomOver t f₀),
        pushPt (act₀ x) (hact_over₀ x) (L₀.mul t P Q) = L₀.mul t (pushPt (act₀ x) (hact_over₀ x) P) (pushPt (act₀ x) (hact_over₀ x) Q))
      (_ : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, act₀ ⟨1, h⟩ = 𝟙 A₀)
      (_ : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
        act₀ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = act₀ y ≫ act₀ x)
      (_ : ∀ (x y : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥R)) (P : SchemeHomOver t f₀),
        pushPt (act₀ (x + y)) (hact_over₀ (x + y)) P =
          L₀.mul t (pushPt (act₀ x) (hact_over₀ x) P) (pushPt (act₀ y) (hact_over₀ y) P))
      (C₀ : Scheme.{0}) (lev₀ : C₀ ⟶ A₀) (_ : IsClosedImmersion lev₀)
      (_ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥R)) (P Q : SchemeHomOver t f₀),
        FactorsThrough lev₀ P → FactorsThrough lev₀ Q → FactorsThrough lev₀ (L₀.mul t P Q) ∧ FactorsThrough lev₀ (L₀.inv t P))
      (_ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥R)), FactorsThrough lev₀ (L₀.one t))
      (_ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥R)) (P : SchemeHomOver t f₀),
        FactorsThrough lev₀ P → nsmulPt L₀ t N P = L₀.one t)
      (_ : ∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥R)) (P : SchemeHomOver t f₀),
        FactorsThrough lev₀ P → FactorsThrough lev₀ (pushPt (act₀ x) (hact_over₀ x) P))
      (_ : IsFinite (lev₀ ≫ f₀)) (_ : Flat (lev₀ ≫ f₀)) (_ : LocallyOfFinitePresentation (lev₀ ≫ f₀))
      (g : E.A ⟶ A₀) (hg : CategoryTheory.IsPullback g E.f f₀ (Spec.map (CommRingCat.ofHom R.val.toRingHom)))
      (gC : E.C ⟶ C₀) (_ : CategoryTheory.IsPullback gC E.lev lev₀ g),
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of L)) (P Q : SchemeHomOver t' E.f),
        (E.L.mul t' P Q).1 ≫ g =
          (L₀.mul (t' ≫ Spec.map (CommRingCat.ofHom R.val.toRingHom))
            ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1) ∧
      (∀ x : ↥Λ, E.act x ≫ g = g ≫ act₀ x) := by
  obtain ⟨R₁, hR₁fg, hsR₁, A₁, f₁, L₁, hcomm₁, hb₁, hgc₁, act₁, hover₁, hhom₁, hone₁, hmul₁, hadd₁, C₁, lev₁, hci₁,
    hfin₁, hflat₁, hlfp₁, g₁, hg₁, gC₁, hgC₁, hmulg₁, hactg₁⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_fg_subalgebra_abelianScheme_act_levelData_isPullback Λ hΛ N L E s
  haveI := hfin₁
  haveI := hlfp₁
  haveI := hb₁.proper
  obtain ⟨T, hT, Hsub, Hone, Htor, Hst⟩ :=
    LevDesc21.exists_stage hΛ E R₁ f₁ L₁ act₁ hover₁ hadd₁ lev₁ g₁ hg₁ gC₁ hgC₁ hmulg₁ hactg₁
  exact LevDesc21.final_bc Λ N L E s R₁ hR₁fg hsR₁ A₁ f₁ L₁ hcomm₁ hb₁ hgc₁ act₁ hover₁ hhom₁ hone₁ hmul₁ hadd₁ C₁ lev₁
    hci₁ hfin₁ hflat₁ hlfp₁ g₁ hg₁ gC₁ hgC₁ hmulg₁ hactg₁ T hT Hsub Hone Htor Hst

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_abelianScheme_act_level_isPullback
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_abelianScheme_act_level_isPullback (solution)
