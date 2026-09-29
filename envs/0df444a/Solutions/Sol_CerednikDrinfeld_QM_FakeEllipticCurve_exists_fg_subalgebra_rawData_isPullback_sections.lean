-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_fg_subalgebra_rawData_isPullback_sections
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/8a958096-5d5a-55d4-89ea-7b1bf4066ed5

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_abelianScheme_act_level_isPullback
import Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_forall_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_rawData_isPullback_sections
p2m_attr_erase "instance" "IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing"
p2m_attr_erase "instance" "TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec"
p2m_attr_erase "simp" "TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq"
p2m_attr_erase "simp" "DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false

noncomputable section

universe u

open scoped TensorProduct Quaternion NumberField
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian GoodReductionJacobian.RelativeGroupLaw

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

end Comparison

end NoethBC20

namespace RawDescend20

open NoethBC20

section Sections

variable {R₁ : Type u} [CommRing R₁] {T : Type u} [CommRing T] {S : Type u} [CommRing S]
variable (jL : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R₁))
variable (ι : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R₁))
variable (jT : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of T)) (hj : jT ≫ ι = jL)
variable {A₁ : Scheme.{u}} (f₁ : A₁ ⟶ Spec (CommRingCat.of R₁))
variable {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of S)) (g : X ⟶ A₁) (hg : IsPullback g p f₁ jL)

def secMor (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) p) :
    pullback (𝟙 (Spec (CommRingCat.of R₁))) jL ⟶ pullback f₁ jL :=
  pullback.snd (𝟙 _) jL ≫ P.1 ≫ pullback.lift g p hg.w

theorem secMor_snd (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) p) :
    secMor jL f₁ p g hg P ≫ pullback.snd f₁ jL = pullback.snd (𝟙 _) jL := by
  simp only [secMor, Category.assoc, pullback.lift_snd]
  rw [P.2, Category.comp_id]

def secOfMor (g₀ : pullback (𝟙 (Spec (CommRingCat.of R₁))) ι ⟶ pullback f₁ ι)
    (hg₀ : g₀ ≫ pullback.snd f₁ ι = pullback.snd (𝟙 _) ι) :
    SchemeHomOver (𝟙 (Spec (CommRingCat.of T))) (baseChangeStr ι f₁) :=
  ⟨pullback.lift ι (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) ≫ g₀, by
    rw [Category.assoc]
    change _ ≫ g₀ ≫ pullback.snd f₁ ι = _
    rw [hg₀, pullback.lift_snd]⟩

theorem coe_comp_bcComparison_eq (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) p)
    (g₀ : pullback (𝟙 (Spec (CommRingCat.of R₁))) ι ⟶ pullback f₁ ι)
    (hg₀ : g₀ ≫ pullback.snd f₁ ι = pullback.snd (𝟙 _) ι)
    (hcmp : ∀ (q₁ : pullback (𝟙 (Spec (CommRingCat.of R₁))) jL ⟶ pullback (𝟙 (Spec (CommRingCat.of R₁))) ι)
        (q₂ : pullback f₁ jL ⟶ pullback f₁ ι),
      q₁ ≫ pullback.fst _ _ = pullback.fst _ _ → q₁ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ jT →
      q₂ ≫ pullback.fst _ _ = pullback.fst _ _ → q₂ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ jT →
      q₁ ≫ g₀ = secMor jL f₁ p g hg P ≫ q₂) :
    P.1 ≫ bcComparison ι p jL jT hj g hg = jT ≫ (secOfMor ι f₁ g₀ hg₀).1 := by

  let q₁ : pullback (𝟙 (Spec (CommRingCat.of R₁))) jL ⟶ pullback (𝟙 (Spec (CommRingCat.of R₁))) ι :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ jT) (by rw [Category.assoc, hj]; exact pullback.condition)
  let q₂ : pullback f₁ jL ⟶ pullback f₁ ι :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ jT) (by rw [Category.assoc, hj]; exact pullback.condition)
  have hq := hcmp q₁ q₂ (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) (pullback.lift_fst _ _ _)
    (pullback.lift_snd _ _ _)

  let v : Spec (CommRingCat.of S) ⟶ pullback (𝟙 (Spec (CommRingCat.of R₁))) jL :=
    pullback.lift jL (𝟙 _) (by rw [Category.comp_id, Category.id_comp])
  have h1 : pullback.lift g p hg.w ≫ q₂ = bcComparison ι p jL jT hj g hg := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, bcComparison_fst]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd, bcComparison_snd]
  have h2 : v ≫ q₁ = jT ≫ pullback.lift ι (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.assoc, pullback.lift_fst, hj]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd, Category.id_comp, Category.assoc,
        pullback.lift_snd, Category.comp_id]
  have h3 : v ≫ secMor jL f₁ p g hg P = P.1 ≫ pullback.lift g p hg.w := by
    simp only [secMor, v, ← Category.assoc, pullback.lift_snd, Category.id_comp]
  calc P.1 ≫ bcComparison ι p jL jT hj g hg = (v ≫ secMor jL f₁ p g hg P) ≫ q₂ := by
        rw [h3, Category.assoc, h1]
    _ = (v ≫ q₁) ≫ g₀ := by rw [Category.assoc, Category.assoc, hq]
    _ = jT ≫ (secOfMor ι f₁ g₀ hg₀).1 := by rw [h2, Category.assoc]; rfl

end Sections

section Misc

theorem specMap_val_comp (L : Type) [CommRing L] (R₁ : Subalgebra ℤ L) (T : Subalgebra ↥R₁ L) :
    Spec.map (CommRingCat.ofHom T.val.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥R₁ ↥T)) =
      Spec.map (CommRingCat.ofHom R₁.val.toRingHom) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem fg_restrictScalars (L : Type) [CommRing L] (R₁ : Subalgebra ℤ L) (T : Subalgebra ↥R₁ L)
    (hR : R₁.FG) (hT : T.FG) : (T.restrictScalars ℤ).FG := by
  have i1 : Algebra.FiniteType ℤ ↥R₁ := (Subalgebra.fg_iff_finiteType _).1 hR
  have i2 : Algebra.FiniteType ↥R₁ ↥T := (Subalgebra.fg_iff_finiteType _).1 hT
  have i3 : Algebra.FiniteType ℤ ↥T := Algebra.FiniteType.trans i1 i2
  exact (Subalgebra.fg_iff_finiteType (T.restrictScalars ℤ)).2 i3

end Misc

end RawDescend20

theorem solution
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (N : ℕ)
    (L : Type) [CommRing L] (E : FakeEllipticCurve Λ N L) (s : Finset L)
    {n : ℕ} (P : Fin n → SchemeHomOver (𝟙 (Spec (CommRingCat.of L))) E.f) :
    ∃ (R : Subalgebra ℤ L) (_ : R.FG) (_ : (↑s : Set L) ⊆ R)
      (A₀ : Scheme.{0}) (f₀ : A₀ ⟶ Spec (CommRingCat.of ↥R)) (L₀ : RelativeGroupLaw ↥R f₀) (_ : L₀.IsCommutative)
      (_ : AbelianSchemePropertyBundle ↥R f₀)
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
      (P' : Fin n → SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥R))) f₀)
      (g : E.A ⟶ A₀) (hg : CategoryTheory.IsPullback g E.f f₀ (Spec.map (CommRingCat.ofHom R.val.toRingHom)))
      (gC : E.C ⟶ C₀) (_ : CategoryTheory.IsPullback gC E.lev lev₀ g),
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of L)) (P Q : SchemeHomOver t' E.f),
        (E.L.mul t' P Q).1 ≫ g =
          (L₀.mul (t' ≫ Spec.map (CommRingCat.ofHom R.val.toRingHom))
            ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1) ∧
      (∀ x : ↥Λ, E.act x ≫ g = g ≫ act₀ x) ∧
      (∀ k, (P k).1 ≫ g = Spec.map (CommRingCat.ofHom R.val.toRingHom) ≫ (P' k).1) := by
  classical

  obtain ⟨R₁, hR₁, hs₁, A₁, f₁, L₁, hc₁, hb₁, hgc₁, act₁, hover₁, hhom₁, hone₁, hmul₁, hadd₁, C₁, lev₁, hcl₁, hsub₁,
    hone'₁, htor₁, hst₁, hfin₁, hfl₁, hlfp₁, g₁, hg₁, gC₁, hgC₁, hmulc₁, hactc₁⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_fg_subalgebra_abelianScheme_act_level_isPullback Λ hΛ N L E s
  haveI := hgc₁
  haveI := hb₁.smooth
  haveI := hcl₁
  haveI := hfin₁
  haveI := hfl₁
  haveI := hlfp₁

  have hg₁' : IsPullback g₁ E.f f₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥R₁ L))) := hg₁
  obtain ⟨T, hT, hsT, g₀, hg₀, hcmp⟩ :=
    AlgebraicGeometry.exists_fg_subalgebra_forall_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation
      (ι := Fin n) (fun _ => 𝟙 (Spec (CommRingCat.of ↥R₁))) (fun _ => f₁)
      (fun k => RawDescend20.secMor _ f₁ E.f g₁ hg₁' (P k)) (fun k => RawDescend20.secMor_snd _ f₁ E.f g₁ hg₁' (P k)) s

  have hj : Spec.map (CommRingCat.ofHom T.val.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥R₁ ↥T)) =
      Spec.map (CommRingCat.ofHom R₁.val.toRingHom) := RawDescend20.specMap_val_comp L R₁ T
  refine ⟨T.restrictScalars ℤ, RawDescend20.fg_restrictScalars L R₁ T hR₁ hT, fun x hx => hsT hx,
    pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥R₁ ↥T))),
    pullback.snd f₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥R₁ ↥T))),
    L₁.baseChange (Spec.map (CommRingCat.ofHom (algebraMap ↥R₁ ↥T))),
    hc₁.baseChange _,
    NoethBC20.abelianSchemePropertyBundle_bc _ hb₁ (L₁.baseChange _),
    fun x => NoethBC20.bcEndo _ (act₁ x) (hover₁ x),
    fun x => NoethBC20.bcEndo_over _ (act₁ x) (hover₁ x),
    fun x {T₀} t P Q => NoethBC20.pushPt_bcEndo_mul _ (act₁ x) (hover₁ x) L₁ (hhom₁ x) _ t P Q,
    fun h => NoethBC20.bcEndo_eq_id _ (hone₁ h) _,
    fun x y h => NoethBC20.bcEndo_eq_comp _ (hmul₁ x y h) _ _ _,
    fun x y {T₀} t P => NoethBC20.pushPt_bcEndo_add _ (act₁ x) (hover₁ x) L₁ (hover₁ (x + y)) (hover₁ y) (hadd₁ x y) _ _ _ t P,
    pullback (lev₁ ≫ f₁) (Spec.map (CommRingCat.ofHom (algebraMap ↥R₁ ↥T))),
    NoethBC20.bcLev _ f₁ lev₁,
    NoethBC20.isClosedImmersion_bcLev _ f₁ lev₁,
    fun t P Q => NoethBC20.lev_sub_bc _ f₁ lev₁ L₁ hsub₁ t P Q,
    fun t => NoethBC20.lev_one_bc _ f₁ lev₁ L₁ hone'₁ t,
    fun t P => NoethBC20.lev_torsion_bc _ f₁ lev₁ L₁ N htor₁ t P,
    fun x {T₀} t P => NoethBC20.lev_stable_bc _ f₁ lev₁ (act₁ x) (hover₁ x) (hst₁ x) _ t P,
    NoethBC20.isFinite_bcLev_comp _ f₁ lev₁,
    NoethBC20.flat_bcLev_comp _ f₁ lev₁,
    NoethBC20.locallyOfFinitePresentation_bcLev_comp _ f₁ lev₁,
    fun k => RawDescend20.secOfMor _ f₁ (g₀ k) (hg₀ k),
    NoethBC20.bcComparison _ E.f _ _ hj g₁ hg₁,
    NoethBC20.isPullback_bcComparison _ E.f _ _ hj g₁ hg₁,
    NoethBC20.bcComparisonSub _ E.f _ _ hj g₁ hg₁ lev₁ E.lev gC₁ hgC₁,
    NoethBC20.isPullback_bcComparisonSub _ E.f _ _ hj g₁ hg₁ lev₁ E.lev gC₁ hgC₁,
    fun t' P Q => NoethBC20.mul_coe_comp_bcComparison _ E.f _ _ hj g₁ hg₁ E.L L₁ hmulc₁ t' P Q,
    fun x => NoethBC20.comp_bcComparison_eq_bcComparison_comp_bcEndo _ E.f _ _ hj g₁ hg₁ (act₁ x) (hover₁ x)
      (E.act x) (E.act_over x) (hactc₁ x),
    fun k => RawDescend20.coe_comp_bcComparison_eq _ _ _ hj f₁ E.f g₁ hg₁' (P k) (g₀ k) (hg₀ k) (hcmp k)⟩

end
end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_rawData_isPullback_sections
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_rawData_isPullback_sections (solution)
