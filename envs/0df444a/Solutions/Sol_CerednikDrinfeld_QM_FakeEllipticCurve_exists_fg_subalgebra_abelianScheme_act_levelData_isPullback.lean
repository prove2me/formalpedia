-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_fg_subalgebra_abelianScheme_act_levelData_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/ab019c01-38f6-58e6-b8aa-02977e52139e

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_abelianScheme_act_isPullback
import Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_isFinite_flat_isPullback_of_isFinite_of_flat_of_locallyOfFinitePresentation
import Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation
import Theorems.Thm_AlgebraicGeometry_IsClosedImmersion_exists_fg_subalgebra_of_isClosedImmersion_pullback_map_of_quasiCompact
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_abelianScheme_act_levelData_isPullback
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

namespace RawLev20

open NoethBC20

section Flat

variable (L : Type) [CommRing L]

theorem specMap_val_comp' (T : Subalgebra ℤ L) (T' : Subalgebra ↥T L) :
    Spec.map (CommRingCat.ofHom T'.val.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥T ↥T')) =
      Spec.map (CommRingCat.ofHom T.val.toRingHom) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem fg_restrictScalars' (T : Subalgebra ℤ L) (T' : Subalgebra ↥T L) (hT : T.FG) (hT' : T'.FG) :
    (T'.restrictScalars ℤ).FG := by
  have i1 : Algebra.FiniteType ℤ ↥T := (Subalgebra.fg_iff_finiteType _).1 hT
  have i2 : Algebra.FiniteType ↥T ↥T' := (Subalgebra.fg_iff_finiteType _).1 hT'
  have i3 : Algebra.FiniteType ℤ ↥T' := Algebra.FiniteType.trans i1 i2
  exact (Subalgebra.fg_iff_finiteType (T'.restrictScalars ℤ)).2 i3

theorem exists_flat_finiteModel (T : Subalgebra ℤ L) (hT : T.FG) {X : Scheme.{0}}
    (g : X ⟶ Spec (CommRingCat.of L)) [IsFinite g] [Flat g] [LocallyOfFinitePresentation g] (s : Finset L) :
    ∃ (T' : Subalgebra ℤ L) (_ : T'.FG) (_ : (↑s : Set L) ⊆ T')
      (ι : Spec (CommRingCat.of ↥T') ⟶ Spec (CommRingCat.of ↥T))
      (_ : Spec.map (CommRingCat.ofHom T'.val.toRingHom) ≫ ι = Spec.map (CommRingCat.ofHom T.val.toRingHom))
      (X₀ : Scheme.{0}) (f₀ : X₀ ⟶ Spec (CommRingCat.of ↥T')) (π : X ⟶ X₀),
      IsFinite f₀ ∧ Flat f₀ ∧ LocallyOfFinitePresentation f₀ ∧
        IsPullback π g f₀ (Spec.map (CommRingCat.ofHom T'.val.toRingHom)) := by
  haveI : Algebra.FiniteType ℤ ↥T := (Subalgebra.fg_iff_finiteType _).1 hT
  haveI : IsNoetherianRing ↥T := Algebra.FiniteType.isNoetherianRing ℤ ↥T
  obtain ⟨T', hT', hs, X₀, f₀, π, h1, h2, h3, hπ⟩ :=
    AlgebraicGeometry.exists_fg_subalgebra_isFinite_flat_isPullback_of_isFinite_of_flat_of_locallyOfFinitePresentation
      (A₀ := ↥T) g s
  exact ⟨T'.restrictScalars ℤ, fg_restrictScalars' L T T' hT hT', hs, Spec.map (CommRingCat.ofHom (algebraMap ↥T ↥T')),
    specMap_val_comp' L T T', X₀, f₀, π, h1, h2, h3, hπ⟩

theorem exists_flat_homDescend (T : Subalgebra ℤ L) (hT : T.FG) {X₁ X₂ : Scheme.{0}}
    (f₁ : X₁ ⟶ Spec (CommRingCat.of ↥T)) (f₂ : X₂ ⟶ Spec (CommRingCat.of ↥T))
    [QuasiCompact f₁] [QuasiSeparated f₁] [LocallyOfFinitePresentation f₂]
    (g : pullback f₁ (Spec.map (CommRingCat.ofHom T.val.toRingHom)) ⟶
      pullback f₂ (Spec.map (CommRingCat.ofHom T.val.toRingHom)))
    (hg : g ≫ pullback.snd f₂ _ = pullback.snd f₁ _) (s : Finset L) :
    ∃ (T' : Subalgebra ℤ L) (_ : T'.FG) (_ : (↑s : Set L) ⊆ T')
      (ι : Spec (CommRingCat.of ↥T') ⟶ Spec (CommRingCat.of ↥T))
      (_ : Spec.map (CommRingCat.ofHom T'.val.toRingHom) ≫ ι = Spec.map (CommRingCat.ofHom T.val.toRingHom))
      (g₀ : pullback f₁ ι ⟶ pullback f₂ ι),
      g₀ ≫ pullback.snd f₂ ι = pullback.snd f₁ ι ∧
      ∀ (q₁ : pullback f₁ (Spec.map (CommRingCat.ofHom T.val.toRingHom)) ⟶ pullback f₁ ι)
        (q₂ : pullback f₂ (Spec.map (CommRingCat.ofHom T.val.toRingHom)) ⟶ pullback f₂ ι),
        q₁ ≫ pullback.fst f₁ ι = pullback.fst f₁ _ →
        q₁ ≫ pullback.snd f₁ ι = pullback.snd f₁ _ ≫ Spec.map (CommRingCat.ofHom T'.val.toRingHom) →
        q₂ ≫ pullback.fst f₂ ι = pullback.fst f₂ _ →
        q₂ ≫ pullback.snd f₂ ι = pullback.snd f₂ _ ≫ Spec.map (CommRingCat.ofHom T'.val.toRingHom) →
        q₁ ≫ g₀ = g ≫ q₂ := by
  obtain ⟨T', hT', hs, g₀, hg₀, hcmp⟩ :=
    AlgebraicGeometry.exists_fg_subalgebra_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation
      (A₀ := ↥T) (A := L) f₁ f₂ g hg s
  exact ⟨T'.restrictScalars ℤ, fg_restrictScalars' L T T' hT hT', hs, Spec.map (CommRingCat.ofHom (algebraMap ↥T ↥T')),
    specMap_val_comp' L T T', g₀, hg₀, hcmp⟩

theorem exists_flat_closedImmDescend (T : Subalgebra ℤ L) (hT : T.FG) {W V : Scheme.{0}}
    (m : W ⟶ V) (v : V ⟶ Spec (CommRingCat.of ↥T)) [QuasiCompact v]
    [QuasiCompact m] [QuasiSeparated m] [LocallyOfFiniteType m]
    (hA : ∀ mA : pullback (m ≫ v) (Spec.map (CommRingCat.ofHom T.val.toRingHom)) ⟶
        pullback v (Spec.map (CommRingCat.ofHom T.val.toRingHom)),
      mA ≫ pullback.fst _ _ = pullback.fst _ _ ≫ m → mA ≫ pullback.snd _ _ = pullback.snd _ _ → IsClosedImmersion mA)
    (s : Finset L) :
    ∃ (T' : Subalgebra ℤ L) (_ : T'.FG) (_ : (↑s : Set L) ⊆ T')
      (ι : Spec (CommRingCat.of ↥T') ⟶ Spec (CommRingCat.of ↥T))
      (_ : Spec.map (CommRingCat.ofHom T'.val.toRingHom) ≫ ι = Spec.map (CommRingCat.ofHom T.val.toRingHom)),
      ∀ mT : pullback (m ≫ v) ι ⟶ pullback v ι,
        mT ≫ pullback.fst _ _ = pullback.fst _ _ ≫ m → mT ≫ pullback.snd _ _ = pullback.snd _ _ → IsClosedImmersion mT := by
  obtain ⟨T', hT', hs, H⟩ :=
    AlgebraicGeometry.IsClosedImmersion.exists_fg_subalgebra_of_isClosedImmersion_pullback_map_of_quasiCompact
      (A₀ := ↥T) (A := L) m v hA s
  exact ⟨T'.restrictScalars ℤ, fg_restrictScalars' L T T' hT hT', hs, Spec.map (CommRingCat.ofHom (algebraMap ↥T ↥T')),
    specMap_val_comp' L T T', H⟩

end Flat

section Lev

variable {O : Type u} [CommRing O] {O' : Type u} [CommRing O'] {S : Type u} [CommRing S]
variable (j : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of O))
variable (ι : Spec (CommRingCat.of O') ⟶ Spec (CommRingCat.of O))
variable (j' : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of O')) (hj : j' ≫ ι = j)
variable {X₀ : Scheme.{u}} (c₀ : X₀ ⟶ Spec (CommRingCat.of O)) {A : Scheme.{u}} (fA : A ⟶ Spec (CommRingCat.of O))
variable {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of S)) {XC : Scheme.{u}} (pC : XC ⟶ X)
variable (π : XC ⟶ X₀) (hπ : IsPullback π (pC ≫ p) c₀ j) (gA : X ⟶ A) (hgA : IsPullback gA p fA j)

def levMor : pullback c₀ j ⟶ pullback fA j :=
  hπ.isoPullback.inv ≫ pC ≫ pullback.lift gA p hgA.w

theorem levMor_snd : levMor j c₀ fA p pC π hπ gA hgA ≫ pullback.snd fA j = pullback.snd c₀ j := by
  simp only [levMor, Category.assoc, pullback.lift_snd]
  exact hπ.isoPullback_inv_snd

theorem bcComparison_comp_eq (lev₂ : pullback c₀ ι ⟶ pullback fA ι)
    (hcmp : ∀ (q₁ : pullback c₀ j ⟶ pullback c₀ ι) (q₂ : pullback fA j ⟶ pullback fA ι),
      q₁ ≫ pullback.fst c₀ ι = pullback.fst c₀ j → q₁ ≫ pullback.snd c₀ ι = pullback.snd c₀ j ≫ j' →
      q₂ ≫ pullback.fst fA ι = pullback.fst fA j → q₂ ≫ pullback.snd fA ι = pullback.snd fA j ≫ j' →
      q₁ ≫ lev₂ = levMor j c₀ fA p pC π hπ gA hgA ≫ q₂) :
    bcComparison ι (pC ≫ p) j j' hj π hπ ≫ lev₂ = pC ≫ bcComparison ι p j j' hj gA hgA := by
  let q₁ : pullback c₀ j ⟶ pullback c₀ ι :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ j') (by rw [Category.assoc, hj]; exact pullback.condition)
  let q₂ : pullback fA j ⟶ pullback fA ι :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ j') (by rw [Category.assoc, hj]; exact pullback.condition)
  have hq := hcmp q₁ q₂ (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) (pullback.lift_fst _ _ _)
    (pullback.lift_snd _ _ _)
  have e1 : hπ.isoPullback.hom ≫ q₁ = bcComparison ι (pC ≫ p) j j' hj π hπ := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, hπ.isoPullback_hom_fst, bcComparison_fst]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, hπ.isoPullback_hom_snd, bcComparison_snd]
  have e2 : pullback.lift gA p hgA.w ≫ q₂ = bcComparison ι p j j' hj gA hgA := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, bcComparison_fst]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd, bcComparison_snd]
  rw [← e1, Category.assoc, hq, levMor, Category.assoc, Category.assoc, e2, Iso.hom_inv_id_assoc]

omit hj in

theorem isPullback_of_comm {W V : Scheme.{u}} (κC : XC ⟶ W) (κA : X ⟶ V) (lev₂ : W ⟶ V)
    (v : V ⟶ Spec (CommRingCat.of O')) (w : W ⟶ Spec (CommRingCat.of O')) (hw : lev₂ ≫ v = w)
    (hκC : IsPullback κC (pC ≫ p) w j') (hκA : IsPullback κA p v j') (comm : κC ≫ lev₂ = pC ≫ κA) :
    IsPullback κC pC lev₂ κA := by
  apply IsPullback.flip
  refine IsPullback.of_right (h₁₂ := p) (v₁₃ := j') (h₂₂ := v) ?_ comm.symm hκA.flip
  rw [hw]
  exact hκC.flip

omit hj in

theorem isClosedImmersion_of_comm {W V : Scheme.{u}} (κC : XC ⟶ W) (κA : X ⟶ V) (lev₂ : W ⟶ V)
    (v : V ⟶ Spec (CommRingCat.of O')) [IsClosedImmersion pC]
    (hκC : IsPullback κC (pC ≫ p) (lev₂ ≫ v) j') (hκA : IsPullback κA p v j') (comm : κC ≫ lev₂ = pC ≫ κA)
    (mA : pullback (lev₂ ≫ v) j' ⟶ pullback v j')
    (h1 : mA ≫ pullback.fst v j' = pullback.fst (lev₂ ≫ v) j' ≫ lev₂) (h2 : mA ≫ pullback.snd v j' = pullback.snd (lev₂ ≫ v) j') :
    IsClosedImmersion mA := by
  have e : hκC.isoPullback.hom ≫ mA = pC ≫ hκA.isoPullback.hom := by
    apply pullback.hom_ext
    · rw [Category.assoc, h1, ← Category.assoc, hκC.isoPullback_hom_fst, comm, Category.assoc, hκA.isoPullback_hom_fst]
    · rw [Category.assoc, h2, hκC.isoPullback_hom_snd, Category.assoc, hκA.isoPullback_hom_snd]
  have e' : mA = hκC.isoPullback.inv ≫ pC ≫ hκA.isoPullback.hom := by
    rw [← e, Iso.inv_hom_id_assoc]
  rw [e']
  infer_instance

end Lev

theorem qc_qs_loft_of_comp_eq {W V B : Scheme.{u}} (m : W ⟶ V) (v : V ⟶ B) (w : W ⟶ B) (hw : m ≫ v = w)
    [IsFinite w] [IsSeparated v] : QuasiCompact m ∧ QuasiSeparated m ∧ LocallyOfFiniteType m := by
  haveI : IsFinite (m ≫ v) := by rw [hw]; infer_instance
  haveI : IsAffineHom (m ≫ v) := inferInstance
  haveI : QuasiCompact (m ≫ v) := inferInstance
  haveI : QuasiSeparated (m ≫ v) := inferInstance
  haveI : LocallyOfFiniteType (m ≫ v) := inferInstance
  exact ⟨QuasiCompact.of_comp m v, QuasiSeparated.of_comp m v, locallyOfFiniteType_of_comp m v⟩

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

end RawLev20

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
      (_ : IsFinite (lev₀ ≫ f₀)) (_ : Flat (lev₀ ≫ f₀)) (_ : LocallyOfFinitePresentation (lev₀ ≫ f₀))
      (g : E.A ⟶ A₀) (hg : CategoryTheory.IsPullback g E.f f₀ (Spec.map (CommRingCat.ofHom R.val.toRingHom)))
      (gC : E.C ⟶ C₀) (_ : CategoryTheory.IsPullback gC E.lev lev₀ g),
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of L)) (P Q : SchemeHomOver t' E.f),
        (E.L.mul t' P Q).1 ≫ g =
          (L₀.mul (t' ≫ Spec.map (CommRingCat.ofHom R.val.toRingHom))
            ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1) ∧
      (∀ x : ↥Λ, E.act x ≫ g = g ≫ act₀ x) := by
  classical

  obtain ⟨R₁, hR₁, hs₁, A₁, f₁, L₁, hc₁, hb₁, hgc₁, act₁, hover₁, hhom₁, hone₁, hmul₁, hadd₁, g₁, hg₁, hmulc₁, hactc₁⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_fg_subalgebra_abelianScheme_act_isPullback Λ hΛ N L E s
  haveI := hgc₁
  haveI := hb₁.smooth
  haveI := hb₁.proper
  haveI := E.lev_closed
  haveI := E.lev_finite
  haveI := E.lev_flat
  haveI := E.lev_finitePresentation

  obtain ⟨T, hT, hsT, ι₁, hj₁, X₀, c₀, π, hfin₀, hfl₀, hlfp₀, hπ⟩ :=
    RawLev20.exists_flat_finiteModel L R₁ hR₁ (E.lev ≫ E.f) s
  haveI := hfin₀
  haveI := hfl₀
  haveI := hlfp₀

  obtain ⟨hoverT, hhomT, honeT, hmulT, haddT⟩ := RawLev20.actLaws_bc Λ ι₁ L₁ act₁ hover₁ hhom₁ hone₁ hmul₁ hadd₁
  obtain ⟨hgT, hmulcT, hactcT⟩ :=
    RawLev20.cmp_bc Λ ι₁ L₁ act₁ hover₁ E.f E.L E.act _ _ hj₁ g₁ hg₁ E.act_over hmulc₁ hactc₁

  obtain ⟨T₂, hT₂, hsT₂, ι₂, hj₂, lev₂, hlev₂, hcmp⟩ :=
    RawLev20.exists_flat_homDescend L T hT c₀ (pullback.snd f₁ ι₁)
      (RawLev20.levMor _ c₀ (pullback.snd f₁ ι₁) E.f E.lev π hπ _ hgT)
      (RawLev20.levMor_snd _ c₀ (pullback.snd f₁ ι₁) E.f E.lev π hπ _ hgT) s

  obtain ⟨hover₂, hhom₂, hone₂, hmul₂, hadd₂⟩ := RawLev20.actLaws_bc Λ ι₂ (L₁.baseChange ι₁) _ hoverT hhomT honeT hmulT haddT
  obtain ⟨hg₂, hmulc₂, hactc₂⟩ :=
    RawLev20.cmp_bc Λ ι₂ (L₁.baseChange ι₁) _ hoverT E.f E.L E.act _ _ hj₂ _ hgT E.act_over hmulcT hactcT
  have hκC := NoethBC20.isPullback_bcComparison ι₂ (E.lev ≫ E.f) _ _ hj₂ π hπ
  have hcomm := RawLev20.bcComparison_comp_eq _ ι₂ _ hj₂ c₀ (pullback.snd f₁ ι₁) E.f E.lev π hπ _ hgT lev₂ hcmp
  have hw : lev₂ ≫ pullback.snd (pullback.snd f₁ ι₁) ι₂ = pullback.snd c₀ ι₂ := hlev₂
  have hgC₂ := RawLev20.isPullback_of_comm _ E.f E.lev _ _ lev₂ _ _ hw hκC hg₂ hcomm
  have hκC' : IsPullback (NoethBC20.bcComparison ι₂ (E.lev ≫ E.f) _ _ hj₂ π hπ) (E.lev ≫ E.f)
      (lev₂ ≫ pullback.snd (pullback.snd f₁ ι₁) ι₂) (Spec.map (CommRingCat.ofHom T₂.val.toRingHom)) := by
    rw [hw]; exact hκC
  haveI : IsFinite (lev₂ ≫ pullback.snd (pullback.snd f₁ ι₁) ι₂) := by rw [hw]; infer_instance
  haveI : Flat (lev₂ ≫ pullback.snd (pullback.snd f₁ ι₁) ι₂) := by rw [hw]; infer_instance
  haveI : LocallyOfFinitePresentation (lev₂ ≫ pullback.snd (pullback.snd f₁ ι₁) ι₂) := by rw [hw]; infer_instance
  obtain ⟨hqc₂, hqs₂, hloft₂⟩ := RawLev20.qc_qs_loft_of_comp_eq lev₂ (pullback.snd (pullback.snd f₁ ι₁) ι₂) _ hw
  haveI := hqc₂
  haveI := hqs₂
  haveI := hloft₂

  obtain ⟨T₃, hT₃, hsT₃, ι₃, hj₃, H₃⟩ :=
    RawLev20.exists_flat_closedImmDescend L T₂ hT₂ lev₂ (pullback.snd (pullback.snd f₁ ι₁) ι₂)
      (fun mA h1 h2 => RawLev20.isClosedImmersion_of_comm _ E.f E.lev _ _ lev₂ _ hκC' hg₂ hcomm mA h1 h2) s

  obtain ⟨hover₃, hhom₃, hone₃, hmul₃, hadd₃⟩ :=
    RawLev20.actLaws_bc Λ ι₃ ((L₁.baseChange ι₁).baseChange ι₂) _ hover₂ hhom₂ hone₂ hmul₂ hadd₂
  obtain ⟨hg₃, hmulc₃, hactc₃⟩ :=
    RawLev20.cmp_bc Λ ι₃ ((L₁.baseChange ι₁).baseChange ι₂) _ hover₂ E.f E.L E.act _ _ hj₃ _ hg₂ E.act_over hmulc₂ hactc₂
  refine ⟨T₃, hT₃, hsT₃,
    pullback (pullback.snd (pullback.snd f₁ ι₁) ι₂) ι₃, pullback.snd _ ι₃,
    ((L₁.baseChange ι₁).baseChange ι₂).baseChange ι₃,
    RelativeGroupLaw.IsCommutative.baseChange ι₃
      (RelativeGroupLaw.IsCommutative.baseChange ι₂ (RelativeGroupLaw.IsCommutative.baseChange ι₁ hc₁)),
    NoethBC20.abelianSchemePropertyBundle_bc ι₃
      (NoethBC20.abelianSchemePropertyBundle_bc ι₂ (NoethBC20.abelianSchemePropertyBundle_bc ι₁ hb₁ (L₁.baseChange ι₁))
        ((L₁.baseChange ι₁).baseChange ι₂)) (((L₁.baseChange ι₁).baseChange ι₂).baseChange ι₃),
    NoethBC20.geometricallyConnected_baseChangeStr ι₃,
    _, hover₃, hhom₃, hone₃, hmul₃, hadd₃,
    pullback (lev₂ ≫ pullback.snd (pullback.snd f₁ ι₁) ι₂) ι₃,
    NoethBC20.bcLev ι₃ (pullback.snd (pullback.snd f₁ ι₁) ι₂) lev₂,
    H₃ _ (NoethBC20.bcLev_fst ι₃ _ lev₂) (NoethBC20.bcLev_snd ι₃ _ lev₂),
    NoethBC20.isFinite_bcLev_comp ι₃ _ lev₂,
    NoethBC20.flat_bcLev_comp ι₃ _ lev₂,
    NoethBC20.locallyOfFinitePresentation_bcLev_comp ι₃ _ lev₂,
    _, hg₃,
    NoethBC20.bcComparisonSub ι₃ E.f _ _ hj₃ _ hg₂ lev₂ E.lev _ hgC₂,
    NoethBC20.isPullback_bcComparisonSub ι₃ E.f _ _ hj₃ _ hg₂ lev₂ E.lev _ hgC₂,
    hmulc₃, hactc₃⟩

end
end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_abelianScheme_act_levelData_isPullback
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_abelianScheme_act_levelData_isPullback (solution)
