-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_fg_subalgebra_abelianScheme_endomorphisms_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/259ff1ea-d206-5a20-9a57-2ae4d54bd1dd

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_fg_subalgebra_abelianSchemePropertyBundle_isPullback_of_isNoetherianRing
import Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_forall_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_abelianScheme_endomorphisms_isPullback
p2m_attr_erase "instance" "IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing"
p2m_attr_erase "instance" "TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec"
p2m_attr_erase "simp" "TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq"
p2m_attr_erase "simp" "DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace NoethKit19

universe u

theorem mul_coe_congr {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)
    {T : Scheme.{u}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)} (h : t₁ = t₂) (x y : SchemeHomOver t₁ f) :
    (G.mul t₁ x y).1 = (G.mul t₂ ⟨x.1, h ▸ x.2⟩ ⟨y.1, h ▸ y.2⟩).1 := by
  subst h; rfl

section Compare

variable {R₁ : Type u} [CommRing R₁] {L : Type u} [CommRing L] [Algebra R₁ L] (T : Subalgebra R₁ L)
  {A₁ : Scheme.{u}} (f₁ : A₁ ⟶ Spec (CommRingCat.of R₁))

theorem specMap_val_comp :
    Spec.map (CommRingCat.ofHom T.val.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap R₁ ↥T)) =
      Spec.map (CommRingCat.ofHom (algebraMap R₁ L)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; rfl

theorem exists_transition :
    ∃ r : pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap R₁ L))) ⟶
        pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap R₁ ↥T))),
      r ≫ pullback.fst f₁ _ = pullback.fst f₁ _ ∧
      r ≫ pullback.snd f₁ _ = pullback.snd f₁ _ ≫ Spec.map (CommRingCat.ofHom T.val.toRingHom) :=
  ⟨pullback.lift (pullback.fst f₁ _) (pullback.snd f₁ _ ≫ Spec.map (CommRingCat.ofHom T.val.toRingHom))
      (by rw [Category.assoc, specMap_val_comp]; exact pullback.condition),
    pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

variable {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of L)} (π : X ⟶ A₁)
  (hπ : IsPullback π p f₁ (Spec.map (CommRingCat.ofHom (algebraMap R₁ L))))

theorem isPullback_comp_transition
    (r : pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap R₁ L))) ⟶
        pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap R₁ ↥T))))
    (hr_fst : r ≫ pullback.fst f₁ _ = pullback.fst f₁ _)
    (hr_snd : r ≫ pullback.snd f₁ _ = pullback.snd f₁ _ ≫ Spec.map (CommRingCat.ofHom T.val.toRingHom)) :
    IsPullback (hπ.isoPullback.hom ≫ r) p (pullback.snd f₁ (Spec.map (CommRingCat.ofHom (algebraMap R₁ ↥T))))
      (Spec.map (CommRingCat.ofHom T.val.toRingHom)) := by
  have hg_fst : (hπ.isoPullback.hom ≫ r) ≫ pullback.fst f₁ _ = π := by
    rw [Category.assoc, hr_fst, hπ.isoPullback_hom_fst]
  have hg_snd : (hπ.isoPullback.hom ≫ r) ≫ pullback.snd f₁ _ = p ≫ Spec.map (CommRingCat.ofHom T.val.toRingHom) := by
    rw [Category.assoc, hr_snd, ← Category.assoc, hπ.isoPullback_hom_snd]
  refine IsPullback.of_right (h₁₂ := pullback.fst f₁ _) (h₂₂ := Spec.map (CommRingCat.ofHom (algebraMap R₁ ↥T))) (v₁₃ := f₁)
    ?_ hg_snd (IsPullback.of_hasPullback f₁ _)
  rw [hg_fst, specMap_val_comp]; exact hπ

variable (L₁ : RelativeGroupLaw R₁ f₁) (G : RelativeGroupLaw L p)

theorem mul_comp_transition
    (hmul : ∀ {T' : Scheme.{u}} (t : T' ⟶ Spec (CommRingCat.of L)) (x y : SchemeHomOver t p),
      (G.mul t x y).1 ≫ π =
        (L₁.mul (t ≫ Spec.map (CommRingCat.ofHom (algebraMap R₁ L)))
          ⟨x.1 ≫ π, by rw [Category.assoc, hπ.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ π, by rw [Category.assoc, hπ.w, ← Category.assoc, y.2]⟩).1)
    (r : pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap R₁ L))) ⟶
        pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap R₁ ↥T))))
    (hr_fst : r ≫ pullback.fst f₁ _ = pullback.fst f₁ _)
    (hr_snd : r ≫ pullback.snd f₁ _ = pullback.snd f₁ _ ≫ Spec.map (CommRingCat.ofHom T.val.toRingHom))
    {T' : Scheme.{u}} (t' : T' ⟶ Spec (CommRingCat.of L)) (x y : SchemeHomOver t' p) :
    (G.mul t' x y).1 ≫ (hπ.isoPullback.hom ≫ r) =
      ((L₁.baseChange (Spec.map (CommRingCat.ofHom (algebraMap R₁ ↥T)))).mul
          (t' ≫ Spec.map (CommRingCat.ofHom T.val.toRingHom))
        ⟨x.1 ≫ (hπ.isoPullback.hom ≫ r), by
          rw [Category.assoc, (isPullback_comp_transition T f₁ π hπ r hr_fst hr_snd).w, ← Category.assoc, x.2]⟩
        ⟨y.1 ≫ (hπ.isoPullback.hom ≫ r), by
          rw [Category.assoc, (isPullback_comp_transition T f₁ π hπ r hr_fst hr_snd).w, ← Category.assoc, y.2]⟩).1 := by
  have hg_fst : (hπ.isoPullback.hom ≫ r) ≫ pullback.fst f₁ _ = π := by
    rw [Category.assoc, hr_fst, hπ.isoPullback_hom_fst]
  have hg_snd : (hπ.isoPullback.hom ≫ r) ≫ pullback.snd f₁ _ = p ≫ Spec.map (CommRingCat.ofHom T.val.toRingHom) := by
    rw [Category.assoc, hr_snd, ← Category.assoc, hπ.isoPullback_hom_snd]
  have ht : t' ≫ Spec.map (CommRingCat.ofHom (algebraMap R₁ L)) =
      (t' ≫ Spec.map (CommRingCat.ofHom T.val.toRingHom)) ≫ Spec.map (CommRingCat.ofHom (algebraMap R₁ ↥T)) := by
    rw [Category.assoc, specMap_val_comp]
  apply pullback.hom_ext
  · rw [Category.assoc, hg_fst, hmul t' x y, RelativeGroupLaw.baseChange_mul, RelativeGroupLaw.baseChangePointOfBase_coe,
      pullback.lift_fst, mul_coe_congr L₁ ht]
    congr 2
    · apply Subtype.ext
      simp only [RelativeGroupLaw.baseChangePointToBase_coe, Category.assoc, hr_fst, IsPullback.isoPullback_hom_fst]
    · apply Subtype.ext
      simp only [RelativeGroupLaw.baseChangePointToBase_coe, Category.assoc, hr_fst, IsPullback.isoPullback_hom_fst]
  · rw [RelativeGroupLaw.baseChange_mul, RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_snd, Category.assoc, hg_snd,
      ← Category.assoc, (G.mul t' x y).2]

end Compare

theorem bundle_baseChange {R : Type u} [CommRing R] {R' : Type u} [CommRing R'] {A : Scheme.{u}}
    (f : A ⟶ Spec (CommRingCat.of R)) (G : RelativeGroupLaw R f) (hb : AbelianSchemePropertyBundle R f)
    [GeometricallyConnected f] (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)) :
    AbelianSchemePropertyBundle R' (pullback.snd f ι) ∧ GeometricallyConnected (pullback.snd f ι) := by
  haveI : IsProper f := hb.proper
  haveI : Smooth f := hb.smooth
  exact ⟨⟨inferInstance, inferInstance, fun x => (pullback.snd f ι).isConnected_preimage_singleton x, ⟨G.baseChange ι⟩⟩,
    inferInstance⟩

theorem fg_restrictScalars {L : Type u} [CommRing L] (R₁ : Subalgebra ℤ L) (T : Subalgebra ↥R₁ L)
    (h₁ : R₁.FG) (h₂ : T.FG) : (T.restrictScalars ℤ).FG := by
  have i1 : Algebra.FiniteType ℤ ↥R₁ := (Subalgebra.fg_iff_finiteType _).1 h₁
  have i2 : Algebra.FiniteType ↥R₁ ↥T := (Subalgebra.fg_iff_finiteType _).1 h₂
  have i3 : Algebra.FiniteType ℤ ↥T := Algebra.FiniteType.trans i1 i2
  exact (Subalgebra.fg_iff_finiteType (T.restrictScalars ℤ)).2 i3

end NoethKit19

open scoped TensorProduct Quaternion NumberField
open QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NoethKit19

theorem solution
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N : ℕ)
    (L : Type) [CommRing L] (E : FakeEllipticCurve Λ N L) (s : Finset L)
    {ι : Type} [Finite ι] (φ : ι → (E.A ⟶ E.A)) (hφ : ∀ i, φ i ≫ E.f = E.f) :
    ∃ (R : Subalgebra ℤ L) (_ : R.FG) (_ : (↑s : Set L) ⊆ R)
      (A₀ : Scheme.{0}) (f₀ : A₀ ⟶ Spec (CommRingCat.of ↥R)) (L₀ : RelativeGroupLaw ↥R f₀) (_ : L₀.IsCommutative)
      (_ : AbelianSchemePropertyBundle ↥R f₀)
      (_ : GeometricallyConnected f₀)
      (φ₀ : ι → (A₀ ⟶ A₀)) (_ : ∀ i, φ₀ i ≫ f₀ = f₀)
      (g : E.A ⟶ A₀) (hg : CategoryTheory.IsPullback g E.f f₀ (Spec.map (CommRingCat.ofHom R.val.toRingHom))),
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of L)) (P Q : SchemeHomOver t' E.f),
        (E.L.mul t' P Q).1 ≫ g =
          (L₀.mul (t' ≫ Spec.map (CommRingCat.ofHom R.val.toRingHom))
            ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1) ∧
      (∀ i, φ i ≫ g = g ≫ φ₀ i) := by
  classical

  obtain ⟨R₁, hR₁fg, hsR₁, A₁, f₁, L₁, π, hπ, hb₁, hgc₁, hcomm₁, hmul₁⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_fg_subalgebra_abelianSchemePropertyBundle_isPullback_of_isNoetherianRing
      (A₀ := ℤ) E.L E.bundle s
  haveI : IsProper f₁ := hb₁.proper
  haveI : Smooth f₁ := hb₁.smooth
  haveI : GeometricallyConnected f₁ := hgc₁

  have he_snd : hπ.isoPullback.hom ≫ pullback.snd f₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥R₁ L))) = E.f := hπ.isoPullback_hom_snd
  have he_inv_snd : hπ.isoPullback.inv ≫ E.f = pullback.snd f₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥R₁ L))) := by
    rw [Iso.inv_comp_eq]; exact he_snd.symm
  have hgA : ∀ i, (hπ.isoPullback.inv ≫ φ i ≫ hπ.isoPullback.hom) ≫ pullback.snd f₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥R₁ L))) = pullback.snd f₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥R₁ L))) := by
    intro i; simp only [Category.assoc, he_snd, hφ i, he_inv_snd]

  obtain ⟨T, hTfg, -, g₀, hg₀, hcompat⟩ :=
    AlgebraicGeometry.exists_fg_subalgebra_forall_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation
      (A₀ := ↥R₁) (A := L) (fun _ : ι => f₁) (fun _ : ι => f₁) (fun i => hπ.isoPullback.inv ≫ φ i ≫ hπ.isoPullback.hom) hgA ∅

  obtain ⟨r, hr_fst, hr_snd⟩ := exists_transition T f₁
  have hg := isPullback_comp_transition T f₁ π hπ r hr_fst hr_snd
  obtain ⟨hb₀, hgc₀⟩ := bundle_baseChange f₁ L₁ hb₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥R₁ ↥T)))
  refine ⟨T.restrictScalars ℤ, fg_restrictScalars R₁ T hR₁fg hTfg, fun x hx => T.algebraMap_mem ⟨x, hsR₁ hx⟩,
    pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥R₁ ↥T))), pullback.snd f₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥R₁ ↥T))), L₁.baseChange (Spec.map (CommRingCat.ofHom (algebraMap ↥R₁ ↥T))),
    RelativeGroupLaw.IsCommutative.baseChange (Spec.map (CommRingCat.ofHom (algebraMap ↥R₁ ↥T))) (hcomm₁ E.comm), hb₀, hgc₀, g₀, hg₀,
    hπ.isoPullback.hom ≫ r, hg, fun t' P Q => mul_comp_transition T f₁ π hπ L₁ E.L hmul₁ r hr_fst hr_snd t' P Q, ?_⟩

  intro i
  rw [Category.assoc, hcompat i r r hr_fst hr_snd hr_fst hr_snd]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_abelianScheme_endomorphisms_isPullback
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_abelianScheme_endomorphisms_isPullback (solution)
