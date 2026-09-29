-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_isFinite_proj_forall_isPullback_of_tower_of_isFinite_proj
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/51ad1db5-92ef-5039-ba33-04beb60887a4

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Theorems.Thm_AlgebraicGeometry_exists_isFinite_of_forall_isFinite_isPullback_of_isClosedImmersion_proj_of_isAdicComplete
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isFinite_proj_forall_isPullback_of_tower_of_isFinite_proj
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.OModulePresheaf.familyFramesGradedModule.moduleBase AlgebraicGeometry.OModulePresheaf.FamilyFrames.module AlgebraicGeometry.OModulePresheaf.FamilyFrames.addCommGroup AlgebraicGeometry.OModulePresheaf.moduleSectionsHomSub AlgebraicGeometry.OModulePresheaf.smulSections AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II"
p2m_attr_erase "instance" "DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec"
p2m_attr_erase "simp" "TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.internalHom.ofAffHom_apply AlgebraicGeometry.OModulePresheaf.internalHom.toAffHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq"

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open scoped TensorProduct Quaternion
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

namespace P2mWs41S0

lemma isPullback_lift_of_fac {X X₁ Y B B' : Scheme.{0}} {p : X ⟶ X₁} {g : X ⟶ Y} {f : X₁ ⟶ B} {ι : Y ⟶ B}
    (sq : IsPullback p g f ι) (κ : B' ⟶ B) (ι' : Y ⟶ B') (hι : ι' ≫ κ = ι)
    (w : p ≫ f = (g ≫ ι') ≫ κ) :
    IsPullback (pullback.lift p (g ≫ ι') w) g (pullback.snd f κ) ι' := by
  refine IsPullback.of_right (h₁₂ := pullback.fst f κ) (v₁₃ := f) (h₂₂ := κ) ?_ (pullback.lift_snd _ _ _)
    (IsPullback.of_hasPullback f κ)
  rw [pullback.lift_fst, hι]
  exact sq

end P2mWs41S0

open P2mWs41S0 in
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
    (r : ℕ) (ι : ∀ n : ℕ, (E n).A ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) R))
    (hι :
      (∀ n, IsFinite (ι n)) ∧
      (∀ n, ι n ≫ ProjSpace.π R r = (E n).f ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1))))) ∧
      (∀ n, t n ≫ ι (n + 1) = ι n)) :
    ∃ (Z : Scheme.{0}) (G : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) R)) (_ : IsFinite G) (jz : ∀ n : ℕ, (E n).A ⟶ Z),
      (∀ n, jz n ≫ G = ι n) ∧
      (∀ n, t n ≫ jz (n + 1) = jz n) ∧
      (∀ n, CategoryTheory.IsPullback (jz n) (E n).f (G ≫ ProjSpace.π R r) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1)))))) := by
  classical
  obtain ⟨hfin, hιπ, hιt⟩ := hι

  let sR : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1))) ⟶ Spec (CommRingCat.of R) :=
    fun n => Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1))))
  have hsR : ∀ n : ℕ, sR n = Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1)))) := fun n => rfl
  let tR : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1))) ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1 + 1))) :=
    fun n => Spec.map (CommRingCat.ofHom (π n))
  have htR : ∀ n : ℕ, tR n ≫ sR (n + 1) = sR n := by
    intro n
    simp only [tR, sR]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hπ n]

  have wx : ∀ n : ℕ, pullback.fst (ProjSpace.π R r) (sR n) ≫ ProjSpace.π R r = (pullback.snd (ProjSpace.π R r) (sR n) ≫ tR n) ≫ sR (n + 1) := by
    intro n; rw [Category.assoc, htR]; exact pullback.condition
  let xn : ∀ n : ℕ, pullback (ProjSpace.π R r) (sR n) ⟶ pullback (ProjSpace.π R r) (sR (n + 1)) :=
    fun n => pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ tR n) (wx n)
  have hxn₁ : ∀ n, xn n ≫ pullback.fst _ _ = pullback.fst _ _ := fun n => pullback.lift_fst _ _ _
  have hxn₂ : ∀ n, xn n ≫ pullback.snd _ _ = pullback.snd _ _ ≫ tR n := fun n => pullback.lift_snd _ _ _
  have hxsq : ∀ n, IsPullback (xn n) (pullback.snd (ProjSpace.π R r) (sR n)) (pullback.snd (ProjSpace.π R r) (sR (n + 1))) (tR n) :=
    fun n => isPullback_lift_of_fac (IsPullback.of_hasPullback _ _) (sR (n + 1)) (tR n) (htR n) (wx n)

  let g : ∀ n : ℕ, (E n).A ⟶ pullback (ProjSpace.π R r) (sR n) := fun n => pullback.lift (ι n) (E n).f (hιπ n)
  have hg₁ : ∀ n, g n ≫ pullback.fst _ _ = ι n := fun n => pullback.lift_fst _ _ _
  have hg₂ : ∀ n, g n ≫ pullback.snd _ _ = (E n).f := fun n => pullback.lift_snd _ _ _
  haveI : ∀ n, IsFinite (g n) := by
    intro n
    haveI : IsFinite (g n ≫ pullback.fst (ProjSpace.π R r) (sR n)) := by rw [hg₁]; exact hfin n
    exact IsFinite.of_comp (g n) (pullback.fst (ProjSpace.π R r) (sR n))
  have hY : ∀ n, IsPullback (t n) (g n) (g (n + 1)) (xn n) := by
    intro n
    have big : IsPullback (t n) (g n ≫ pullback.snd _ _) (g (n + 1) ≫ pullback.snd _ _) (tR n) := by
      rw [hg₂, hg₂]; exact (ht n).1
    refine IsPullback.of_bot big ?_ (hxsq n)
    apply pullback.hom_ext
    · rw [Category.assoc, hg₁, hιt, Category.assoc, hxn₁, hg₁]
    · rw [Category.assoc, hg₂, Category.assoc, hxn₂, ← Category.assoc, hg₂]
      exact (ht n).1.w

  obtain ⟨Yf, G, hG, e, he, hcomp⟩ :=
    AlgebraicGeometry.exists_isFinite_of_forall_isFinite_isPullback_of_isClosedImmersion_proj_of_isAdicComplete
      R (IsLocalRing.maximalIdeal R) (Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) R)) (ProjSpace.π R r)
      r (𝟙 _) (Category.id_comp _) sR hsR tR htR xn hxn₁ hxn₂ (fun n => (E n).A) g t hY
  refine ⟨Yf, G, hG, fun n => (e n).inv ≫ pullback.fst G (pullback.fst (ProjSpace.π R r) (sR n)), ?_, ?_, ?_⟩
  · intro n
    rw [Category.assoc, pullback.condition, ← he n, Category.assoc, Iso.inv_hom_id_assoc, hg₁]
  · intro n
    have h1 : t n ≫ (e (n + 1)).inv =
        (e n).inv ≫ pullback.map G (pullback.fst (ProjSpace.π R r) (sR n)) G (pullback.fst (ProjSpace.π R r) (sR (n + 1))) (𝟙 Yf) (xn n) (𝟙 _)
          (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hxn₁]) := by
      rw [Iso.comp_inv_eq, Category.assoc, hcomp n, Iso.inv_hom_id_assoc]
    rw [← Category.assoc, h1, Category.assoc, pullback.map, pullback.lift_fst, Category.comp_id]
  · intro n
    have hsnd : (e n).inv ≫ (pullback.snd G (pullback.fst (ProjSpace.π R r) (sR n)) ≫ pullback.snd (ProjSpace.π R r) (sR n)) = (E n).f := by
      rw [← he n, Category.assoc, Iso.inv_hom_id_assoc, hg₂]
    have sq1 : IsPullback (pullback.fst G (pullback.fst (ProjSpace.π R r) (sR n)))
        (pullback.snd G (pullback.fst (ProjSpace.π R r) (sR n)) ≫ pullback.snd (ProjSpace.π R r) (sR n))
        (G ≫ ProjSpace.π R r) (sR n) :=
      ((IsPullback.of_hasPullback G (pullback.fst (ProjSpace.π R r) (sR n))).flip.paste_horiz
        (IsPullback.of_hasPullback (ProjSpace.π R r) (sR n)).flip).flip
    have sq0 : IsPullback (e n).inv (E n).f
        (pullback.snd G (pullback.fst (ProjSpace.π R r) (sR n)) ≫ pullback.snd (ProjSpace.π R r) (sR n)) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by rw [hsnd, Category.comp_id]⟩
    have := sq0.paste_horiz sq1
    rwa [Category.id_comp] at this

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isFinite_proj_forall_isPullback_of_tower_of_isFinite_proj
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isFinite_proj_forall_isPullback_of_tower_of_isFinite_proj (solution)
