-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_fg_subalgebra_extension_isInvertible_nonempty_pullback_iso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/6b9f3bb2-e478-59b1-90fa-ec7c34906517

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_Mathlib_Algebra_IsDirectLimit
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullback_levelIff
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_forall_nonempty_pullback_iso_of_isDirectLimit_of_comp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_extension_isInvertible_nonempty_pullback_iso
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModulePreGlue AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies SheafOfModules.isIso_ihomModelToIhom PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module"
p2m_attr_erase "instance" "CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.glueComponent_glueMk AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.injEq AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.sizeOf_spec AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec"
p2m_attr_erase "simp" "CoherentBaseChange.TwoTermComplex.mk.injEq"

set_option autoImplicit false

open scoped TensorProduct Quaternion
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

namespace T3FGStages

variable {A₀ : Type} [CommRing A₀] {A : Type} [CommRing A] [Algebra A₀ A] (B : Subalgebra A₀ A)

abbrev Idx : Type := {T : Subalgebra A₀ A // T.FG ∧ B ≤ T}

abbrev G (i : Idx B) : Type := ↥i.1

def φ (i j : Idx B) (h : i ≤ j) : G B i →+* G B j := (Subalgebra.inclusion (show i.1 ≤ j.1 from h)).toRingHom

def g (i : Idx B) : G B i →+* A := (i.1).val.toRingHom

@[scoped simp] theorem φ_apply (i j : Idx B) (h : i ≤ j) (x : G B i) : (φ B i j h x : A) = (x : A) := rfl
@[scoped simp] theorem g_apply (i : Idx B) (x : G B i) : g B i x = (x : A) := rfl

scoped instance : DirectedSystem (G B) (fun i j h => ⇑(φ B i j h)) where
  map_self _ _ := rfl
  map_map _ _ _ _ _ _ := rfl

private def _root_.T3FGStages.sup (i j : Idx B) : Idx B := ⟨i.1 ⊔ j.1, i.2.1.sup j.2.1, le_sup_of_le_left i.2.2⟩

p2m_export "T3FGStages" "sup"
scoped instance : IsDirected (Idx B) (· ≤ ·) :=
  ⟨fun i j => ⟨sup B i j, (le_sup_left : i.1 ≤ i.1 ⊔ j.1), (le_sup_right : j.1 ≤ i.1 ⊔ j.1)⟩⟩

theorem nonempty (hB : B.FG) : Nonempty (Idx B) := ⟨⟨B, hB, le_rfl⟩⟩

theorem isDirectLimit (hB : B.FG) : IsDirectLimit (fun i j h => ⇑(φ B i j h)) (fun i => ⇑(g B i)) where
  surj m := by
    refine ⟨⟨B ⊔ Algebra.adjoin A₀ {m}, hB.sup ⟨{m}, by rw [Finset.coe_singleton]⟩, le_sup_left⟩, ⟨m, ?_⟩, rfl⟩
    exact Algebra.mem_sup_right (Algebra.self_mem_adjoin_singleton A₀ m)
  inj i j mi mj h := ⟨sup B i j, (le_sup_left : i.1 ≤ i.1 ⊔ j.1), (le_sup_right : j.1 ≤ i.1 ⊔ j.1), Subtype.ext h⟩
  compatibility _ _ _ _ := rfl

end T3FGStages
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_extension_isInvertible_nonempty_pullback_iso.T3FGStages"

namespace T3DM1

theorem mul_val_congr {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) {T : Scheme.{0}} {t t' : T ⟶ Spec (CommRingCat.of S)} (h : t = t')
    (P Q : SchemeHomOver t f) (P' Q' : SchemeHomOver t' f) (hP : P.1 = P'.1) (hQ : Q.1 = Q'.1) :
    (L.mul t P Q).1 = (L.mul t' P' Q').1 := by
  subst h
  obtain ⟨P, hP0⟩ := P; obtain ⟨Q, hQ0⟩ := Q; obtain ⟨P', hP1⟩ := P'; obtain ⟨Q', hQ1⟩ := Q'
  simp only at hP hQ
  subst hP; subst hQ
  rfl

noncomputable def pullbackHomInvObj {X Y : Scheme.{0}} (e : X ≅ Y) (M : X.Modules) :
    (Scheme.Modules.pullback e.hom).obj ((Scheme.Modules.pullback e.inv).obj M) ≅ M :=
  (Scheme.Modules.pullbackComp e.hom e.inv).app M ≪≫ (Scheme.Modules.pullbackCongr e.hom_inv_id).app M ≪≫
    (Scheme.Modules.pullbackId X).app M

end T3DM1
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_extension_isInvertible_nonempty_pullback_iso.T3FGStages"

open T3DM1 T3FGStages in
theorem solution
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (N : ℕ) (R : Type) [CommRing R] (E : FakeEllipticCurve Λ N R)
    (T₀ : Subalgebra ℤ R) (hT₀ : T₀.FG) (E₀ : FakeEllipticCurve Λ N ↥T₀) (g₀ : E.A ⟶ E₀.A)
    (hg₀ : CategoryTheory.IsPullback g₀ E.f E₀.f (Spec.map (CommRingCat.ofHom T₀.val.toRingHom)))
    (hlaw₀ :
      (∀ {X : Scheme.{0}} (t' : X ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t' E.f),
        (E.L.mul t' P Q).1 ≫ g₀ =
          (E₀.L.mul (t' ≫ Spec.map (CommRingCat.ofHom T₀.val.toRingHom))
            ⟨P.1 ≫ g₀, by rw [Category.assoc, hg₀.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ g₀, by rw [Category.assoc, hg₀.w, ← Category.assoc, Q.2]⟩).1))
    (hact₀ : ∀ x : ↥Λ, E.act x ≫ g₀ = g₀ ≫ E₀.act x)
    (𝓜 : E.A.Modules) (h𝓜 : Scheme.Modules.IsInvertible 𝓜) :
    ∃ (T : Subalgebra ℤ R) (_ : T.FG) (hle : T₀ ≤ T) (ET : FakeEllipticCurve Λ N ↥T) (g : E.A ⟶ ET.A)
      (hg : CategoryTheory.IsPullback g E.f ET.f (Spec.map (CommRingCat.ofHom T.val.toRingHom)))
      (h : ET.A ⟶ E₀.A)
      (hh : CategoryTheory.IsPullback h ET.f E₀.f (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hle).toRingHom))),
      g ≫ h = g₀ ∧
      (∀ {X : Scheme.{0}} (t' : X ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t' E.f),
        (E.L.mul t' P Q).1 ≫ g =
          (ET.L.mul (t' ≫ Spec.map (CommRingCat.ofHom T.val.toRingHom))
            ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1) ∧
      (∀ x : ↥Λ, E.act x ≫ g = g ≫ ET.act x) ∧
      (∀ {X : Scheme.{0}} (t' : X ⟶ Spec (CommRingCat.of ↥T)) (P Q : SchemeHomOver t' ET.f),
        (ET.L.mul t' P Q).1 ≫ h =
          (E₀.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hle).toRingHom))
            ⟨P.1 ≫ h, by rw [Category.assoc, hh.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ h, by rw [Category.assoc, hh.w, ← Category.assoc, Q.2]⟩).1) ∧
      (∀ x : ↥Λ, ET.act x ≫ h = h ≫ E₀.act x) ∧
      ∃ 𝓜T : ET.A.Modules, Scheme.Modules.IsInvertible 𝓜T ∧ Nonempty ((Scheme.Modules.pullback g).obj 𝓜T ≅ 𝓜) := by
  classical

  haveI : Nonempty (Idx T₀) := T3FGStages.nonempty T₀ hT₀
  have hlim := T3FGStages.isDirectLimit T₀ hT₀

  haveI : IsProper E₀.f := E₀.bundle.proper

  let eA : E.A ≅ pullback E₀.f (Spec.map (CommRingCat.ofHom T₀.val.toRingHom)) := hg₀.isoPullback
  have heA1 : eA.inv ≫ g₀ = pullback.fst _ _ := hg₀.isoPullback_inv_fst
  have heA2 : eA.inv ≫ E.f = pullback.snd _ _ := hg₀.isoPullback_inv_snd

  obtain ⟨j, 𝓜j, h𝓜j, hiso⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_isInvertible_forall_nonempty_pullback_iso_of_isDirectLimit_of_comp_eq
      E₀.f (T3FGStages.φ T₀) (T3FGStages.g T₀) hlim (fun i => (Subalgebra.inclusion i.2.2).toRingHom) (fun i j h => rfl)
      T₀.val.toRingHom (fun i => rfl) ((Scheme.Modules.pullback eA.inv).obj 𝓜) (h𝓜.pullback _)

  have hbase : Spec.map (CommRingCat.ofHom T₀.val.toRingHom) =
      Spec.map (CommRingCat.ofHom (j.1).val.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (Subalgebra.inclusion j.2.2).toRingHom) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; rfl
  obtain ⟨ET, h, hh, hlawh, hacth, -, -⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_levelIff (Subalgebra.inclusion j.2.2).toRingHom E₀
  let g : E.A ⟶ ET.A := hh.lift g₀ (E.f ≫ Spec.map (CommRingCat.ofHom (j.1).val.toRingHom)) (by rw [hg₀.w, hbase, Category.assoc])
  have hg1 : g ≫ h = g₀ := hh.lift_fst _ _ _
  have hg2 : g ≫ ET.f = E.f ≫ Spec.map (CommRingCat.ofHom (j.1).val.toRingHom) := hh.lift_snd _ _ _
  have hg : IsPullback g E.f ET.f (Spec.map (CommRingCat.ofHom (j.1).val.toRingHom)) := by
    have big : IsPullback (g ≫ h) E.f E₀.f
        (Spec.map (CommRingCat.ofHom (j.1).val.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (Subalgebra.inclusion j.2.2).toRingHom)) := by
      rw [hg1, ← hbase]; exact hg₀
    exact IsPullback.of_right big hg2 hh

  let eT : ET.A ≅ pullback E₀.f (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion j.2.2).toRingHom)) := hh.isoPullback
  have heT1 : eT.hom ≫ pullback.fst _ _ = h := hh.isoPullback_hom_fst
  have heT2 : eT.hom ≫ pullback.snd _ _ = ET.f := hh.isoPullback_hom_snd
  let 𝓜T : ET.A.Modules := (Scheme.Modules.pullback eT.hom).obj 𝓜j

  let ρ := eA.inv ≫ g ≫ eT.hom
  have hρ1 : ρ ≫ pullback.fst _ _ = pullback.fst _ _ := by
    simp only [ρ, Category.assoc, heT1, hg1, heA1]
  have hρ2 : ρ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (T3FGStages.g T₀ j)) := by
    simp only [ρ, Category.assoc, heT2, hg2]
    rw [← Category.assoc, heA2]
    rfl
  obtain ⟨eM⟩ := hiso ρ hρ1 hρ2

  have eM' : (Scheme.Modules.pullback eA.inv).obj ((Scheme.Modules.pullback g).obj 𝓜T) ≅
      (Scheme.Modules.pullback eA.inv).obj 𝓜 :=
    (Scheme.Modules.pullback eA.inv).mapIso ((Scheme.Modules.pullbackComp g eT.hom).app 𝓜j) ≪≫
      (Scheme.Modules.pullbackComp eA.inv (g ≫ eT.hom)).app 𝓜j ≪≫ eM
  have eFinal : (Scheme.Modules.pullback g).obj 𝓜T ≅ 𝓜 :=
    (pullbackHomInvObj eA _).symm ≪≫ (Scheme.Modules.pullback eA.hom).mapIso eM' ≪≫ pullbackHomInvObj eA 𝓜
  refine ⟨j.1, j.2.1, j.2.2, ET, g, hg, h, hh, hg1, ?_, ?_, hlawh, hacth, 𝓜T, h𝓜j.pullback _, ⟨eFinal⟩⟩
  · intro X t' P Q
    apply hh.hom_ext
    · rw [Category.assoc, hg1, hlaw₀ t' P Q, hlawh]
      refine mul_val_congr E₀.L ?_ _ _ _ _ ?_ ?_
      · rw [Category.assoc, ← hbase]
      · simp only [Category.assoc, hg1]
      · simp only [Category.assoc, hg1]
    · conv_lhs => rw [Category.assoc, hg2, ← Category.assoc, (E.L.mul t' P Q).2]
      exact ((ET.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (j.1).val.toRingHom)) _ _).2).symm
  · intro x
    apply hh.hom_ext
    · rw [Category.assoc, hg1, hact₀, Category.assoc, hacth, ← Category.assoc, hg1]
    · rw [Category.assoc, hg2, ← Category.assoc, E.act_over, Category.assoc, ET.act_over, hg2]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_extension_isInvertible_nonempty_pullback_iso
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_extension_isInvertible_nonempty_pullback_iso (solution)
