-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_not_mem_stage_kernelIsTwoTorsion_isSymmetric_rosatiCompatible_of_isCanonicalPolData_atPrime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/5e42fb55-e237-5c26-9e44-7008caea125e

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_nonempty_iso_pullback_of_isInvertible_atPrime_of_isSeparated
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_nonempty_iso_pullback_away_of_nonempty_iso_pullback_atPrime
import Theorems.Thm_CerednikDrinfeld_QM_IsCanonicalPolData_of_iso
import Theorems.Thm_AlgebraicGeometry_Polarisation_locIsoOnBase_iff_nonempty_iso_of_isLocalRing
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_comp_negMor_eq_negMor_comp_of_compatible
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_fst_eq
import Theorems.Thm_AlgebraicGeometry_Polarisation_KernelIsTwoTorsion_pullback_of_isPullback_of_isInvertible
import Theorems.Thm_AlgebraicGeometry_Polarisation_RosatiCompatible_pullback_of_isPullback
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_not_mem_stage_kernelIsTwoTorsion_isSymmetric_rosatiCompatible_of_isCanonicalPolData_atPrime
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModulePreGlue AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies SheafOfModules.isIso_ihomModelToIhom TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.glueComponent_glueMk AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.injEq AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.sizeOf_spec AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec"
p2m_attr_erase "simp" "CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open scoped TensorProduct Quaternion
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

noncomputable section

namespace DatumAtStage

section ModIso
variable {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)

theorem nonempty_dual_iso {X : Scheme.{0}} {M M' : X.Modules} (hM : Scheme.Modules.IsInvertible M)
    (hM' : Scheme.Modules.IsInvertible M') (e : M ≅ M') :
    Nonempty (Scheme.Modules.dual M ≅ Scheme.Modules.dual M') := by
  obtain ⟨u⟩ := hM.dual_monoidalV2.2
  obtain ⟨u'⟩ := hM'.dual_monoidalV2.2

  exact ⟨(ρ_ _).symm ≪≫ whiskerLeftIso _ u'.symm ≪≫ (α_ _ _ _).symm ≪≫
    whiskerRightIso (whiskerLeftIso _ e.symm ≪≫ β_ _ _ ≪≫ u) _ ≪≫ λ_ _⟩

theorem nonempty_mumfordBundle_iso {𝓛 𝓛' : A.Modules} (h : Scheme.Modules.IsInvertible 𝓛)
    (h' : Scheme.Modules.IsInvertible 𝓛') (e : 𝓛 ≅ 𝓛') :
    Nonempty (mumfordBundle f L 𝓛 ≅ mumfordBundle f L 𝓛') := by
  obtain ⟨d⟩ := nonempty_dual_iso h h' e
  exact ⟨tensorIso ((Scheme.Modules.pullback _).mapIso e)
    (tensorIso ((Scheme.Modules.pullback _).mapIso d) ((Scheme.Modules.pullback _).mapIso d))⟩

theorem locIsoOnBase_congr {S' : Type} [CommRing S'] {X : Scheme.{0}} (g : X ⟶ Spec (CommRingCat.of S'))
    {M M' N N' : X.Modules} (eM : M ≅ N) (eM' : M' ≅ N') (h : LocIsoOnBase g M M') : LocIsoOnBase g N N' := by
  intro s
  obtain ⟨U, hs, ⟨i⟩⟩ := h s
  exact ⟨U, hs, ⟨((Scheme.Modules.pullback _).mapIso eM).symm ≪≫ i ≪≫ (Scheme.Modules.pullback _).mapIso eM'⟩⟩

theorem locIsoOnBase_of_iso {S' : Type} [CommRing S'] {X : Scheme.{0}} (g : X ⟶ Spec (CommRingCat.of S'))
    {M M' : X.Modules} (e : M ≅ M') : LocIsoOnBase g M M' :=
  fun s => ⟨⊤, trivial, ⟨(Scheme.Modules.pullback _).mapIso e⟩⟩

theorem kernelIsTwoTorsion_of_iso {𝓛 𝓛' : A.Modules} (h : Scheme.Modules.IsInvertible 𝓛)
    (h' : Scheme.Modules.IsInvertible 𝓛') (e : 𝓛 ≅ 𝓛') (hK : KernelIsTwoTorsion f L 𝓛) :
    KernelIsTwoTorsion f L 𝓛' := by
  obtain ⟨m⟩ := nonempty_mumfordBundle_iso f L h h' e
  intro R _ t x
  refine Iff.trans ?_ (hK R t x)
  constructor
  · exact fun hl => locIsoOnBase_congr _ ((Scheme.Modules.pullback _).mapIso m).symm (Iso.refl _) hl
  · exact fun hl => locIsoOnBase_congr _ ((Scheme.Modules.pullback _).mapIso m) (Iso.refl _) hl

theorem isSymmetric_of_iso {𝓛 𝓛' : A.Modules} (e : 𝓛 ≅ 𝓛') (h : IsSymmetric f L 𝓛) : IsSymmetric f L 𝓛' :=
  locIsoOnBase_congr _ ((Scheme.Modules.pullback _).mapIso e) e h

theorem rosatiCompatible_of_iso {𝓛 𝓛' : A.Modules} (h : Scheme.Modules.IsInvertible 𝓛)
    (h' : Scheme.Modules.IsInvertible 𝓛') (e : 𝓛 ≅ 𝓛')
    {I : Type} (act : I → (A ⟶ A)) (act_over : ∀ x : I, act x ≫ f = f) (star : I → I)
    (hR : RosatiCompatible f L 𝓛 act act_over star) : RosatiCompatible f L 𝓛' act act_over star := by
  obtain ⟨m⟩ := nonempty_mumfordBundle_iso f L h h' e
  intro b
  exact locIsoOnBase_congr _ ((Scheme.Modules.pullback _).mapIso m) ((Scheme.Modules.pullback _).mapIso m) (hR b)

theorem mul_coe_congr {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of S)} (ht : t₁ = t₂)
    (x₁ y₁ : SchemeHomOver t₁ f) (x₂ y₂ : SchemeHomOver t₂ f) (hx : x₁.1 = x₂.1) (hy : y₁.1 = y₂.1) :
    (L.mul t₁ x₁ y₁).1 = (L.mul t₂ x₂ y₂).1 := by
  subst ht
  obtain rfl : x₁ = x₂ := Subtype.ext hx
  obtain rfl : y₁ = y₂ := Subtype.ext hy
  rfl

end ModIso

section Kap

variable {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (G : RelativeGroupLaw S f)

abbrev bι (S R : Type) [CommRing S] [CommRing R] [Algebra S R] : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S) :=
  Spec.map (CommRingCat.ofHom (algebraMap S R))

theorem spec_comp_bι {R R' : Type} [CommRing R] [CommRing R'] [Algebra S R] [Algebra S R']
    (φ : R →+* R') (hφ : φ.comp (algebraMap S R) = algebraMap S R') :
    Spec.map (CommRingCat.ofHom φ) ≫ bι S R = bι S R' := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ]

abbrev kap {R R' : Type} [CommRing R] [CommRing R'] [Algebra S R] [Algebra S R']
    (φ : R →+* R') (hφ : φ.comp (algebraMap S R) = algebraMap S R') :
    pullback f (bι S R') ⟶ pullback f (bι S R) :=
  pullback.lift (pullback.fst f (bι S R')) (pullback.snd f (bι S R') ≫ Spec.map (CommRingCat.ofHom φ))
    (by rw [pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ])

@[reassoc] theorem kap_fst {R R' : Type} [CommRing R] [CommRing R'] [Algebra S R] [Algebra S R']
    (φ : R →+* R') (hφ : φ.comp (algebraMap S R) = algebraMap S R') :
    kap f φ hφ ≫ pullback.fst f (bι S R) = pullback.fst f (bι S R') := pullback.lift_fst _ _ _

@[reassoc] theorem kap_snd {R R' : Type} [CommRing R] [CommRing R'] [Algebra S R] [Algebra S R']
    (φ : R →+* R') (hφ : φ.comp (algebraMap S R) = algebraMap S R') :
    kap f φ hφ ≫ pullback.snd f (bι S R) = pullback.snd f (bι S R') ≫ Spec.map (CommRingCat.ofHom φ) :=
  pullback.lift_snd _ _ _

theorem isPullback_kap {R R' : Type} [CommRing R] [CommRing R'] [Algebra S R] [Algebra S R']
    (φ : R →+* R') (hφ : φ.comp (algebraMap S R) = algebraMap S R') :
    IsPullback (kap f φ hφ) (pullback.snd f (bι S R')) (pullback.snd f (bι S R)) (Spec.map (CommRingCat.ofHom φ)) := by
  refine IsPullback.of_right (h₁₂ := pullback.fst f (bι S R)) (v₁₃ := f) (h₂₂ := bι S R) ?_ (kap_snd f φ hφ)
    (IsPullback.of_hasPullback f (bι S R))
  rw [kap_fst, spec_comp_bι φ hφ]
  exact IsPullback.of_hasPullback f (bι S R')

theorem kap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] [Algebra S R] [Algebra S R'] [Algebra S R'']
    (φ : R →+* R') (hφ : φ.comp (algebraMap S R) = algebraMap S R')
    (φ' : R' →+* R'') (hφ' : φ'.comp (algebraMap S R') = algebraMap S R'')
    (φ'' : R →+* R'') (hφ'' : φ''.comp (algebraMap S R) = algebraMap S R'') (hc : φ'.comp φ = φ'') :
    kap f φ' hφ' ≫ kap f φ hφ = kap f φ'' hφ'' := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst]
  · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hc]

theorem hmul_kap {R R' : Type} [CommRing R] [CommRing R'] [Algebra S R] [Algebra S R']
    (φ : R →+* R') (hφ : φ.comp (algebraMap S R) = algebraMap S R')
    (LR : RelativeGroupLaw R (pullback.snd f (bι S R))) (LR' : RelativeGroupLaw R' (pullback.snd f (bι S R')))
    (hR : ∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t' (pullback.snd f (bι S R))),
      (LR.mul t' P Q).1 ≫ pullback.fst f (bι S R) =
        (G.mul (t' ≫ bι S R) ⟨P.1 ≫ pullback.fst f (bι S R), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ pullback.fst f (bι S R), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1)
    (hR' : ∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of R')) (P Q : SchemeHomOver t' (pullback.snd f (bι S R'))),
      (LR'.mul t' P Q).1 ≫ pullback.fst f (bι S R') =
        (G.mul (t' ≫ bι S R') ⟨P.1 ≫ pullback.fst f (bι S R'), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ pullback.fst f (bι S R'), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1)
    {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of R')) (P Q : SchemeHomOver t' (pullback.snd f (bι S R'))) :
    (LR'.mul t' P Q).1 ≫ kap f φ hφ =
      (LR.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
        ⟨P.1 ≫ kap f φ hφ, by rw [Category.assoc, (isPullback_kap f φ hφ).w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ kap f φ hφ, by rw [Category.assoc, (isPullback_kap f φ hφ).w, ← Category.assoc, Q.2]⟩).1 := by
  apply pullback.hom_ext
  · rw [Category.assoc, kap_fst, hR', hR]
    exact mul_coe_congr f G (by rw [Category.assoc, spec_comp_bι φ hφ]) _ _ _ _
      (by simp only [Category.assoc, pullback.lift_fst]) (by simp only [Category.assoc, pullback.lift_fst])
  · have h1 : ((LR'.mul t' P Q).1 ≫ kap f φ hφ) ≫ pullback.snd f (bι S R) = t' ≫ Spec.map (CommRingCat.ofHom φ) := by
      rw [Category.assoc, kap_snd, ← Category.assoc, (LR'.mul t' P Q).2]
    exact h1.trans ((LR.mul (t' ≫ Spec.map (CommRingCat.ofHom φ)) _ _).2).symm

abbrev actLift {I : Type} (act : I → (A ⟶ A)) (act_over : ∀ x : I, act x ≫ f = f)
    (R : Type) [CommRing R] [Algebra S R] (x : I) : pullback f (bι S R) ⟶ pullback f (bι S R) :=
  pullback.lift (pullback.fst f (bι S R) ≫ act x) (pullback.snd f (bι S R))
    (by rw [Category.assoc, act_over]; exact pullback.condition)

@[reassoc] theorem actLift_fst {I : Type} (act : I → (A ⟶ A)) (act_over : ∀ x : I, act x ≫ f = f)
    (R : Type) [CommRing R] [Algebra S R] (x : I) :
    actLift f act act_over R x ≫ pullback.fst f (bι S R) = pullback.fst f (bι S R) ≫ act x := pullback.lift_fst _ _ _

@[reassoc] theorem actLift_snd {I : Type} (act : I → (A ⟶ A)) (act_over : ∀ x : I, act x ≫ f = f)
    (R : Type) [CommRing R] [Algebra S R] (x : I) :
    actLift f act act_over R x ≫ pullback.snd f (bι S R) = pullback.snd f (bι S R) := pullback.lift_snd _ _ _

theorem actLift_kap {I : Type} (act : I → (A ⟶ A)) (act_over : ∀ x : I, act x ≫ f = f)
    {R R' : Type} [CommRing R] [CommRing R'] [Algebra S R] [Algebra S R']
    (φ : R →+* R') (hφ : φ.comp (algebraMap S R) = algebraMap S R') (x : I) :
    actLift f act act_over R' x ≫ kap f φ hφ = kap f φ hφ ≫ actLift f act act_over R x := by
  apply pullback.hom_ext
  · simp only [Category.assoc, kap_fst, kap_fst_assoc, actLift_fst, actLift_fst_assoc]
  · simp only [Category.assoc, kap_snd, kap_snd_assoc, actLift_snd, actLift_snd_assoc]

theorem baseChange_compat (R : Type) [CommRing R] [Algebra S R]
    (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t' (pullback.snd f (bι S R))) :
    ((G.baseChange (bι S R)).mul t' P Q).1 ≫ pullback.fst f (bι S R) =
      (G.mul (t' ≫ bι S R) ⟨P.1 ≫ pullback.fst f (bι S R), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ pullback.fst f (bι S R), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1 :=
  congrArg Subtype.val (RelativeGroupLaw.baseChangePointToBase_mul (bι S R) G t' P Q)

end Kap

section Kap2

variable {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (G : RelativeGroupLaw S f)
  {R R'' P : Type} [CommRing R] [CommRing R''] [CommRing P] [Algebra S R] [Algebra R R''] [Algebra S P]
  (φ : P →+* R'') (hφ : φ.comp (algebraMap S P) = (algebraMap R R'').comp (algebraMap S R))

include hφ

theorem spec_comp_bι₂ : Spec.map (CommRingCat.ofHom (algebraMap R R'')) ≫ bι S R = Spec.map (CommRingCat.ofHom φ) ≫ bι S P := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hφ]

abbrev kap₂ : pullback (pullback.snd f (bι S R)) (Spec.map (CommRingCat.ofHom (algebraMap R R''))) ⟶ pullback f (bι S P) :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst f (bι S R)) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom φ))
    (by rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc, spec_comp_bι₂ φ hφ,
      Category.assoc])

@[reassoc] theorem kap₂_fst : kap₂ f φ hφ ≫ pullback.fst f (bι S P) = pullback.fst _ _ ≫ pullback.fst f (bι S R) :=
  pullback.lift_fst _ _ _

@[reassoc] theorem kap₂_snd : kap₂ f φ hφ ≫ pullback.snd f (bι S P) = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom φ) :=
  pullback.lift_snd _ _ _

theorem isPullback_kap₂ :
    IsPullback (kap₂ f φ hφ) (pullback.snd _ _) (pullback.snd f (bι S P)) (Spec.map (CommRingCat.ofHom φ)) := by
  refine IsPullback.of_right (h₁₂ := pullback.fst f (bι S P)) (v₁₃ := f) (h₂₂ := bι S P) ?_ (pullback.lift_snd _ _ _)
    (IsPullback.of_hasPullback f (bι S P))
  rw [show kap₂ f φ hφ ≫ pullback.fst f (bι S P) = pullback.fst _ _ ≫ pullback.fst f (bι S R) from pullback.lift_fst _ _ _,
    ← spec_comp_bι₂ φ hφ]
  exact (IsPullback.of_hasPullback (pullback.snd f (bι S R)) (Spec.map (CommRingCat.ofHom (algebraMap R R'')))).paste_horiz
    (IsPullback.of_hasPullback f (bι S R))

theorem hmul_kap₂
    (LR : RelativeGroupLaw R (pullback.snd f (bι S R)))
    (hR : ∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of R)) (P' Q : SchemeHomOver t' (pullback.snd f (bι S R))),
      (LR.mul t' P' Q).1 ≫ pullback.fst f (bι S R) =
        (G.mul (t' ≫ bι S R) ⟨P'.1 ≫ pullback.fst f (bι S R), by rw [Category.assoc, pullback.condition, ← Category.assoc, P'.2]⟩
          ⟨Q.1 ≫ pullback.fst f (bι S R), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1)
    (LX : RelativeGroupLaw R'' (pullback.snd (pullback.snd f (bι S R)) (Spec.map (CommRingCat.ofHom (algebraMap R R'')))))
    (hX : ∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of R''))
      (P' Q : SchemeHomOver t' (pullback.snd (pullback.snd f (bι S R)) (Spec.map (CommRingCat.ofHom (algebraMap R R''))))),
      (LX.mul t' P' Q).1 ≫ pullback.fst _ _ =
        (LR.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R'')))
          ⟨P'.1 ≫ pullback.fst _ _, by rw [Category.assoc, pullback.condition, ← Category.assoc, P'.2]⟩
          ⟨Q.1 ≫ pullback.fst _ _, by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1)
    (LP : RelativeGroupLaw P (pullback.snd f (bι S P)))
    (hP : ∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of P)) (P' Q : SchemeHomOver t' (pullback.snd f (bι S P))),
      (LP.mul t' P' Q).1 ≫ pullback.fst f (bι S P) =
        (G.mul (t' ≫ bι S P) ⟨P'.1 ≫ pullback.fst f (bι S P), by rw [Category.assoc, pullback.condition, ← Category.assoc, P'.2]⟩
          ⟨Q.1 ≫ pullback.fst f (bι S P), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1)
    {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of R''))
    (P' Q : SchemeHomOver t' (pullback.snd (pullback.snd f (bι S R)) (Spec.map (CommRingCat.ofHom (algebraMap R R''))))) :
    (LX.mul t' P' Q).1 ≫ kap₂ f φ hφ =
      (LP.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
        ⟨P'.1 ≫ kap₂ f φ hφ, by rw [Category.assoc, (isPullback_kap₂ f φ hφ).w, ← Category.assoc, P'.2]⟩
        ⟨Q.1 ≫ kap₂ f φ hφ, by rw [Category.assoc, (isPullback_kap₂ f φ hφ).w, ← Category.assoc, Q.2]⟩).1 := by
  apply pullback.hom_ext
  · rw [Category.assoc, kap₂_fst, ← Category.assoc, hX, hR, hP]
    exact mul_coe_congr f G (by rw [Category.assoc, Category.assoc, spec_comp_bι₂ φ hφ]) _ _ _ _
      (by simp only [Category.assoc, kap₂_fst]) (by simp only [Category.assoc, kap₂_fst])
  · have h1 : ((LX.mul t' P' Q).1 ≫ kap₂ f φ hφ) ≫ pullback.snd f (bι S P) = t' ≫ Spec.map (CommRingCat.ofHom φ) := by
      rw [Category.assoc, kap₂_snd, ← Category.assoc, (LX.mul t' P' Q).2]
    exact h1.trans ((LP.mul (t' ≫ Spec.map (CommRingCat.ofHom φ)) _ _).2).symm

theorem act_kap₂ {I : Type} (act : I → (A ⟶ A)) (act_over : ∀ x : I, act x ≫ f = f)
    (act' : I → (pullback (pullback.snd f (bι S R)) (Spec.map (CommRingCat.ofHom (algebraMap R R''))) ⟶
      pullback (pullback.snd f (bι S R)) (Spec.map (CommRingCat.ofHom (algebraMap R R'')))))
    (act'_over : ∀ x : I, act' x ≫ pullback.snd _ _ = pullback.snd _ _)
    (hact' : ∀ x : I, act' x ≫ pullback.fst _ _ = pullback.fst _ _ ≫ actLift f act act_over R x) (x : I) :
    act' x ≫ kap₂ f φ hφ = kap₂ f φ hφ ≫ actLift f act act_over P x := by
  apply pullback.hom_ext
  · rw [Category.assoc, kap₂_fst, ← Category.assoc, hact', Category.assoc, actLift_fst, Category.assoc, actLift_fst,
      kap₂_fst_assoc]
  · rw [Category.assoc, kap₂_snd, ← Category.assoc, act'_over, Category.assoc, actLift_snd, kap₂_snd]

end Kap2

section Kap3

variable {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (G : RelativeGroupLaw S f)
  {R RK T : Type} [CommRing R] [CommRing RK] [CommRing T] [Algebra S R] [Algebra R RK] [Algebra S T]
  (θ₀ : R →+* T) (hθ₀ : θ₀.comp (algebraMap S R) = algebraMap S T)
  (θ : RK →+* T) (hθ : θ.comp (algebraMap R RK) = θ₀)

abbrev actLift₂ {I : Type} (act : I → (A ⟶ A)) (act_over : ∀ x : I, act x ≫ f = f) (x : I) :
    pullback (pullback.snd f (bι S R)) (Spec.map (CommRingCat.ofHom (algebraMap R RK))) ⟶
      pullback (pullback.snd f (bι S R)) (Spec.map (CommRingCat.ofHom (algebraMap R RK))) :=
  pullback.lift (pullback.fst _ _ ≫ actLift f act act_over R x) (pullback.snd _ _)
    (by rw [Category.assoc, pullback.lift_snd]; exact pullback.condition)

@[reassoc] theorem actLift₂_fst {I : Type} (act : I → (A ⟶ A)) (act_over : ∀ x : I, act x ≫ f = f) (x : I) :
    actLift₂ f (R := R) (RK := RK) act act_over x ≫ pullback.fst _ _ = pullback.fst _ _ ≫ actLift f act act_over R x :=
  pullback.lift_fst _ _ _

@[reassoc] theorem actLift₂_snd {I : Type} (act : I → (A ⟶ A)) (act_over : ∀ x : I, act x ≫ f = f) (x : I) :
    actLift₂ f (R := R) (RK := RK) act act_over x ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _

include hθ₀ hθ

abbrev kap₃ : pullback f (bι S T) ⟶ pullback (pullback.snd f (bι S R)) (Spec.map (CommRingCat.ofHom (algebraMap R RK))) :=
  pullback.lift (kap f θ₀ hθ₀) (pullback.snd f (bι S T) ≫ Spec.map (CommRingCat.ofHom θ))
    (by rw [kap_snd, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hθ])

@[reassoc] theorem kap₃_fst : kap₃ f θ₀ hθ₀ θ hθ ≫ pullback.fst _ _ = kap f θ₀ hθ₀ := pullback.lift_fst _ _ _

@[reassoc] theorem kap₃_snd : kap₃ f θ₀ hθ₀ θ hθ ≫ pullback.snd _ _ = pullback.snd f (bι S T) ≫ Spec.map (CommRingCat.ofHom θ) :=
  pullback.lift_snd _ _ _

theorem isPullback_kap₃ :
    IsPullback (kap₃ f θ₀ hθ₀ θ hθ) (pullback.snd f (bι S T))
      (pullback.snd (pullback.snd f (bι S R)) (Spec.map (CommRingCat.ofHom (algebraMap R RK)))) (Spec.map (CommRingCat.ofHom θ)) := by
  refine IsPullback.of_right (h₁₂ := pullback.fst _ _) (v₁₃ := pullback.snd f (bι S R))
    (h₂₂ := Spec.map (CommRingCat.ofHom (algebraMap R RK))) ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
  rw [show kap₃ f θ₀ hθ₀ θ hθ ≫ pullback.fst _ _ = kap f θ₀ hθ₀ from pullback.lift_fst _ _ _,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, hθ]
  exact isPullback_kap f θ₀ hθ₀

theorem hmul_kap₃
    (LR : RelativeGroupLaw R (pullback.snd f (bι S R)))
    (hR : ∀ (T' : Scheme.{0}) (t' : T' ⟶ Spec (CommRingCat.of R)) (P' Q : SchemeHomOver t' (pullback.snd f (bι S R))),
      (LR.mul t' P' Q).1 ≫ pullback.fst f (bι S R) =
        (G.mul (t' ≫ bι S R) ⟨P'.1 ≫ pullback.fst f (bι S R), by rw [Category.assoc, pullback.condition, ← Category.assoc, P'.2]⟩
          ⟨Q.1 ≫ pullback.fst f (bι S R), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1)
    (LX : RelativeGroupLaw RK (pullback.snd (pullback.snd f (bι S R)) (Spec.map (CommRingCat.ofHom (algebraMap R RK)))))
    (hX : ∀ (T' : Scheme.{0}) (t' : T' ⟶ Spec (CommRingCat.of RK))
      (P' Q : SchemeHomOver t' (pullback.snd (pullback.snd f (bι S R)) (Spec.map (CommRingCat.ofHom (algebraMap R RK))))),
      (LX.mul t' P' Q).1 ≫ pullback.fst _ _ =
        (LR.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap R RK)))
          ⟨P'.1 ≫ pullback.fst _ _, by rw [Category.assoc, pullback.condition, ← Category.assoc, P'.2]⟩
          ⟨Q.1 ≫ pullback.fst _ _, by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1)
    (LT : RelativeGroupLaw T (pullback.snd f (bι S T)))
    (hT : ∀ (T' : Scheme.{0}) (t' : T' ⟶ Spec (CommRingCat.of T)) (P' Q : SchemeHomOver t' (pullback.snd f (bι S T))),
      (LT.mul t' P' Q).1 ≫ pullback.fst f (bι S T) =
        (G.mul (t' ≫ bι S T) ⟨P'.1 ≫ pullback.fst f (bι S T), by rw [Category.assoc, pullback.condition, ← Category.assoc, P'.2]⟩
          ⟨Q.1 ≫ pullback.fst f (bι S T), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1)
    {T' : Scheme.{0}} (t' : T' ⟶ Spec (CommRingCat.of T)) (P' Q : SchemeHomOver t' (pullback.snd f (bι S T))) :
    (LT.mul t' P' Q).1 ≫ kap₃ f θ₀ hθ₀ θ hθ =
      (LX.mul (t' ≫ Spec.map (CommRingCat.ofHom θ))
        ⟨P'.1 ≫ kap₃ f θ₀ hθ₀ θ hθ, by rw [Category.assoc, (isPullback_kap₃ f θ₀ hθ₀ θ hθ).w, ← Category.assoc, P'.2]⟩
        ⟨Q.1 ≫ kap₃ f θ₀ hθ₀ θ hθ, by rw [Category.assoc, (isPullback_kap₃ f θ₀ hθ₀ θ hθ).w, ← Category.assoc, Q.2]⟩).1 := by
  apply pullback.hom_ext
  · rw [Category.assoc, kap₃_fst, hmul_kap f G θ₀ hθ₀ LR LT hR hT, hX]
    exact mul_coe_congr _ LR (by rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hθ]) _ _ _ _
      (by simp only [Category.assoc, kap₃_fst]) (by simp only [Category.assoc, kap₃_fst])
  · have h1 : ((LT.mul t' P' Q).1 ≫ kap₃ f θ₀ hθ₀ θ hθ) ≫ pullback.snd _ _ = t' ≫ Spec.map (CommRingCat.ofHom θ) := by
      rw [Category.assoc, kap₃_snd, ← Category.assoc, (LT.mul t' P' Q).2]
    exact h1.trans ((LX.mul (t' ≫ Spec.map (CommRingCat.ofHom θ)) _ _).2).symm

theorem actLift_kap₃ {I : Type} (act : I → (A ⟶ A)) (act_over : ∀ x : I, act x ≫ f = f) (x : I) :
    actLift f act act_over T x ≫ kap₃ f θ₀ hθ₀ θ hθ = kap₃ f θ₀ hθ₀ θ hθ ≫ actLift₂ f act act_over x := by
  apply pullback.hom_ext
  · rw [Category.assoc, kap₃_fst, Category.assoc, actLift₂_fst, kap₃_fst_assoc, actLift_kap]
  · rw [Category.assoc, kap₃_snd, Category.assoc, actLift₂_snd, kap₃_snd, actLift_snd_assoc]

end Kap3

end DatumAtStage

end

open DatumAtStage in
set_option maxHeartbeats 800000 in
theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (N : ℕ) (S : Type) [CommRing S] [IsNoetherianRing S] (h2 : IsUnit (2 : S)) (E : FakeEllipticCurve Λ N S)
(hKSPREAD : (∀ {S : Type} [CommRing S] [IsNoetherianRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (𝔭 : PrimeSpectrum S)
    (h𝔭 : (∀ (L' : RelativeGroupLaw (Localization.AtPrime 𝔭.asIdeal) (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))))),
          (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of (Localization.AtPrime 𝔭.asIdeal)))
              (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))))),
              (L'.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))) =
                (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal))))
                  ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))),
                    by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                  ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))),
                    by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
          KernelIsTwoTorsion (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal))))) L'
            ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))))).obj 𝓛))),
      ∃ g : S, g ∉ 𝔭.asIdeal ∧
      (∀ (L' : RelativeGroupLaw (Localization.Away g) (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))))),
          (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of (Localization.Away g)))
              (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))))),
              (L'.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))) =
                (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g))))
                  ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))),
                    by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                  ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))),
                    by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
          KernelIsTwoTorsion (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g))))) L'
            ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))))).obj 𝓛))))
        (hROS : (∀ {S : Type} [CommRing S] [IsNoetherianRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    {I : Type} (act : I → (A ⟶ A)) (act_over : ∀ x : I, act x ≫ f = f) (star : I → I)
    (𝔭 : PrimeSpectrum S)
    (h𝔭 : (∀ (L' : RelativeGroupLaw (Localization.AtPrime 𝔭.asIdeal) (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))))),
          (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of (Localization.AtPrime 𝔭.asIdeal)))
              (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))))),
              (L'.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))) =
                (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal))))
                  ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))),
                    by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                  ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))),
                    by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
          ∀ (act' : I → (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))) ⟶
              pullback f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal))))))
            (act'_over : ∀ x : I, act' x ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))) =
              pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal))))),
            (∀ x : I, act' x ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))) =
              pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))) ≫ act x) →
          RosatiCompatible (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal))))) L'
            ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))))).obj 𝓛)
            act' act'_over star)),
      ∃ g : S, g ∉ 𝔭.asIdeal ∧
      (∀ (L' : RelativeGroupLaw (Localization.Away g) (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))))),
          (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of (Localization.Away g)))
              (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))))),
              (L'.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))) =
                (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g))))
                  ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))),
                    by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                  ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))),
                    by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
          ∀ (act' : I → (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))) ⟶
              pullback f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g))))))
            (act'_over : ∀ x : I, act' x ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))) =
              pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g))))),
            (∀ x : I, act' x ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))) =
              pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))) ≫ act x) →
          RosatiCompatible (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g))))) L'
            ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))))).obj 𝓛)
            act' act'_over star)))
    (𝔭 : PrimeSpectrum S)
    (hdat𝔭 : ∀ (L' : RelativeGroupLaw (Localization.AtPrime 𝔭.asIdeal) (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))))),
        (∀ (T : Scheme) (t' : T ⟶ Spec (CommRingCat.of (Localization.AtPrime 𝔭.asIdeal)))
            (P Q : SchemeHomOver t' (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))))),
            (L'.mul t' P Q).1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))) =
              (E.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))))
                ⟨P.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
        ∃ 𝓛' : (pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal))))).Modules,
          CerednikDrinfeld.QM.IsCanonicalPolData (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal))))) L'
            (fun x : ↥Λ => pullback.lift (pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))) ≫ E.act x) (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))))
              (by rw [Category.assoc, E.act_over]; exact pullback.condition))
            (fun x => pullback.lift_snd _ _ _)
            star 𝓛')
    :
    ∃ (g₀ : S) (hg₀ : g₀ ∉ 𝔭.asIdeal) (ψ : Localization.Away g₀ →+* Localization.AtPrime 𝔭.asIdeal)
    (hψ : ψ.comp (algebraMap S (Localization.Away g₀)) = algebraMap S (Localization.AtPrime 𝔭.asIdeal))
    (𝓜 : (pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀))))).Modules),
      Scheme.Modules.IsInvertible 𝓜 ∧
      (∀ (L' : RelativeGroupLaw (Localization.Away g₀) (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀)))))),
        (∀ (T : Scheme) (t' : T ⟶ Spec (CommRingCat.of (Localization.Away g₀)))
            (P Q : SchemeHomOver t' (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀)))))),
            (L'.mul t' P Q).1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀)))) =
              (E.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀)))))
                ⟨P.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀)))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀)))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
        KernelIsTwoTorsion (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀))))) L' 𝓜 ∧
        IsSymmetric (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀))))) L' 𝓜 ∧
        RosatiCompatible (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀))))) L' 𝓜
            (fun x : ↥Λ => pullback.lift (pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀)))) ≫ E.act x) (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀)))))
              (by rw [Category.assoc, E.act_over]; exact pullback.condition))
            (fun x => pullback.lift_snd _ _ _) star) ∧
      (∀ (L' : RelativeGroupLaw (Localization.AtPrime 𝔭.asIdeal) (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))))),
        (∀ (T : Scheme) (t' : T ⟶ Spec (CommRingCat.of (Localization.AtPrime 𝔭.asIdeal)))
            (P Q : SchemeHomOver t' (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))))),
            (L'.mul t' P Q).1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))) =
              (E.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))))
                ⟨P.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
        CerednikDrinfeld.QM.IsCanonicalPolData (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal))))) L'
            (fun x : ↥Λ => pullback.lift (pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))) ≫ E.act x) (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))))
              (by rw [Category.assoc, E.act_over]; exact pullback.condition))
            (fun x => pullback.lift_snd _ _ _)
            star
          ((Scheme.Modules.pullback (pullback.lift (pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))))
              (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))) ≫ Spec.map (CommRingCat.ofHom ψ))
              (by rw [pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ]) :
              pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))) ⟶
                pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀)))))).obj 𝓜)) := by
  classical
  haveI : IsProper E.f := E.bundle.proper

  have cP := baseChange_compat E.f E.L (Localization.AtPrime 𝔭.asIdeal)
  obtain ⟨𝓛', hd'⟩ := hdat𝔭 (E.L.baseChange (bι S (Localization.AtPrime 𝔭.asIdeal))) (fun T t' P' Q => cP T t' P' Q)

  obtain ⟨r₀, hr₀, ψ, hψ, 𝓜r, h𝓜r, ⟨e⟩⟩ :=
    Scheme.Modules.exists_isInvertible_nonempty_iso_pullback_of_isInvertible_atPrime_of_isSeparated E.f 𝔭.asIdeal 𝓛' hd'.1
  have hdP : CerednikDrinfeld.QM.IsCanonicalPolData (pullback.snd E.f (bι S (Localization.AtPrime 𝔭.asIdeal))) (E.L.baseChange (bι S (Localization.AtPrime 𝔭.asIdeal)))
      (actLift E.f E.act E.act_over (Localization.AtPrime 𝔭.asIdeal)) (fun x => pullback.lift_snd _ _ _) star
      ((Scheme.Modules.pullback (kap E.f ψ hψ)).obj 𝓜r) :=
    CerednikDrinfeld.QM.IsCanonicalPolData.of_iso _ _ _ _ _ e.symm hd'

  have hdisj : Disjoint (↑(Submonoid.powers r₀) : Set S) ↑𝔭.asIdeal := by
    rw [Set.disjoint_left]
    rintro x ⟨n, rfl⟩ hx
    exact hr₀ (𝔭.isPrime.mem_of_pow_mem n hx)
  let 𝔭₀ : PrimeSpectrum (Localization.Away r₀) :=
    ⟨Ideal.map (algebraMap S (Localization.Away r₀)) 𝔭.asIdeal, IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers r₀) _ 𝔭.asIdeal 𝔭.isPrime hdisj⟩
  haveI h𝔭₀prime : 𝔭₀.asIdeal.IsPrime := 𝔭₀.2
  haveI : IsNoetherianRing (Localization.Away r₀) := IsLocalization.isNoetherianRing (Submonoid.powers r₀) _ inferInstance
  have h𝔭₀ : Ideal.comap (algebraMap S (Localization.Away r₀)) 𝔭₀.asIdeal = 𝔭.asIdeal :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers r₀) (Localization.Away r₀) 𝔭.isPrime hdisj
  have hunits : ∀ y : 𝔭.asIdeal.primeCompl,
      IsUnit (((algebraMap (Localization.Away r₀) (Localization.AtPrime 𝔭₀.asIdeal)).comp (algebraMap S (Localization.Away r₀))) y) := by
    intro y
    refine IsLocalization.map_units (Localization.AtPrime 𝔭₀.asIdeal) (⟨algebraMap S (Localization.Away r₀) y, ?_⟩ : 𝔭₀.asIdeal.primeCompl)
    intro h
    have h' : (y : S) ∈ Ideal.comap (algebraMap S (Localization.Away r₀)) 𝔭₀.asIdeal := Ideal.mem_comap.mpr h
    rw [h𝔭₀] at h'
    exact y.2 h'
  let φ₀ : (Localization.AtPrime 𝔭.asIdeal) →+* Localization.AtPrime 𝔭₀.asIdeal := IsLocalization.lift (M := 𝔭.asIdeal.primeCompl) hunits
  have hφ₀ : φ₀.comp (algebraMap S (Localization.AtPrime 𝔭.asIdeal)) = (algebraMap (Localization.Away r₀) (Localization.AtPrime 𝔭₀.asIdeal)).comp (algebraMap S (Localization.Away r₀)) :=
    IsLocalization.lift_comp _
  have hψφ : φ₀.comp ψ = algebraMap (Localization.Away r₀) (Localization.AtPrime 𝔭₀.asIdeal) :=
    IsLocalization.ringHom_ext (Submonoid.powers r₀) (by rw [RingHom.comp_assoc, hψ, hφ₀])

  have cR0 := baseChange_compat E.f E.L (Localization.Away r₀)
  have hA0 : AbelianSchemePropertyBundle (Localization.Away r₀) (pullback.snd E.f (bι S (Localization.Away r₀))) :=
    E.bundle.of_isPullback (IsPullback.of_hasPullback E.f (bι S (Localization.Away r₀)))

  have hkk : kap₂ E.f φ₀ hφ₀ ≫ kap E.f ψ hψ =
      pullback.fst (pullback.snd E.f (bι S (Localization.Away r₀))) (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away r₀) (Localization.AtPrime 𝔭₀.asIdeal)))) := by
    apply pullback.hom_ext
    · rw [Category.assoc, kap_fst, kap₂_fst]
    · rw [Category.assoc, kap_snd, kap₂_snd_assoc, pullback.condition, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψφ]
  have eKK : (Scheme.Modules.pullback (kap₂ E.f φ₀ hφ₀)).obj ((Scheme.Modules.pullback (kap E.f ψ hψ)).obj 𝓜r) ≅
      (Scheme.Modules.pullback (pullback.fst (pullback.snd E.f (bι S (Localization.Away r₀)))
        (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away r₀) (Localization.AtPrime 𝔭₀.asIdeal)))))).obj 𝓜r :=
    (Scheme.Modules.pullbackComp _ _).app 𝓜r ≪≫ (Scheme.Modules.pullbackCongr hkk).app 𝓜r

  obtain ⟨rK, hrK, hKout⟩ := hKSPREAD (E.L.baseChange (bι S (Localization.Away r₀))) hA0 𝓜r h𝓜r 𝔭₀ (by
    intro L' hL'
    have ht := KernelIsTwoTorsion.pullback_of_isPullback_of_isInvertible φ₀ (isPullback_kap₂ E.f φ₀ hφ₀)
      (E.L.baseChange (bι S (Localization.AtPrime 𝔭.asIdeal))) L' (hmul_kap₂ E.f E.L φ₀ hφ₀ _ cR0 L' hL' _ cP) _ (h𝓜r.pullback _) hdP.2.2.1
    exact kernelIsTwoTorsion_of_iso _ _ ((h𝓜r.pullback _).pullback _) (h𝓜r.pullback _) eKK ht)

  obtain ⟨rR, hrR, hRout⟩ := hROS (E.L.baseChange (bι S (Localization.Away r₀))) hA0 𝓜r h𝓜r (actLift E.f E.act E.act_over (Localization.Away r₀))
    (fun x => actLift_snd E.f E.act E.act_over (Localization.Away r₀) x) star 𝔭₀ (by
    intro L' hL' act' act'_over hact'
    have ht := RosatiCompatible.pullback_of_isPullback _ _ φ₀ _ (E.L.baseChange (bι S (Localization.AtPrime 𝔭.asIdeal))) _ L' (kap₂ E.f φ₀ hφ₀)
      (isPullback_kap₂ E.f φ₀ hφ₀) (hmul_kap₂ E.f E.L φ₀ hφ₀ _ cR0 L' hL' _ cP)
      (actLift E.f E.act E.act_over (Localization.AtPrime 𝔭.asIdeal)) (fun x => actLift_snd E.f E.act E.act_over (Localization.AtPrime 𝔭.asIdeal) x) act' act'_over
      (act_kap₂ E.f φ₀ hφ₀ E.act E.act_over act' act'_over hact') star _ (h𝓜r.pullback _) hdP.2.2.2.2.2
    exact rosatiCompatible_of_iso _ _ ((h𝓜r.pullback _).pullback _) (h𝓜r.pullback _) eKK _ _ _ ht)

  have h56 := RelativeGroupLaw.comp_negMor_eq_negMor_comp_of_compatible E.L (Localization.Away r₀) (Localization.AtPrime 𝔭.asIdeal) ψ hψ
    (E.L.baseChange (bι S (Localization.Away r₀))) (E.L.baseChange (bι S (Localization.AtPrime 𝔭.asIdeal))) cR0 cP (kap E.f ψ hψ) (kap_fst E.f ψ hψ) (kap_snd E.f ψ hψ)
  obtain ⟨eσ⟩ := (locIsoOnBase_iff_nonempty_iso_of_isLocalRing _ _ _).mp hdP.2.1
  have hiso : Nonempty ((Scheme.Modules.pullback (kap E.f ψ hψ)).obj
      ((Scheme.Modules.pullback (negMor (pullback.snd E.f (bι S (Localization.Away r₀))) (E.L.baseChange (bι S (Localization.Away r₀))))).obj 𝓜r) ≅
      (Scheme.Modules.pullback (kap E.f ψ hψ)).obj 𝓜r) :=
    ⟨(Scheme.Modules.pullbackComp _ _).app 𝓜r ≪≫ (Scheme.Modules.pullbackCongr h56).app 𝓜r ≪≫
      ((Scheme.Modules.pullbackComp _ _).app 𝓜r).symm ≪≫ eσ⟩
  obtain ⟨r₁, hr₁, ψ₁, hψ₁, ⟨e₁⟩⟩ :=
    Scheme.Modules.exists_nonempty_iso_pullback_away_of_nonempty_iso_pullback_atPrime E.f 𝔭.asIdeal r₀ hr₀ ψ hψ
      _ 𝓜r (h𝓜r.pullback _) h𝓜r hiso

  obtain ⟨nK, aK, haK⟩ := IsLocalization.Away.surj r₀ rK
  obtain ⟨nR, aR, haR⟩ := IsLocalization.Away.surj r₀ rR
  have hnum : ∀ (r : (Localization.Away r₀)) (n : ℕ) (a : S), r ∉ 𝔭₀.asIdeal → r * algebraMap S (Localization.Away r₀) r₀ ^ n = algebraMap S (Localization.Away r₀) a →
      a ∉ 𝔭.asIdeal := by
    intro r n a hr h ha
    have h1 : r * algebraMap S (Localization.Away r₀) r₀ ^ n ∈ 𝔭₀.asIdeal := by rw [h]; exact Ideal.mem_map_of_mem _ ha
    rcases 𝔭₀.isPrime.mem_or_mem h1 with h2 | h2
    · exact hr h2
    · have h3 : r₀ ^ n ∈ 𝔭.asIdeal := by
        rw [← h𝔭₀, Ideal.mem_comap, map_pow]; exact h2
      exact hr₀ (𝔭.isPrime.mem_of_pow_mem n h3)
  have haK' := hnum rK nK aK hrK haK
  have haR' := hnum rR nR aR hrR haR
  let g₀ : S := r₀ * r₁ * aK * aR
  have hg₀ : g₀ ∉ 𝔭.asIdeal := by
    have : g₀ ∈ 𝔭.asIdeal.primeCompl :=
      Submonoid.mul_mem _ (Submonoid.mul_mem _ (Submonoid.mul_mem _ hr₀ hr₁) haK') haR'
    exact this

  have ur₀ : IsUnit (algebraMap S (Localization.Away g₀) r₀) := IsLocalization.Away.isUnit_of_dvd g₀ ⟨r₁ * aK * aR, by ring⟩
  have ur₁ : IsUnit (algebraMap S (Localization.Away g₀) r₁) := IsLocalization.Away.isUnit_of_dvd g₀ ⟨r₀ * aK * aR, by ring⟩
  have uaK : IsUnit (algebraMap S (Localization.Away g₀) aK) := IsLocalization.Away.isUnit_of_dvd g₀ ⟨r₀ * r₁ * aR, by ring⟩
  have uaR : IsUnit (algebraMap S (Localization.Away g₀) aR) := IsLocalization.Away.isUnit_of_dvd g₀ ⟨r₀ * r₁ * aK, by ring⟩
  let θ₀ : (Localization.Away r₀) →+* (Localization.Away g₀) := IsLocalization.Away.lift r₀ ur₀
  have hθ₀ : θ₀.comp (algebraMap S (Localization.Away r₀)) = algebraMap S (Localization.Away g₀) := IsLocalization.Away.lift_comp r₀ ur₀
  let θ₁ : Localization.Away r₁ →+* (Localization.Away g₀) := IsLocalization.Away.lift r₁ ur₁
  have hθ₁ : θ₁.comp (algebraMap S (Localization.Away r₁)) = algebraMap S (Localization.Away g₀) := IsLocalization.Away.lift_comp r₁ ur₁
  have huK : IsUnit (θ₀ rK) := by
    have h1 : θ₀ rK * algebraMap S (Localization.Away g₀) r₀ ^ nK = algebraMap S (Localization.Away g₀) aK := by
      have := congrArg θ₀ haK
      rw [map_mul, map_pow] at this
      rw [← hθ₀]; exact this
    exact isUnit_of_mul_isUnit_left (by rw [h1]; exact uaK)
  have huR : IsUnit (θ₀ rR) := by
    have h1 : θ₀ rR * algebraMap S (Localization.Away g₀) r₀ ^ nR = algebraMap S (Localization.Away g₀) aR := by
      have := congrArg θ₀ haR
      rw [map_mul, map_pow] at this
      rw [← hθ₀]; exact this
    exact isUnit_of_mul_isUnit_left (by rw [h1]; exact uaR)
  let θK : Localization.Away rK →+* (Localization.Away g₀) := IsLocalization.Away.lift rK huK
  have hθK : θK.comp (algebraMap (Localization.Away r₀) (Localization.Away rK)) = θ₀ := IsLocalization.Away.lift_comp rK huK
  let θR : Localization.Away rR →+* (Localization.Away g₀) := IsLocalization.Away.lift rR huR
  have hθR : θR.comp (algebraMap (Localization.Away r₀) (Localization.Away rR)) = θ₀ := IsLocalization.Away.lift_comp rR huR
  have ug₀P : IsUnit (algebraMap S (Localization.AtPrime 𝔭.asIdeal) g₀) := IsLocalization.map_units _ (⟨g₀, hg₀⟩ : 𝔭.asIdeal.primeCompl)
  let ψT : (Localization.Away g₀) →+* (Localization.AtPrime 𝔭.asIdeal) := IsLocalization.Away.lift g₀ ug₀P
  have hψT : ψT.comp (algebraMap S (Localization.Away g₀)) = algebraMap S (Localization.AtPrime 𝔭.asIdeal) := IsLocalization.Away.lift_comp g₀ ug₀P
  have hθψ : ψT.comp θ₀ = ψ := IsLocalization.ringHom_ext (Submonoid.powers r₀) (by rw [RingHom.comp_assoc, hθ₀, hψT, hψ])
  have hθ₁ψ₁ : θ₁.comp ψ₁ = θ₀ := IsLocalization.ringHom_ext (Submonoid.powers r₀) (by rw [RingHom.comp_assoc, hψ₁, hθ₁, hθ₀])

  have cT := baseChange_compat E.f E.L (Localization.Away g₀)
  refine ⟨g₀, hg₀, ψT, hψT, (Scheme.Modules.pullback (kap E.f θ₀ hθ₀)).obj 𝓜r, h𝓜r.pullback _, ?_, ?_⟩
  ·
    intro L' hL'
    obtain rfl := RelativeGroupLaw.eq_of_forall_mul_comp_fst_eq (bι S (Localization.Away g₀)) E.L L' (E.L.baseChange (bι S (Localization.Away g₀))) hL' cT
    refine ⟨?_, ?_, ?_⟩
    ·
      have cXK := baseChange_compat (pullback.snd E.f (bι S (Localization.Away r₀))) (E.L.baseChange (bι S (Localization.Away r₀))) (Localization.Away rK)
      have hKX := hKout ((E.L.baseChange (bι S (Localization.Away r₀))).baseChange (bι (Localization.Away r₀) (Localization.Away rK))) (fun T t' P' Q => cXK T t' P' Q)
      have ht := KernelIsTwoTorsion.pullback_of_isPullback_of_isInvertible θK (isPullback_kap₃ E.f θ₀ hθ₀ θK hθK)
        _ (E.L.baseChange (bι S (Localization.Away g₀)))
        (hmul_kap₃ E.f E.L θ₀ hθ₀ θK hθK _ cR0 _ (fun T t' P' Q => cXK T t' P' Q) _ cT) _ (h𝓜r.pullback _) hKX
      exact kernelIsTwoTorsion_of_iso _ _ ((h𝓜r.pullback _).pullback _) (h𝓜r.pullback _)
        ((Scheme.Modules.pullbackComp _ _).app 𝓜r ≪≫ (Scheme.Modules.pullbackCongr (kap₃_fst E.f θ₀ hθ₀ θK hθK)).app 𝓜r) ht
    ·
      have h56T := RelativeGroupLaw.comp_negMor_eq_negMor_comp_of_compatible E.L (Localization.Away r₀) (Localization.Away g₀) θ₀ hθ₀
        (E.L.baseChange (bι S (Localization.Away r₀))) (E.L.baseChange (bι S (Localization.Away g₀))) cR0 cT (kap E.f θ₀ hθ₀) (kap_fst E.f θ₀ hθ₀) (kap_snd E.f θ₀ hθ₀)
      have hc : kap E.f θ₁ hθ₁ ≫ kap E.f ψ₁ hψ₁ = kap E.f θ₀ hθ₀ := kap_comp E.f ψ₁ hψ₁ θ₁ hθ₁ θ₀ hθ₀ hθ₁ψ₁
      apply locIsoOnBase_of_iso
      exact (Scheme.Modules.pullbackComp _ _).app 𝓜r ≪≫ (Scheme.Modules.pullbackCongr h56T.symm).app 𝓜r ≪≫
        ((Scheme.Modules.pullbackComp _ _).app 𝓜r).symm ≪≫
        (Scheme.Modules.pullbackCongr hc.symm).app _ ≪≫ ((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫
        (Scheme.Modules.pullback (kap E.f θ₁ hθ₁)).mapIso e₁ ≪≫
        (Scheme.Modules.pullbackComp _ _).app 𝓜r ≪≫ (Scheme.Modules.pullbackCongr hc).app 𝓜r
    ·
      have cXR := baseChange_compat (pullback.snd E.f (bι S (Localization.Away r₀))) (E.L.baseChange (bι S (Localization.Away r₀))) (Localization.Away rR)
      have hRX := hRout ((E.L.baseChange (bι S (Localization.Away r₀))).baseChange (bι (Localization.Away r₀) (Localization.Away rR))) (fun T t' P' Q => cXR T t' P' Q)
        (actLift₂ E.f E.act E.act_over) (fun x => actLift₂_snd E.f E.act E.act_over x) (fun x => actLift₂_fst E.f E.act E.act_over x)
      have ht := RosatiCompatible.pullback_of_isPullback _ _ θR _ _ _ (E.L.baseChange (bι S (Localization.Away g₀))) (kap₃ E.f θ₀ hθ₀ θR hθR)
        (isPullback_kap₃ E.f θ₀ hθ₀ θR hθR)
        (hmul_kap₃ E.f E.L θ₀ hθ₀ θR hθR _ cR0 _ (fun T t' P' Q => cXR T t' P' Q) _ cT)
        (actLift₂ E.f E.act E.act_over) (fun x => actLift₂_snd E.f E.act E.act_over x)
        (actLift E.f E.act E.act_over (Localization.Away g₀)) (fun x => actLift_snd E.f E.act E.act_over (Localization.Away g₀) x)
        (actLift_kap₃ E.f θ₀ hθ₀ θR hθR E.act E.act_over) star _ (h𝓜r.pullback _) hRX
      exact rosatiCompatible_of_iso _ _ ((h𝓜r.pullback _).pullback _) (h𝓜r.pullback _)
        ((Scheme.Modules.pullbackComp _ _).app 𝓜r ≪≫ (Scheme.Modules.pullbackCongr (kap₃_fst E.f θ₀ hθ₀ θR hθR)).app 𝓜r) _ _ _ ht
  ·
    intro L'' hL''
    obtain rfl := RelativeGroupLaw.eq_of_forall_mul_comp_fst_eq (bι S (Localization.AtPrime 𝔭.asIdeal)) E.L L'' (E.L.baseChange (bι S (Localization.AtPrime 𝔭.asIdeal))) hL'' cP
    have hc : kap E.f ψT hψT ≫ kap E.f θ₀ hθ₀ = kap E.f ψ hψ := kap_comp E.f θ₀ hθ₀ ψT hψT ψ hψ hθψ
    exact CerednikDrinfeld.QM.IsCanonicalPolData.of_iso _ _ _ _ _
      ((Scheme.Modules.pullbackCongr hc.symm).app 𝓜r ≪≫ ((Scheme.Modules.pullbackComp _ _).app 𝓜r).symm) hdP

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_not_mem_stage_kernelIsTwoTorsion_isSymmetric_rosatiCompatible_of_isCanonicalPolData_atPrime
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_not_mem_stage_kernelIsTwoTorsion_isSymmetric_rosatiCompatible_of_isCanonicalPolData_atPrime (solution)
