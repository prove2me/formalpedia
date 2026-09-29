-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_isFormalModuleOf_of_isLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/20a9a216-8127-5236-acd4-e398bc4a6bf5

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_cover_isFormalModuleOf
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullback_levelIff
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_IsFormalModuleOf_map_of_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isFormalModuleOf_of_isLocalRing
p2m_attr_erase "instance" "MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup AlgebraicGeometry.SquareZero.isLocalRing' AlgebraicGeometry.SquareZero.isLocalRing AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited"
p2m_attr_erase "simp" "MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec AlgebraicGeometry.TangentPoints.map_coe AlgebraicGeometry.SquareZero.basePoint_toBase_assoc AlgebraicGeometry.SquareZero.basePoint_toBase AlgebraicGeometry.SquareZero.basePoint_specMap AlgebraicGeometry.SquareZero.basePointOver_coe AlgebraicGeometry.SquareZero.specMap_toBase_assoc AlgebraicGeometry.SquareZero.specMapOver_coe AlgebraicGeometry.RelPicard.TrivialModDeformations.map_coe AlgebraicGeometry.SquareZero.specMap_toBase AlgebraicGeometry.SquareZero.basePoint_specMap_assoc AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc"
p2m_attr_erase "simp" "NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM

open scoped Quaternion TensorProduct

noncomputable section

namespace P2mKcForgetF1Loc

section General

variable {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)

theorem mul_val_congr {T : Scheme.{0}} {s s' : T ⟶ Spec (CommRingCat.of R)} (h : s = s')
    {P Q : SchemeHomOver s f} {P' Q' : SchemeHomOver s' f} (hP : P.1 = P'.1) (hQ : Q.1 = Q'.1) :
    (L.mul s P Q).1 = (L.mul s' P' Q').1 := by
  subst h
  rw [Subtype.ext hP, Subtype.ext hQ]

end General

section PB

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

theorem isPullback_id {S : Type} [CommRing S] (E : FakeEllipticCurve Λ N S) :
    FakeEllipticCurve.IsPullback (RingHom.id S) E E := by
  have hb : Spec.map (CommRingCat.ofHom (RingHom.id S)) = 𝟙 _ := by rw [CommRingCat.ofHom_id, Spec.map_id]
  have hsq : IsPullback (𝟙 E.A) E.f E.f (Spec.map (CommRingCat.ofHom (RingHom.id S))) := by
    rw [hb]; exact IsPullback.of_horiz_isIso ⟨by simp⟩
  refine ⟨𝟙 _, hsq, ?_, ?_, ?_⟩
  · intro T t P Q
    rw [Category.comp_id]
    exact mul_val_congr E.L (by rw [hb, Category.comp_id]) (Category.comp_id _).symm (Category.comp_id _).symm
  · intro x; simp
  · intro T t P hP
    obtain ⟨P₀, h⟩ := hP
    exact ⟨P₀, by rw [h, Category.comp_id]⟩

theorem isPullback_of_isPullback_comp {S S' S'' : Type} [CommRing S] [CommRing S'] [CommRing S'']
    (φ : S →+* S') (ψ : S' →+* S'')
    (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S') (E'' : FakeEllipticCurve Λ N S'')
    (g' : E'.A ⟶ E.A) (hg' : IsPullback g' E'.f E.f (Spec.map (CommRingCat.ofHom φ)))
    (hmul' : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' E'.f),
      (E'.L.mul t' P Q).1 ≫ g' =
        (E.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨P.1 ≫ g', by rw [Category.assoc, hg'.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g', by rw [Category.assoc, hg'.w, ← Category.assoc, Q.2]⟩).1)
    (hact' : ∀ x : ↥Λ, E'.act x ≫ g' = g' ≫ E.act x)
    (hlev' : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' E'.f),
      (∃ P₀ : T ⟶ E.C, P₀ ≫ E.lev = P.1 ≫ g') → FactorsThrough E'.lev P)
    (h'' : FakeEllipticCurve.IsPullback (ψ.comp φ) E E'') :
    FakeEllipticCurve.IsPullback ψ E' E'' := by
  obtain ⟨g'', hg'', hmul'', hact'', hlev''⟩ := h''
  have hb : Spec.map (CommRingCat.ofHom (ψ.comp φ)) =
      Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  have hbig : IsPullback g'' E''.f E.f (Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ)) := by
    rw [← hb]; exact hg''

  have hw : g'' ≫ E.f = (E''.f ≫ Spec.map (CommRingCat.ofHom ψ)) ≫ Spec.map (CommRingCat.ofHom φ) := by
    rw [Category.assoc, ← hb]; exact hg''.w
  set h : E''.A ⟶ E'.A := hg'.lift g'' (E''.f ≫ Spec.map (CommRingCat.ofHom ψ)) hw with hh
  have hh1 : h ≫ g' = g'' := hg'.lift_fst _ _ _
  have hh2 : h ≫ E'.f = E''.f ≫ Spec.map (CommRingCat.ofHom ψ) := hg'.lift_snd _ _ _
  have hsq : IsPullback h E''.f E'.f (Spec.map (CommRingCat.ofHom ψ)) := by
    refine IsPullback.of_right ?_ hh2 hg'
    rw [hh1]; exact hbig
  refine ⟨h, hsq, ?_, ?_, ?_⟩
  ·
    intro T t P Q
    apply hg'.hom_ext
    · rw [Category.assoc, hh1, hmul'', hmul']
      refine mul_val_congr E.L (by rw [hb, Category.assoc]) ?_ ?_
      · show P.1 ≫ g'' = (P.1 ≫ h) ≫ g'
        rw [Category.assoc, hh1]
      · show Q.1 ≫ g'' = (Q.1 ≫ h) ≫ g'
        rw [Category.assoc, hh1]
    · rw [Category.assoc, hh2, ← Category.assoc, (E''.L.mul t P Q).2]
      exact ((E'.L.mul (t ≫ Spec.map (CommRingCat.ofHom ψ)) _ _).2).symm
  ·
    intro x
    apply hg'.hom_ext
    · rw [Category.assoc, hh1, hact'', Category.assoc, hact', ← Category.assoc, hh1]
    · rw [Category.assoc, hh2, ← Category.assoc, E''.act_over x, Category.assoc, E'.act_over x, hh2]
  ·
    intro T t P hP
    obtain ⟨P₀, hP₀⟩ := hlev'' t P hP
    have hR : FactorsThrough E'.lev
        (⟨P.1 ≫ h, by rw [Category.assoc, hsq.w, ← Category.assoc, P.2]⟩ :
          SchemeHomOver (t ≫ Spec.map (CommRingCat.ofHom ψ)) E'.f) :=
      hlev' _ _ ⟨P₀, by rw [hP₀, Category.assoc, hh1]⟩
    obtain ⟨P₀', hP₀'⟩ := hR
    exact ⟨P₀', hP₀'⟩

end PB

theorem exists_isUnit_of_span_eq_top {B : Type} [CommRing B] [IsLocalRing B] (s : Finset B)
    (hs : Ideal.span (s : Set B) = ⊤) : ∃ c ∈ s, IsUnit c := by
  by_contra h
  push Not at h
  have hle : Ideal.span (s : Set B) ≤ IsLocalRing.maximalIdeal B :=
    Ideal.span_le.mpr fun c hc => (IsLocalRing.mem_maximalIdeal c).mpr (h c hc)
  rw [hs, top_le_iff] at hle
  exact (IsLocalRing.maximalIdeal.isMaximal B).ne_top hle

end P2mKcForgetF1Loc

end

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal

open scoped Quaternion TensorProduct NumberField

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {q : ℕ} [Fact q.Prime]
    (coord : ↥Λ → Zp2 q × Zp2 q) (hcoord : IsOrderCoord Λ q coord)
    (B : Type) [CommRing B] [IsLocalRing B] (hq : IsNilpotent ((q : ℕ) : B)) (E : FakeEllipticCurve Λ N B) :
    ∃ X : FormalODModule q B, E.IsFormalModuleOf coord X := by
  classical

  obtain ⟨s, hspan, hcov⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_cover_isFormalModuleOf coord hcoord B hq E

  obtain ⟨c, hcs, hcu⟩ := P2mKcForgetF1Loc.exists_isUnit_of_span_eq_top s hspan
  set L : Type := Localization.Away c with hL

  obtain ⟨E', g', hg', hmul', hact', hlev', hlev'iff⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_levelIff (algebraMap B L) E
  have hE' : FakeEllipticCurve.IsPullback (algebraMap B L) E E' := ⟨g', hg', hmul', hact', hlev'⟩
  obtain ⟨X', hX'⟩ := hcov c hcs E' hE'

  have hunits : Submonoid.powers c ≤ IsUnit.submonoid B := by
    rintro y ⟨n, rfl⟩
    exact hcu.pow n
  let e : B ≃ₐ[B] L := IsLocalization.atUnits B (Submonoid.powers c) (S := L) hunits
  let ψ : L →+* B := (e.symm : L ≃ₐ[B] B).toRingEquiv.toRingHom
  have hψ : ψ.comp (algebraMap B L) = RingHom.id B := by
    ext y
    change e.symm (algebraMap B L y) = y
    rw [← e.commutes y]
    exact e.symm_apply_apply y

  have hid : FakeEllipticCurve.IsPullback (ψ.comp (algebraMap B L)) E E := by
    rw [hψ]; exact P2mKcForgetF1Loc.isPullback_id E
  have hE : FakeEllipticCurve.IsPullback ψ E' E :=
    P2mKcForgetF1Loc.isPullback_of_isPullback_comp (algebraMap B L) ψ E E' E g' hg' hmul' hact' hlev'iff hid
  exact ⟨X'.map ψ,
    CerednikDrinfeld.QM.FakeEllipticCurve.IsFormalModuleOf.map_of_isPullback coord ψ E' E hE X' hX'⟩

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isFormalModuleOf_of_isLocalRing
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isFormalModuleOf_of_isLocalRing (solution)
