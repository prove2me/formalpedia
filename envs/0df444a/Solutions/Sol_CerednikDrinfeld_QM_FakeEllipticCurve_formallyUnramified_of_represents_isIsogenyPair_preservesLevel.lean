-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.formallyUnramified_of_represents_isIsogenyPair_preservesLevel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/2bbadea8-fe4d-5aa4-918c-6613a5b3feaa

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Definitions.Def_CerednikDrinfeld_QMRigidification
import Theorems.Thm_AlgebraicGeometry_formallyUnramified_of_forall_lift_unique_of_isArtinianRing
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullback_levelIff
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_IsPullbackVia_comp
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_lev_of_exists_comp_eq_comp_of_isPullbackVia
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_comp_act_eq_comp_act_of_isPullbackVia_of_isIsogenyPair_of_ker_pow_eq_bot
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_formallyUnramified_of_represents_isIsogenyPair_preservesLevel
p2m_attr_erase "instance" "AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom"
p2m_attr_erase "simp" "AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply"

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

namespace UnramD

theorem mul_val_congr {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : GoodReductionJacobian.RelativeGroupLaw R f)
    {T : Scheme.{0}} {t t' : T ⟶ Spec (CommRingCat.of R)} (ht : t = t')
    (P Q : SchemeHomOver t f) (P' Q' : SchemeHomOver t' f) (hP : P.1 = P'.1) (hQ : Q.1 = Q'.1) :
    (L.mul t P Q).1 = (L.mul t' P' Q').1 := by
  subst ht
  rw [Subtype.ext hP, Subtype.ext hQ]

theorem ptext {S₁ : Type} [CommRing S₁] {X Y Z : Scheme.{0}} {fX : X ⟶ Spec (CommRingCat.of S₁)} {gg : X ⟶ Y} {fY : Y ⟶ Z}
    {s : Spec (CommRingCat.of S₁) ⟶ Z} (hsq : CategoryTheory.IsPullback gg fX fY s)
    {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S₁)} (P Q : SchemeHomOver t fX) (h : P.1 ≫ gg = Q.1 ≫ gg) : P = Q :=
  Subtype.ext (hsq.hom_ext h (by rw [P.2, Q.2]))

theorem isIsogenyPair_symm {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]
    (d : ℕ) (E E' : FakeEllipticCurve Λ N S) (φ : E.A ⟶ E'.A) (ψ : E'.A ⟶ E.A)
    (h : FakeEllipticCurve.IsIsogenyPair d E E' φ ψ) : FakeEllipticCurve.IsIsogenyPair d E' E ψ φ := by
  obtain ⟨hφ, hψ, mφ, mψ, lφ, lψ, c⟩ := h
  exact ⟨hψ, hφ, mψ, mφ, lψ, lφ, fun hd => (c hd).symm⟩

theorem exists_pullPair {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {U D : Type} [CommRing U] [CommRing D] (p : U →+* D)
    (dd : ℕ) (E' A' : FakeEllipticCurve Λ N U) (E'' A'' : FakeEllipticCurve Λ N D)
    (hE : E''.A ⟶ E'.A) (hhE : FakeEllipticCurve.IsPullbackVia p E' E'' hE)
    (hA : A''.A ⟶ A'.A) (hhA : FakeEllipticCurve.IsPullbackVia p A' A'' hA)
    (φ : E'.A ⟶ A'.A) (φ' : A'.A ⟶ E'.A) (hφ : φ ≫ A'.f = E'.f)
    (hp : FakeEllipticCurve.IsIsogenyPair dd E' A' φ φ') (hl : FakeEllipticCurve.PreservesLevel E' A' φ hφ) :
    ∃ (ψ : E''.A ⟶ A''.A) (ψ' : A''.A ⟶ E''.A) (hψ : ψ ≫ A''.f = E''.f),
      FakeEllipticCurve.IsIsogenyPair dd E'' A'' ψ ψ' ∧ FakeEllipticCurve.PreservesLevel E'' A'' ψ hψ ∧
        ψ ≫ hA = hE ≫ φ ∧ ψ' ≫ hE = hA ≫ φ' := by
  obtain ⟨hsqE, Emul, Eact, Elev⟩ := hhE
  obtain ⟨hsqA, Amul, Aact, Alev⟩ := hhA
  obtain ⟨hφo, hφ'o, hφmul, hφ'mul, hφlin, hφ'lin, hdeg⟩ := hp
  let ψ : E''.A ⟶ A''.A := hsqA.lift (hE ≫ φ) E''.f (by rw [Category.assoc, hφo]; exact hsqE.w)
  have hψ₁ : ψ ≫ hA = hE ≫ φ := hsqA.lift_fst _ _ _
  have hψ₂ : ψ ≫ A''.f = E''.f := hsqA.lift_snd _ _ _
  let ψ' : A''.A ⟶ E''.A := hsqE.lift (hA ≫ φ') A''.f (by rw [Category.assoc, hφ'o]; exact hsqA.w)
  have hψ'₁ : ψ' ≫ hE = hA ≫ φ' := hsqE.lift_fst _ _ _
  have hψ'₂ : ψ' ≫ E''.f = A''.f := hsqE.lift_snd _ _ _

  have ψ_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of D)) (P Q : SchemeHomOver t E''.f),
      mapPt ψ hψ₂ (E''.L.mul t P Q) = A''.L.mul t (mapPt ψ hψ₂ P) (mapPt ψ hψ₂ Q) := by
    intro T t P Q
    apply ptext hsqA
    rw [mapPt_coe, Category.assoc, hψ₁, ← Category.assoc, Emul, Amul]
    have := congrArg Subtype.val (hφmul (t ≫ Spec.map (CommRingCat.ofHom p))
      ⟨P.1 ≫ hE, by rw [Category.assoc, hsqE.w, ← Category.assoc, P.2]⟩
      ⟨Q.1 ≫ hE, by rw [Category.assoc, hsqE.w, ← Category.assoc, Q.2]⟩)
    rw [mapPt_coe] at this
    rw [this]
    exact mul_val_congr A'.L rfl _ _ _ _ (by simp only [mapPt_coe, Category.assoc, hψ₁])
      (by simp only [mapPt_coe, Category.assoc, hψ₁])
  have ψ'_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of D)) (P Q : SchemeHomOver t A''.f),
      mapPt ψ' hψ'₂ (A''.L.mul t P Q) = E''.L.mul t (mapPt ψ' hψ'₂ P) (mapPt ψ' hψ'₂ Q) := by
    intro T t P Q
    apply ptext hsqE
    rw [mapPt_coe, Category.assoc, hψ'₁, ← Category.assoc, Amul, Emul]
    have := congrArg Subtype.val (hφ'mul (t ≫ Spec.map (CommRingCat.ofHom p))
      ⟨P.1 ≫ hA, by rw [Category.assoc, hsqA.w, ← Category.assoc, P.2]⟩
      ⟨Q.1 ≫ hA, by rw [Category.assoc, hsqA.w, ← Category.assoc, Q.2]⟩)
    rw [mapPt_coe] at this
    rw [this]
    exact mul_val_congr E'.L rfl _ _ _ _ (by simp only [mapPt_coe, Category.assoc, hψ'₁])
      (by simp only [mapPt_coe, Category.assoc, hψ'₁])

  have ψ_act : ∀ x : ↥Λ, E''.act x ≫ ψ = ψ ≫ A''.act x := by
    intro x
    apply hsqA.hom_ext
    · rw [Category.assoc, hψ₁, ← Category.assoc, Eact, Category.assoc, hφlin, Category.assoc, Aact, ← Category.assoc ψ hA, hψ₁,
        Category.assoc]
    · rw [Category.assoc, hψ₂, E''.act_over, Category.assoc, A''.act_over, hψ₂]
  have ψ'_act : ∀ x : ↥Λ, A''.act x ≫ ψ' = ψ' ≫ E''.act x := by
    intro x
    apply hsqE.hom_ext
    · rw [Category.assoc, hψ'₁, ← Category.assoc, Aact, Category.assoc, hφ'lin, Category.assoc, Eact, ← Category.assoc ψ' hE, hψ'₁,
        Category.assoc]
    · rw [Category.assoc, hψ'₂, A''.act_over, Category.assoc, E''.act_over, hψ'₂]

  have ψ_deg : ∀ hm : (((dd : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
      ψ ≫ ψ' = E''.act ⟨_, hm⟩ ∧ ψ' ≫ ψ = A''.act ⟨_, hm⟩ := by
    intro hm
    obtain ⟨h1, h2⟩ := hdeg hm
    constructor
    · apply hsqE.hom_ext
      · rw [Category.assoc, hψ'₁, ← Category.assoc, hψ₁, Category.assoc, h1, Eact]
      · rw [Category.assoc, hψ'₂, hψ₂, E''.act_over]
    · apply hsqA.hom_ext
      · rw [Category.assoc, hψ₁, ← Category.assoc, hψ'₁, Category.assoc, h2, Aact]
      · rw [Category.assoc, hψ₂, hψ'₂, A''.act_over]

  have ψ_lev : FakeEllipticCurve.PreservesLevel E'' A'' ψ hψ₂ := by
    intro T t P hP
    obtain ⟨P₀, hP₀⟩ := Elev t P hP
    have hQ := hl (t ≫ Spec.map (CommRingCat.ofHom p))
      ⟨P.1 ≫ hE, by rw [Category.assoc, hsqE.w, ← Category.assoc, P.2]⟩ ⟨P₀, hP₀⟩
    obtain ⟨Q₀, hQ₀⟩ := hQ
    apply CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_lev_of_exists_comp_eq_comp_of_isPullbackVia A' p A'' hA
      ⟨hsqA, Amul, Aact, Alev⟩ t (mapPt ψ hψ₂ P)
    exact ⟨Q₀, by rw [hQ₀]; simp only [mapPt_coe, Category.assoc, hψ₁]⟩
  exact ⟨ψ, ψ', hψ₂, ⟨hψ₂, hψ'₂, ψ_hom, ψ'_hom, ψ_act, ψ'_act, ψ_deg⟩, ψ_lev, hψ₁, hψ'₁⟩

end UnramD

open UnramD in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (r d : ℕ)
    (S : Type) [CommRing S] (E A : FakeEllipticCurve Λ N S)
    (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) [LocallyOfFiniteType ξ]
    (pt : ∀ (T : Type) [CommRing T] [Algebra S T]
      (E' A' : FakeEllipticCurve Λ N T) (gE : E'.A ⟶ E.A) (_ : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
      (gA : A'.A ⟶ A.A) (_ : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA)
      (φ : E'.A ⟶ A'.A) (φ' : A'.A ⟶ E'.A) (hφ : φ ≫ A'.f = E'.f),
      FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ φ' → FakeEllipticCurve.PreservesLevel E' A' φ hφ →
        SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap S T))) ξ)

    (hX1 : ∀ (T : Type) [CommRing T] [Algebra S T]
        (E' A' : FakeEllipticCurve Λ N T) (gE : E'.A ⟶ E.A) (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
        (gA : A'.A ⟶ A.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA)
        (φ : E'.A ⟶ A'.A) (φ' : A'.A ⟶ E'.A) (hφ : φ ≫ A'.f = E'.f)
        (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ φ') (hl : FakeEllipticCurve.PreservesLevel E' A' φ hφ)
        (E'' A'' : FakeEllipticCurve Λ N T) (gE'' : E''.A ⟶ E.A) (hgE'' : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E'' gE'')
        (gA'' : A''.A ⟶ A.A) (hgA'' : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A'' gA'')
        (ψ : E''.A ⟶ A''.A) (ψ' : A''.A ⟶ E''.A) (hψ : ψ ≫ A''.f = E''.f)
        (hq : FakeEllipticCurve.IsIsogenyPair (r ^ d) E'' A'' ψ ψ') (hm : FakeEllipticCurve.PreservesLevel E'' A'' ψ hψ)
        (iE : E'.A ≅ E''.A) (hiE : iE.hom ≫ E''.f = E'.f) (iA : A'.A ≅ A''.A) (hiA : iA.hom ≫ A''.f = A'.f),
        FakeEllipticCurve.IsoVia E' E'' iE hiE → FakeEllipticCurve.IsoVia A' A'' iA hiA →
        iE.hom ≫ gE'' = gE → iA.hom ≫ gA'' = gA → iE.hom ≫ ψ = φ ≫ iA.hom →
          pt T E' A' gE hgE gA hgA φ φ' hφ hp hl = pt T E'' A'' gE'' hgE'' gA'' hgA'' ψ ψ' hψ hq hm)

    (hX2 : ∀ (T T' : Type) [CommRing T] [Algebra S T] [CommRing T'] [Algebra S T'] (f : T →ₐ[S] T')
        (E' A' : FakeEllipticCurve Λ N T) (gE : E'.A ⟶ E.A) (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
        (gA : A'.A ⟶ A.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA)
        (φ : E'.A ⟶ A'.A) (φ' : A'.A ⟶ E'.A) (hφ : φ ≫ A'.f = E'.f)
        (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ φ') (hl : FakeEllipticCurve.PreservesLevel E' A' φ hφ)
        (E'' A'' : FakeEllipticCurve Λ N T') (hE : E''.A ⟶ E'.A) (hhE : FakeEllipticCurve.IsPullbackVia (f : T →+* T') E' E'' hE)
        (hA : A''.A ⟶ A'.A) (hhA : FakeEllipticCurve.IsPullbackVia (f : T →+* T') A' A'' hA)
        (hgE'' : FakeEllipticCurve.IsPullbackVia (algebraMap S T') E E'' (hE ≫ gE))
        (hgA'' : FakeEllipticCurve.IsPullbackVia (algebraMap S T') A A'' (hA ≫ gA))
        (ψ : E''.A ⟶ A''.A) (ψ' : A''.A ⟶ E''.A) (hψ : ψ ≫ A''.f = E''.f)
        (hq : FakeEllipticCurve.IsIsogenyPair (r ^ d) E'' A'' ψ ψ') (hm : FakeEllipticCurve.PreservesLevel E'' A'' ψ hψ),
        ψ ≫ hA = hE ≫ φ → ψ' ≫ hE = hA ≫ φ' →
          (pt T' E'' A'' (hE ≫ gE) hgE'' (hA ≫ gA) hgA'' ψ ψ' hψ hq hm).1 =
            Spec.map (CommRingCat.ofHom (f : T →+* T')) ≫ (pt T E' A' gE hgE gA hgA φ φ' hφ hp hl).1)

    (hX3 : ∀ (T : Type) [CommRing T] [Algebra S T]
        (E' A' : FakeEllipticCurve Λ N T) (gE : E'.A ⟶ E.A) (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
        (gA : A'.A ⟶ A.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA)
        (z : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap S T))) ξ),
        ∃ (φ : E'.A ⟶ A'.A) (φ' : A'.A ⟶ E'.A) (hφ : φ ≫ A'.f = E'.f)
          (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ φ') (hl : FakeEllipticCurve.PreservesLevel E' A' φ hφ),
          pt T E' A' gE hgE gA hgA φ φ' hφ hp hl = z)

    (hX3' : ∀ (T : Type) [CommRing T] [Algebra S T]
        (E' A' : FakeEllipticCurve Λ N T) (gE : E'.A ⟶ E.A) (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
        (gA : A'.A ⟶ A.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA)
        (φ₁ : E'.A ⟶ A'.A) (φ₁' : A'.A ⟶ E'.A) (hφ₁ : φ₁ ≫ A'.f = E'.f)
        (hp₁ : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ₁ φ₁') (hl₁ : FakeEllipticCurve.PreservesLevel E' A' φ₁ hφ₁)
        (φ₂ : E'.A ⟶ A'.A) (φ₂' : A'.A ⟶ E'.A) (hφ₂ : φ₂ ≫ A'.f = E'.f)
        (hp₂ : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ₂ φ₂') (hl₂ : FakeEllipticCurve.PreservesLevel E' A' φ₂ hφ₂),
        pt T E' A' gE hgE gA hgA φ₁ φ₁' hφ₁ hp₁ hl₁ = pt T E' A' gE hgE gA hgA φ₂ φ₂' hφ₂ hp₂ hl₂ → φ₁ = φ₂ ∧ φ₁' = φ₂') :
    FormallyUnramified ξ := by
  classical
  have h1Λ : (1 : ℍ[ℚ, a, b]) ∈ Λ := by simpa using hΛℤ 1
  have hone : (⟨(((r ^ 0 : ℕ) : ℤ) : ℚ), hΛℤ _⟩ : ↥Λ) = ⟨1, h1Λ⟩ := Subtype.ext (by push_cast; simp)
  apply AlgebraicGeometry.formallyUnramified_of_forall_lift_unique_of_isArtinianRing ξ
  intro T' T _ _ _ _ _ _ p hp hpm s m hm m₁ m₂ h₁s h₁m h₂s h₂m

  obtain ⟨σ', hσ'⟩ : ∃ σ' : CommRingCat.of S ⟶ CommRingCat.of T', Spec.map σ' = s := ⟨_, Spec.map_preimage _⟩
  letI algST' : Algebra S T' := σ'.hom.toAlgebra
  letI algST : Algebra S T := (p.comp (algebraMap S T')).toAlgebra
  have hs : Spec.map (CommRingCat.ofHom (algebraMap S T')) = s := by
    rw [show algebraMap S T' = σ'.hom from rfl, CommRingCat.ofHom_hom]; exact hσ'
  let pa : T' →ₐ[S] T := ⟨p, fun _ => rfl⟩
  have hpa : (pa : T' →+* T) = p := rfl

  have hkle : RingHom.ker p ≤ IsLocalRing.maximalIdeal T' := IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top p)
  have hnil : ∃ n : ℕ, RingHom.ker p ^ n = ⊥ :=
    ⟨2, le_bot_iff.1 (by rw [pow_two, ← hpm]; exact Ideal.mul_mono_right hkle)⟩

  obtain ⟨E', gE, hgEsq, hgEmul, hgEact, hgElev, -⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_levelIff (algebraMap S T') E
  have hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T') E E' gE := ⟨hgEsq, hgEmul, hgEact, hgElev⟩
  obtain ⟨A', gA, hgAsq, hgAmul, hgAact, hgAlev, -⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_levelIff (algebraMap S T') A
  have hgA : FakeEllipticCurve.IsPullbackVia (algebraMap S T') A A' gA := ⟨hgAsq, hgAmul, hgAact, hgAlev⟩
  obtain ⟨E'', hE, hhEsq, hhEmul, hhEact, hhElev, -⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_levelIff p E'
  have hhE : FakeEllipticCurve.IsPullbackVia p E' E'' hE := ⟨hhEsq, hhEmul, hhEact, hhElev⟩
  obtain ⟨A'', hA, hhAsq, hhAmul, hhAact, hhAlev, -⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_levelIff p A'
  have hhA : FakeEllipticCurve.IsPullbackVia p A' A'' hA := ⟨hhAsq, hhAmul, hhAact, hhAlev⟩
  have hgE'' : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E'' (hE ≫ gE) :=
    CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia.comp (algebraMap S T') p E E' E'' gE hE hgE hhE
  have hgA'' : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A'' (hA ≫ gA) :=
    CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia.comp (algebraMap S T') p A A' A'' gA hA hgA hhA

  have h₁s' : m₁ ≫ ξ = Spec.map (CommRingCat.ofHom (algebraMap S T')) := by rw [hs]; exact h₁s
  have h₂s' : m₂ ≫ ξ = Spec.map (CommRingCat.ofHom (algebraMap S T')) := by rw [hs]; exact h₂s
  obtain ⟨φ₁, φ₁', hφ₁, hp₁, hl₁, e₁⟩ := hX3 T' E' A' gE hgE gA hgA ⟨m₁, h₁s'⟩
  obtain ⟨φ₂, φ₂', hφ₂, hp₂, hl₂, e₂⟩ := hX3 T' E' A' gE hgE gA hgA ⟨m₂, h₂s'⟩

  obtain ⟨ψ₁, ψ₁', hψ₁, hq₁, hm₁, c₁, c₁'⟩ := exists_pullPair p (r ^ d) E' A' E'' A'' hE hhE hA hhA φ₁ φ₁' hφ₁ hp₁ hl₁
  obtain ⟨ψ₂, ψ₂', hψ₂, hq₂, hm₂, c₂, c₂'⟩ := exists_pullPair p (r ^ d) E' A' E'' A'' hE hhE hA hhA φ₂ φ₂' hφ₂ hp₂ hl₂

  have f₁ := hX2 T' T pa E' A' gE hgE gA hgA φ₁ φ₁' hφ₁ hp₁ hl₁ E'' A'' hE hhE hA hhA hgE'' hgA'' ψ₁ ψ₁' hψ₁ hq₁ hm₁ c₁ c₁'
  have f₂ := hX2 T' T pa E' A' gE hgE gA hgA φ₂ φ₂' hφ₂ hp₂ hl₂ E'' A'' hE hhE hA hhA hgE'' hgA'' ψ₂ ψ₂' hψ₂ hq₂ hm₂ c₂ c₂'
  have f₁₂ : pt T E'' A'' (hE ≫ gE) hgE'' (hA ≫ gA) hgA'' ψ₁ ψ₁' hψ₁ hq₁ hm₁ =
      pt T E'' A'' (hE ≫ gE) hgE'' (hA ≫ gA) hgA'' ψ₂ ψ₂' hψ₂ hq₂ hm₂ := by
    apply Subtype.ext
    rw [f₁, f₂, hpa, e₁, e₂]
    change Spec.map (CommRingCat.ofHom p) ≫ m₁ = Spec.map (CommRingCat.ofHom p) ≫ m₂
    rw [h₁m, h₂m]

  obtain ⟨hψ₁₂, hψ₁₂'⟩ := hX3' T E'' A'' (hE ≫ gE) hgE'' (hA ≫ gA) hgA'' ψ₁ ψ₁' hψ₁ hq₁ hm₁ ψ₂ ψ₂' hψ₂ hq₂ hm₂ f₁₂

  have hactA : A'.act ⟨(((r ^ 0 : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = 𝟙 A'.A := by rw [hone]; exact A'.act_one h1Λ
  have hactE : E'.act ⟨(((r ^ 0 : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = 𝟙 E'.A := by rw [hone]; exact E'.act_one h1Λ
  have hφ₁₂ : φ₁ = φ₂ := by
    have key := CerednikDrinfeld.QM.FakeEllipticCurve.comp_act_eq_comp_act_of_isPullbackVia_of_isIsogenyPair_of_ker_pow_eq_bot
      hΛℤ r T' T p hp hnil E' E'' A' hE hhE d d φ₁ φ₂ φ₁' φ₂' hp₁ hp₂ 0 0
      (by rw [hactA, Category.comp_id, Category.comp_id, ← c₁, ← c₂, hψ₁₂])
    rwa [hactA, Category.comp_id, Category.comp_id] at key
  have hφ₁₂' : φ₁' = φ₂' := by
    have key := CerednikDrinfeld.QM.FakeEllipticCurve.comp_act_eq_comp_act_of_isPullbackVia_of_isIsogenyPair_of_ker_pow_eq_bot
      hΛℤ r T' T p hp hnil A' A'' E' hA hhA d d φ₁' φ₂' φ₁ φ₂
      (isIsogenyPair_symm _ _ _ _ _ hp₁) (isIsogenyPair_symm _ _ _ _ _ hp₂) 0 0
      (by rw [hactE, Category.comp_id, Category.comp_id, ← c₁', ← c₂', hψ₁₂'])
    rwa [hactE, Category.comp_id, Category.comp_id] at key
  subst hφ₁₂ hφ₁₂'
  have := (congrArg Subtype.val e₁).symm.trans (congrArg Subtype.val e₂)
  exact this

end S_CerednikDrinfeld_QM_FakeEllipticCurve_formallyUnramified_of_represents_isIsogenyPair_preservesLevel
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_formallyUnramified_of_represents_isIsogenyPair_preservesLevel (solution)
