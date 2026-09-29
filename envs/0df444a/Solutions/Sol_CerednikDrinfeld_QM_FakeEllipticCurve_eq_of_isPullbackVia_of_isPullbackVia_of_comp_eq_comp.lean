-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.eq_of_isPullbackVia_of_isPullbackVia_of_comp_eq_comp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/59d6ed68-b3b1-5c78-8c66-739fa09f399c

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_eq_of_comp_eq_of_isPullback_of_isArtinianRing
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral
import Theorems.Thm_AlgebraicGeometry_GeometricallyIrreducible_geometricallyConnected
import Theorems.Thm_AlgebraicGeometry_bijective_appTop_of_universallyClosed_of_geometricallyReduced_of_geometricallyConnected
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_eq_of_isPullbackVia_of_isPullbackVia_of_comp_eq_comp
p2m_attr_erase "instance" "AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open scoped Quaternion
open IsLocalRing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

noncomputable section

namespace RigidPB

theorem bijective_appTop_of_abelianSchemePropertyBundle {k : Type} [Field k] {A : Scheme.{0}}
    {f : A ⟶ Spec (CommRingCat.of k)} (hA : AbelianSchemePropertyBundle k f) : Function.Bijective f.appTop := by
  haveI : IsProper f := hA.proper
  haveI : GeometricallyIntegral f := AbelianSchemePropertyBundle.geometricallyIntegral hA
  haveI : GeometricallyConnected f := GeometricallyIrreducible.geometricallyConnected f
  exact bijective_appTop_of_universallyClosed_of_geometricallyReduced_of_geometricallyConnected f

theorem one_comp_eq_one_of_hom {R : Type} [CommRing R] {A A' : Scheme.{0}}
    {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (L' : RelativeGroupLaw R f')
    (e : A ⟶ A') (he : e ≫ f' = f)
    (hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      mapPt e he (L.mul t P Q) = L'.mul t (mapPt e he P) (mapPt e he Q)) :
    (L.one (𝟙 _)).1 ≫ e = (L'.one (𝟙 _)).1 := by
  set y : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f' := mapPt e he (L.one (𝟙 _)) with hy
  have hyy : L'.mul (𝟙 _) y y = y := by
    rw [hy, ← hom, L.one_mul]
  have hone : y = L'.one (𝟙 _) := by
    calc y = L'.mul (𝟙 _) (L'.mul (𝟙 _) y y) (L'.inv (𝟙 _) y) := by rw [L'.mul_assoc, L'.mul_inv_cancel, L'.mul_one]
      _ = L'.mul (𝟙 _) y (L'.inv (𝟙 _) y) := by rw [hyy]
      _ = L'.one (𝟙 _) := L'.mul_inv_cancel _ _
  have := congrArg Subtype.val hone
  rw [hy, mapPt_coe] at this
  exact this

end RigidPB

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (kbar : Type) [Field kbar]
    (B : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B]
    (ρ : B →+* kbar) (hρ : Function.Surjective ρ) (hρker : RingHom.ker ρ = maximalIdeal B)
    (E₀ : FakeEllipticCurve Λ N kbar) (E' : FakeEllipticCurve Λ N B)
    (g' : E₀.A ⟶ E'.A) (hg' : FakeEllipticCurve.IsPullbackVia ρ E' E₀ g')
    (S : Type) [CommRing S] (E : FakeEllipticCurve Λ N S) (φ : S →+* B)
    (h h' : E'.A ⟶ E.A)
    (hh : FakeEllipticCurve.IsPullbackVia φ E E' h) (hh' : FakeEllipticCurve.IsPullbackVia φ E E' h')
    (hcomp : g' ≫ h = g' ≫ h') :
    h = h' := by
  obtain ⟨sq, hmul, -, -⟩ := hh
  obtain ⟨sq', hmul', -, -⟩ := hh'
  obtain ⟨sq₀, -, -, -⟩ := hg'

  set α : E'.A ⟶ E'.A := sq'.lift h E'.f sq.w with hαdef
  have hα₁ : α ≫ h' = h := sq'.lift_fst _ _ _
  have hα₂ : α ≫ E'.f = E'.f := sq'.lift_snd _ _ _
  suffices hα : α = 𝟙 _ by
    rw [← hα₁, hα, Category.id_comp]

  have hgα : g' ≫ α = g' ≫ 𝟙 _ := by
    apply sq'.hom_ext
    · rw [Category.assoc, hα₁, hcomp, Category.assoc, Category.id_comp]
    · rw [Category.assoc, hα₂, Category.assoc, Category.id_comp]

  have hαhom : ∀ {T : Scheme.{0}} (t'' : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t'' E'.f),
      mapPt α hα₂ (E'.L.mul t'' P Q) = E'.L.mul t'' (mapPt α hα₂ P) (mapPt α hα₂ Q) := by
    intro T t'' P Q
    apply Subtype.ext
    apply sq'.hom_ext
    ·
      rw [mapPt_coe, Category.assoc, hα₁, hmul t'' P Q, hmul' t'' (mapPt α hα₂ P) (mapPt α hα₂ Q)]
      congr 2 <;> apply Subtype.ext <;> simp [mapPt_coe, Category.assoc, hα₁]
    · rw [mapPt_coe, Category.assoc, hα₂, (E'.L.mul t'' P Q).2, (E'.L.mul t'' (mapPt α hα₂ P) (mapPt α hα₂ Q)).2]
  have hid : ∀ {T : Scheme.{0}} (t'' : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t'' E'.f),
      mapPt (𝟙 E'.A) (Category.id_comp _) (E'.L.mul t'' P Q) =
        E'.L.mul t'' (mapPt (𝟙 E'.A) (Category.id_comp _) P) (mapPt (𝟙 E'.A) (Category.id_comp _) Q) := by
    intro T t'' P Q
    have hP : ∀ P : SchemeHomOver t'' E'.f, mapPt (𝟙 E'.A) (Category.id_comp _) P = P := fun P =>
      Subtype.ext (by rw [mapPt_coe, Category.comp_id])
    rw [hP, hP, hP]

  have hs₁ := RigidPB.one_comp_eq_one_of_hom E'.L E'.L α hα₂ hαhom
  have hs₂ := RigidPB.one_comp_eq_one_of_hom E'.L E'.L (𝟙 _) (Category.id_comp _) hid
  haveI : IsProper E'.f := E'.bundle.proper
  haveI : Smooth E'.f := E'.bundle.smooth
  exact GoodReductionJacobian.RelativeGroupLaw.eq_of_comp_eq_of_isPullback_of_isArtinianRing
    ρ hρ E'.L (RigidPB.bijective_appTop_of_abelianSchemePropertyBundle E₀.bundle) g' sq₀
    (E'.L.one (𝟙 _)).1 (E'.L.one (𝟙 _)).2 α (𝟙 _) hα₂ (Category.id_comp _) hgα (hs₁.trans hs₂.symm)

#print axioms solution

end

end S_CerednikDrinfeld_QM_FakeEllipticCurve_eq_of_isPullbackVia_of_isPullbackVia_of_comp_eq_comp
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_eq_of_isPullbackVia_of_isPullbackVia_of_comp_eq_comp (solution)
