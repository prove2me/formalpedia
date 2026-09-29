-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.iso_of_isTwist_of_isTwist_of_sub_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/2b6a2e2c-e8c0-5fdc-8142-6ecc7ce8df45

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_iso_of_isTwist_of_isTwist_of_sub_eq_smul

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra CerednikDrinfeld.QM

namespace Law3TC

variable {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem eq_one_of_mul_self (L : GoodReductionJacobian.RelativeGroupLaw R f) {T : Scheme.{0}}
    (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) (h : L.mul t x x = x) : x = L.one t := by
  have := congrArg (fun z => L.mul t (L.inv t x) z) h
  rw [← L.mul_assoc, L.inv_mul_cancel, L.one_mul] at this
  exact this

theorem pushPt_one (L : GoodReductionJacobian.RelativeGroupLaw R f) (φ : A ⟶ A) (hφ : φ ≫ f = f)
    (hhom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      pushPt φ hφ (L.mul t P Q) = L.mul t (pushPt φ hφ P) (pushPt φ hφ Q))
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) : pushPt φ hφ (L.one t) = L.one t := by
  apply eq_one_of_mul_self
  rw [← hhom, L.one_mul]

theorem pushPt_nsmulPt (L : GoodReductionJacobian.RelativeGroupLaw R f) (φ : A ⟶ A) (hφ : φ ≫ f = f)
    (hhom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      pushPt φ hφ (L.mul t P Q) = L.mul t (pushPt φ hφ P) (pushPt φ hφ Q))
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f) (n : ℕ) :
    pushPt φ hφ (nsmulPt L t n P) = nsmulPt L t n (pushPt φ hφ P) := by
  induction n with
  | zero => exact pushPt_one L φ hφ hhom t
  | succ n ih => show pushPt φ hφ (L.mul t (nsmulPt L t n P) P) = L.mul t (nsmulPt L t n (pushPt φ hφ P)) (pushPt φ hφ P)
                 rw [hhom, ih]

theorem mapPt_mapPt {A₁ A₂ A₃ : Scheme.{0}} {f₁ : A₁ ⟶ Spec (CommRingCat.of R)} {f₂ : A₂ ⟶ Spec (CommRingCat.of R)}
    {f₃ : A₃ ⟶ Spec (CommRingCat.of R)} (φ : A₁ ⟶ A₂) (hφ : φ ≫ f₂ = f₁) (ψ : A₂ ⟶ A₃) (hψ : ψ ≫ f₃ = f₂)
    {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f₁)
    (χ : A₁ ⟶ A₃) (hχ : χ ≫ f₃ = f₁) (hcomp : φ ≫ ψ = χ) :
    mapPt ψ hψ (mapPt φ hφ P) = mapPt χ hχ P := by
  apply Subtype.ext; simp only [mapPt_coe, Category.assoc, hcomp]

theorem mapPt_id_of_comp {A₁ A₂ : Scheme.{0}} {f₁ : A₁ ⟶ Spec (CommRingCat.of R)} {f₂ : A₂ ⟶ Spec (CommRingCat.of R)}
    (φ : A₁ ⟶ A₂) (hφ : φ ≫ f₂ = f₁) (ψ : A₂ ⟶ A₁) (hψ : ψ ≫ f₁ = f₂)
    {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f₁) (hcomp : φ ≫ ψ = 𝟙 A₁) :
    mapPt ψ hψ (mapPt φ hφ P) = P := by
  apply Subtype.ext; simp only [mapPt_coe, Category.assoc, hcomp, Category.comp_id]

end Law3TC

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) {N m : ℕ} {S : Type} [CommRing S]
    (u u' u'' : FakeEllipticCurve.WithFullLevel Λ N m S) (c c' : ↥Λ)
    (h' : FakeEllipticCurve.WithFullLevel.IsTwist c u u') (h'' : FakeEllipticCurve.WithFullLevel.IsTwist c' u u'')
    (hcc' : ∃ y : ↥Λ, (c : ℍ[ℚ, a, b]) - (c' : ℍ[ℚ, a, b]) = (m : ℚ) • (y : ℍ[ℚ, a, b])) :
    FakeEllipticCurve.WithFullLevel.Iso u' u'' := by
  obtain ⟨e', he', hmul', hact', hlev', hP'⟩ := h'
  obtain ⟨e'', he'', hmul'', hact'', hlev'', hP''⟩ := h''
  obtain ⟨y, hy⟩ := hcc'

  have hT : pushPt (u.1.act c) (u.1.act_over c) u.2.P = pushPt (u.1.act c') (u.1.act_over c') u.2.P := by
    set t := 𝟙 (Spec (CommRingCat.of S)) with ht
    have hc : c = c' + m • y := by
      apply Subtype.ext
      rw [Submodule.coe_add, Submodule.coe_smul_of_tower, ← Nat.cast_smul_eq_nsmul ℚ, ← hy]
      abel

    have hA : ∀ n : ℕ, pushPt (u.1.act (n • y)) (u.1.act_over (n • y)) u.2.P =
        nsmulPt u.1.L t n (pushPt (u.1.act y) (u.1.act_over y) u.2.P) := by
      intro n
      induction n with
      | zero =>
        show pushPt (u.1.act (0 • y)) (u.1.act_over (0 • y)) u.2.P = u.1.L.one t
        apply Law3TC.eq_one_of_mul_self
        have := u.1.act_add (0 • y) (0 • y) t u.2.P
        rw [show (0 • y + 0 • y : ↥Λ) = 0 • y by rw [zero_smul, add_zero]] at this
        exact this.symm
      | succ n ih =>
        have := u.1.act_add (n • y) y t u.2.P
        rw [show (n • y + y : ↥Λ) = (n + 1) • y by rw [succ_nsmul]] at this
        rw [this, ih]; rfl
    rw [hc, u.1.act_add c' (m • y) t u.2.P, hA m, ← Law3TC.pushPt_nsmulPt u.1.L _ _ (u.1.act_hom y), u.2.torsion,
      Law3TC.pushPt_one u.1.L _ _ (u.1.act_hom y), u.1.L.mul_one]

  have h₀ : e'.inv ≫ u.1.f = u'.1.f := by rw [Iso.inv_comp_eq, he']
  have hE : (e'.symm ≪≫ e'').hom ≫ u''.1.f = u'.1.f := by
    show (e'.inv ≫ e''.hom) ≫ u''.1.f = u'.1.f
    rw [Category.assoc, he'', h₀]
  have hEhom : (e'.symm ≪≫ e'').hom = e'.inv ≫ e''.hom := rfl

  have back : ∀ {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t u'.1.f),
      mapPt e'.hom he' (mapPt e'.inv h₀ P) = P := fun P => Law3TC.mapPt_id_of_comp _ _ _ _ P e'.inv_hom_id
  have fwd : ∀ {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t u'.1.f),
      mapPt (e'.symm ≪≫ e'').hom hE P = mapPt e''.hom he'' (mapPt e'.inv h₀ P) := fun P =>
    (Law3TC.mapPt_mapPt e'.inv h₀ e''.hom he'' P _ hE hEhom.symm).symm
  have fwd' : ∀ {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (P₀ : SchemeHomOver t u.1.f),
      mapPt (e'.symm ≪≫ e'').hom hE (mapPt e'.hom he' P₀) = mapPt e''.hom he'' P₀ := fun P₀ =>
    Law3TC.mapPt_mapPt e'.hom he' _ hE P₀ e''.hom he'' (by rw [hEhom, ← Category.assoc, e'.hom_inv_id, Category.id_comp])
  refine ⟨e'.symm ≪≫ e'', hE, ?_, ?_, ?_, ?_⟩
  · intro T t P Q
    rw [← back P, ← back Q, ← hmul', fwd', fwd', fwd', hmul'']
  · intro x
    rw [hEhom]
    have h1 : u'.1.act x ≫ e'.inv = e'.inv ≫ u.1.act x := by
      rw [Iso.eq_inv_comp, ← Category.assoc, ← hact' x, Category.assoc, e'.hom_inv_id, Category.comp_id]
    rw [← Category.assoc, h1, Category.assoc, hact'' x, Category.assoc]
  · intro T t P
    rw [← back P, fwd', ← hlev', ← hlev'']
  · rw [← hP', fwd', hT, hP'']

end S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_iso_of_isTwist_of_isTwist_of_sub_eq_smul
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_iso_of_isTwist_of_isTwist_of_sub_eq_smul (solution)
