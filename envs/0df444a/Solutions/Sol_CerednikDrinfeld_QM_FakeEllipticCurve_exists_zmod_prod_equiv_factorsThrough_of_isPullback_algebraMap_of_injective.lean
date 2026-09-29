-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_zmod_prod_equiv_factorsThrough_of_isPullback_algebraMap_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/4978be94-4440-53f4-a409-8d3066b57023

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_zmod_prod_equiv_factorsThrough_of_isPullback_algebraMap_of_injective

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

namespace LevelFibreGenericPt

section Transport

variable {K Ω : Type u} [CommRing K] [CommRing Ω] (ι : K →+* Ω)
  {A : Scheme.{u}} {fA : A ⟶ Spec (CommRingCat.of Ω)} (LA : RelativeGroupLaw Ω fA)
  {A₀ : Scheme.{u}} {f₀ : A₀ ⟶ Spec (CommRingCat.of K)} (L₀ : RelativeGroupLaw K f₀)
  (g : A ⟶ A₀) (hg : IsPullback g fA f₀ (Spec.map (CommRingCat.ofHom ι)))

def rebase (f : A₀ ⟶ Spec (CommRingCat.of K)) {T : Scheme.{u}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of K)} (h : t₁ = t₂)
    (P : SchemeHomOver t₁ f) : SchemeHomOver t₂ f := ⟨P.1, P.2.trans h⟩

theorem rebase_mul {T : Scheme.{u}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of K)} (h : t₁ = t₂)
    (P Q : SchemeHomOver t₁ f₀) : rebase f₀ h (L₀.mul t₁ P Q) = L₀.mul t₂ (rebase f₀ h P) (rebase f₀ h Q) := by
  subst h; rfl

def push {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of Ω)} {t₀ : T ⟶ Spec (CommRingCat.of K)}
    (ht : t' ≫ Spec.map (CommRingCat.ofHom ι) = t₀) (Q : SchemeHomOver t' fA) : SchemeHomOver t₀ f₀ :=
  ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2, ht]⟩

@[scoped simp] theorem push_coe {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of Ω)} {t₀ : T ⟶ Spec (CommRingCat.of K)}
    (ht : t' ≫ Spec.map (CommRingCat.ofHom ι) = t₀) (Q : SchemeHomOver t' fA) : (push ι g hg ht Q).1 = Q.1 ≫ g := rfl

private noncomputable def _root_.LevelFibreGenericPt.lift {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of Ω)} {t₀ : T ⟶ Spec (CommRingCat.of K)}
    (ht : t' ≫ Spec.map (CommRingCat.ofHom ι) = t₀) (P : SchemeHomOver t₀ f₀) : SchemeHomOver t' fA :=
  ⟨hg.lift P.1 t' (by rw [P.2, ht]), hg.lift_snd _ _ _⟩

p2m_export "LevelFibreGenericPt" "lift"
theorem lift_coe_g {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of Ω)} {t₀ : T ⟶ Spec (CommRingCat.of K)}
    (ht : t' ≫ Spec.map (CommRingCat.ofHom ι) = t₀) (P : SchemeHomOver t₀ f₀) : (lift ι g hg ht P).1 ≫ g = P.1 :=
  hg.lift_fst _ _ _

theorem push_lift {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of Ω)} {t₀ : T ⟶ Spec (CommRingCat.of K)}
    (ht : t' ≫ Spec.map (CommRingCat.ofHom ι) = t₀) (P : SchemeHomOver t₀ f₀) :
    push ι g hg ht (lift ι g hg ht P) = P :=
  Subtype.ext (lift_coe_g ι g hg ht P)

theorem lift_push {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of Ω)} {t₀ : T ⟶ Spec (CommRingCat.of K)}
    (ht : t' ≫ Spec.map (CommRingCat.ofHom ι) = t₀) (Q : SchemeHomOver t' fA) :
    lift ι g hg ht (push ι g hg ht Q) = Q := by
  apply Subtype.ext
  apply hg.hom_ext
  · rw [lift_coe_g]; rfl
  · rw [(lift ι g hg ht (push ι g hg ht Q)).2, Q.2]

variable
  (hg_mul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of Ω)) (P Q : SchemeHomOver t' fA),
      (LA.mul t' P Q).1 ≫ g =
        (L₀.mul (t' ≫ Spec.map (CommRingCat.ofHom ι))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)

include hg_mul in
theorem push_mul {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of Ω)} {t₀ : T ⟶ Spec (CommRingCat.of K)}
    (ht : t' ≫ Spec.map (CommRingCat.ofHom ι) = t₀) (P Q : SchemeHomOver t' fA) :
    push ι g hg ht (LA.mul t' P Q) = L₀.mul t₀ (push ι g hg ht P) (push ι g hg ht Q) := by
  apply Subtype.ext
  change (LA.mul t' P Q).1 ≫ g = _
  rw [hg_mul]
  exact congrArg Subtype.val (rebase_mul L₀ ht _ _)

end Transport

theorem geomPoint_comp {K Ω : Type u} [CommRing K] [CommRing Ω] (ι : K →+* Ω) (k : Type u) [Field k] (s : Ω →+* k) :
    geomPoint k s ≫ Spec.map (CommRingCat.ofHom ι) = geomPoint k (s.comp ι) := by
  rw [geomPoint, geomPoint, ← Spec.map_comp]; rfl

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

theorem main
    {R K : Type u} [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (E₀ : FakeEllipticCurve Λ N K)
    {𝒜 : Scheme.{u}} {f : 𝒜 ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {C : Scheme.{u}} (lev : C ⟶ 𝒜)
    (g : E₀.A ⟶ 𝒜) (hg : CategoryTheory.IsPullback g E₀.f f (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hg_mul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t' E₀.f),
      (E₀.L.mul t' x y).1 ≫ g =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)))
          ⟨x.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, y.2]⟩).1)
    (hg_lev : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of K)) (P : SchemeHomOver t' E₀.f),
      FactorsThrough E₀.lev P ↔ ∃ P₀ : T ⟶ C, P₀ ≫ lev = P.1 ≫ g) :
    ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : R →+* k), Function.Injective sk → (N : k) ≠ 0 →
      ∃ e : ZMod N × ZMod N ≃ {P : SchemeHomOver (geomPoint k sk) f // FactorsThrough lev P},
        ∀ x y : ZMod N × ZMod N,
          (e (x + y) : SchemeHomOver (geomPoint k sk) f) = L.mul (geomPoint k sk) (e x) (e y) := by
  intro k _ _ sk hsk hN
  haveI : Nontrivial R := ⟨⟨0, 1, fun h => zero_ne_one (α := k) (by rw [← map_zero sk, ← map_one sk, h])⟩⟩
  have hunit : ∀ y : ↥(nonZeroDivisors R), IsUnit (sk y) := by
    intro y
    have hy0 : (y : R) ≠ 0 := nonZeroDivisors.coe_ne_zero y
    exact IsUnit.mk0 _ (fun h => hy0 (hsk (by rw [h, map_zero])))
  let s : K →+* k := IsLocalization.lift (M := nonZeroDivisors R) (S := K) hunit
  have hs : s.comp (algebraMap R K) = sk := RingHom.ext fun r => IsLocalization.lift_eq hunit r
  have hgp : geomPoint k s ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)) = geomPoint k sk := by
    rw [geomPoint_comp, hs]
  obtain ⟨e₀, he₀⟩ := E₀.lev_fibre k s hN
  let Φ : {P : SchemeHomOver (geomPoint k s) E₀.f // FactorsThrough E₀.lev P} ≃
      {P : SchemeHomOver (geomPoint k sk) f // FactorsThrough lev P} :=
    { toFun := fun P => ⟨push (algebraMap R K) g hg hgp P.1, (hg_lev _ P.1).mp P.2⟩
      invFun := fun Q => ⟨lift (algebraMap R K) g hg hgp Q.1,
        (hg_lev _ _).mpr (by rw [lift_coe_g]; exact Q.2)⟩
      left_inv := fun P => Subtype.ext (lift_push (algebraMap R K) g hg hgp P.1)
      right_inv := fun Q => Subtype.ext (push_lift (algebraMap R K) g hg hgp Q.1) }
  refine ⟨e₀.trans Φ, fun x y => ?_⟩
  change push (algebraMap R K) g hg hgp (e₀ (x + y)).1 =
    L.mul (geomPoint k sk) (push (algebraMap R K) g hg hgp (e₀ x).1) (push (algebraMap R K) g hg hgp (e₀ y).1)
  rw [he₀, push_mul (algebraMap R K) E₀.L L g hg hg_mul hgp]

end LevelFibreGenericPt
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_zmod_prod_equiv_factorsThrough_of_isPullback_algebraMap_of_injective.LevelFibreGenericPt"

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {R K : Type u} [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (E₀ : FakeEllipticCurve Λ N K)
    {𝒜 : Scheme.{u}} {f : 𝒜 ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {C : Scheme.{u}} (lev : C ⟶ 𝒜)
    (g : E₀.A ⟶ 𝒜) (hg : CategoryTheory.IsPullback g E₀.f f (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hg_mul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t' E₀.f),
      (E₀.L.mul t' x y).1 ≫ g =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)))
          ⟨x.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, y.2]⟩).1)
    (hg_lev : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of K)) (P : SchemeHomOver t' E₀.f),
      FactorsThrough E₀.lev P ↔ ∃ P₀ : T ⟶ C, P₀ ≫ lev = P.1 ≫ g) :
    ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : R →+* k), Function.Injective sk → (N : k) ≠ 0 →
      ∃ e : ZMod N × ZMod N ≃ {P : SchemeHomOver (geomPoint k sk) f // FactorsThrough lev P},
        ∀ x y : ZMod N × ZMod N,
          (e (x + y) : SchemeHomOver (geomPoint k sk) f) = L.mul (geomPoint k sk) (e x) (e y) := by
  exact LevelFibreGenericPt.main E₀ L lev g hg hg_mul hg_lev

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_zmod_prod_equiv_factorsThrough_of_isPullback_algebraMap_of_injective
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_zmod_prod_equiv_factorsThrough_of_isPullback_algebraMap_of_injective (solution)
