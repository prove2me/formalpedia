-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.mul_assoc_comm_and_act_identities_of_forall_comp_eq_of_isPushout_of_isPullbackVia
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/0de7b677-038e-5b6b-97bd-33c127006938

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_ModuliPackageDeformation
import Theorems.Thm_AlgebraicGeometry_isPushout_of_flat_of_isPullback_specMap_pullbackFst_pullbackSnd
import Theorems.Thm_AlgebraicGeometry_isPullback_pullbackMap_fst_comp_of_isPullback_of_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_mul_assoc_comm_and_act_identities_of_forall_comp_eq_of_isPushout_of_isPullbackVia

set_option autoImplicit false

open scoped Quaternion
open IsLocalRing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal CerednikDrinfeld.SpecialFormal.ModuliPackage NeronModelInfra GoodReductionJacobian

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

noncomputable section

namespace GlueIdent

section Leg

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
  {R B₁ : Type} [CommRing R] [CommRing B₁] (σ : R →+* B₁)
  {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))
  (E₁ : FakeEllipticCurve Λ N B₁) (k : E₁.A ⟶ X)
  (hk : IsPullback k E₁.f f (Spec.map (CommRingCat.ofHom σ)))
  (m : pullback f f ⟶ X)
  (hmul₁ : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of B₁)) (P Q : SchemeHomOver t' E₁.f),
      (E₁.L.mul t' P Q).1 ≫ k =
        pullback.lift (P.1 ≫ k) (Q.1 ≫ k)
          (by simp only [Category.assoc]; rw [hk.w, ← Category.assoc, P.2, ← Category.assoc, Q.2]) ≫ m)

theorem mul_coe_congr {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of B₁)} (ht : t₁ = t₂)
    {P₁ Q₁ : SchemeHomOver t₁ E₁.f} {P₂ Q₂ : SchemeHomOver t₂ E₁.f} (hP : P₁.1 = P₂.1) (hQ : Q₁.1 = Q₂.1) :
    (E₁.L.mul t₁ P₁ Q₁).1 = (E₁.L.mul t₂ P₂ Q₂).1 := by
  subst ht; rw [Subtype.ext hP, Subtype.ext hQ]

include hmul₁ in

theorem mul_comp_eq {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of B₁)) (P Q : SchemeHomOver t' E₁.f)
    (u : T ⟶ pullback f f) (hu₁ : u ≫ pullback.fst f f = P.1 ≫ k) (hu₂ : u ≫ pullback.snd f f = Q.1 ≫ k) :
    (E₁.L.mul t' P Q).1 ≫ k = u ≫ m := by
  rw [hmul₁ t' P Q]
  congr 1
  apply pullback.hom_ext
  · rw [pullback.lift_fst, hu₁]
  · rw [pullback.lift_snd, hu₂]

def idPt : SchemeHomOver E₁.f E₁.f := ⟨𝟙 _, Category.id_comp _⟩

@[scoped simp] theorem idPt_coe : (idPt E₁).1 = 𝟙 _ := rfl

def p₁ : SchemeHomOver (pullback.fst E₁.f E₁.f ≫ E₁.f) E₁.f := ⟨pullback.fst E₁.f E₁.f, rfl⟩
def p₂ : SchemeHomOver (pullback.fst E₁.f E₁.f ≫ E₁.f) E₁.f := ⟨pullback.snd E₁.f E₁.f, pullback.condition.symm⟩
@[scoped simp] theorem p₁_coe : (p₁ E₁).1 = pullback.fst E₁.f E₁.f := rfl
@[scoped simp] theorem p₂_coe : (p₂ E₁).1 = pullback.snd E₁.f E₁.f := rfl

def q₁ : SchemeHomOver (pullback.fst (pullback.fst E₁.f E₁.f ≫ E₁.f) E₁.f ≫ pullback.fst E₁.f E₁.f ≫ E₁.f) E₁.f :=
  ⟨pullback.fst _ _ ≫ pullback.fst E₁.f E₁.f, by rw [Category.assoc]⟩
def q₂ : SchemeHomOver (pullback.fst (pullback.fst E₁.f E₁.f ≫ E₁.f) E₁.f ≫ pullback.fst E₁.f E₁.f ≫ E₁.f) E₁.f :=
  ⟨pullback.fst _ _ ≫ pullback.snd E₁.f E₁.f, by rw [Category.assoc, ← pullback.condition]⟩
def q₃ : SchemeHomOver (pullback.fst (pullback.fst E₁.f E₁.f ≫ E₁.f) E₁.f ≫ pullback.fst E₁.f E₁.f ≫ E₁.f) E₁.f :=
  ⟨pullback.snd _ _, by rw [← pullback.condition]⟩
@[scoped simp] theorem q₁_coe : (q₁ E₁).1 = pullback.fst _ _ ≫ pullback.fst E₁.f E₁.f := rfl
@[scoped simp] theorem q₂_coe : (q₂ E₁).1 = pullback.fst _ _ ≫ pullback.snd E₁.f E₁.f := rfl
@[scoped simp] theorem q₃_coe : (q₃ E₁).1 = pullback.snd _ _ := rfl

end Leg

end GlueIdent
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_mul_assoc_comm_and_act_identities_of_forall_comp_eq_of_isPushout_of_isPullbackVia.GlueIdent"

open GlueIdent

namespace GlueIdent
section Leg2

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
  {R B₁ : Type} [CommRing R] [CommRing B₁] (σ : R →+* B₁)
  {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))
  (E₁ : FakeEllipticCurve Λ N B₁) (k : E₁.A ⟶ X)
  (hk : IsPullback k E₁.f f (Spec.map (CommRingCat.ofHom σ)))
  (m : pullback f f ⟶ X) (hm : m ≫ f = pullback.fst f f ≫ f)
  (e : Spec (CommRingCat.of R) ⟶ X) (he : e ≫ f = 𝟙 _)
  (ι : X ⟶ X) (hι : ι ≫ f = f) (act : ↥Λ → (X ⟶ X)) (act_over : ∀ x : ↥Λ, act x ≫ f = f)
  (hmul₁ : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of B₁)) (P Q : SchemeHomOver t' E₁.f),
      (E₁.L.mul t' P Q).1 ≫ k =
        pullback.lift (P.1 ≫ k) (Q.1 ≫ k)
          (by simp only [Category.assoc]; rw [hk.w, ← Category.assoc, P.2, ← Category.assoc, Q.2]) ≫ m)
  (hone₁ : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of B₁)),
      (E₁.L.one t').1 ≫ k = (t' ≫ Spec.map (CommRingCat.ofHom σ)) ≫ e)
  (hinv₁ : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of B₁)) (P : SchemeHomOver t' E₁.f),
      (E₁.L.inv t' P).1 ≫ k = (P.1 ≫ k) ≫ ι)
  (hact₁ : ∀ x : ↥Λ, E₁.act x ≫ k = k ≫ act x)
  (K₂ : pullback E₁.f E₁.f ⟶ pullback f f)
  (hK₁ : K₂ ≫ pullback.fst f f = pullback.fst E₁.f E₁.f ≫ k) (hK₂ : K₂ ≫ pullback.snd f f = pullback.snd E₁.f E₁.f ≫ k)
  (K₃ : pullback (pullback.fst E₁.f E₁.f ≫ E₁.f) E₁.f ⟶ pullback (pullback.fst f f ≫ f) f)
  (hK₃₁ : K₃ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ K₂) (hK₃₂ : K₃ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ k)

include hk hm he hι act_over hmul₁ hone₁ hinv₁ hact₁ hK₁ hK₂ hK₃₁ hK₃₂

theorem leg_one_mul : k ≫ (pullback.lift (f ≫ e) (𝟙 X) (by rw [Category.assoc, he, Category.comp_id, Category.id_comp]) ≫ m) = k := by
  have h := mul_comp_eq σ f E₁ k hk m hmul₁ E₁.f (E₁.L.one E₁.f) (idPt E₁)
    (k ≫ pullback.lift (f ≫ e) (𝟙 X) (by rw [Category.assoc, he, Category.comp_id, Category.id_comp]))
    (by rw [Category.assoc, pullback.lift_fst, hone₁, ← Category.assoc, hk.w])
    (by rw [Category.assoc, pullback.lift_snd, idPt_coe, Category.id_comp, Category.comp_id])
  rw [E₁.L.one_mul, idPt_coe, Category.id_comp] at h
  rw [← Category.assoc, ← h]

theorem leg_mul_one : k ≫ (pullback.lift (𝟙 X) (f ≫ e) (by rw [Category.assoc, he, Category.comp_id, Category.id_comp]) ≫ m) = k := by
  have h := mul_comp_eq σ f E₁ k hk m hmul₁ E₁.f (idPt E₁) (E₁.L.one E₁.f)
    (k ≫ pullback.lift (𝟙 X) (f ≫ e) (by rw [Category.assoc, he, Category.comp_id, Category.id_comp]))
    (by rw [Category.assoc, pullback.lift_fst, idPt_coe, Category.id_comp, Category.comp_id])
    (by rw [Category.assoc, pullback.lift_snd, hone₁, ← Category.assoc, hk.w])
  rw [E₁.L.mul_one, idPt_coe, Category.id_comp] at h
  rw [← Category.assoc, ← h]

theorem leg_inv : k ≫ (pullback.lift ι (𝟙 X) (by rw [hι, Category.id_comp]) ≫ m) = k ≫ (f ≫ e) := by
  have h := mul_comp_eq σ f E₁ k hk m hmul₁ E₁.f (E₁.L.inv E₁.f (idPt E₁)) (idPt E₁)
    (k ≫ pullback.lift ι (𝟙 X) (by rw [hι, Category.id_comp]))
    (by rw [Category.assoc, pullback.lift_fst, hinv₁, idPt_coe, Category.id_comp])
    (by rw [Category.assoc, pullback.lift_snd, idPt_coe, Category.id_comp, Category.comp_id])
  rw [E₁.L.inv_mul_cancel, hone₁] at h
  rw [← Category.assoc, ← h, ← Category.assoc, hk.w]

theorem leg_act_one (h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ) : k ≫ act ⟨1, h1⟩ = k ≫ 𝟙 X := by
  rw [← hact₁, E₁.act_one h1, Category.id_comp, Category.comp_id]

theorem leg_act_mul (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ) :
    k ≫ act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = k ≫ (act y ≫ act x) := by
  rw [← hact₁, E₁.act_mul x y h, Category.assoc, hact₁, ← Category.assoc, hact₁, Category.assoc]

theorem leg_act_add (x y : ↥Λ) :
    k ≫ act (x + y) = k ≫ (pullback.lift (act x) (act y) (by rw [act_over, act_over]) ≫ m) := by
  have h := mul_comp_eq σ f E₁ k hk m hmul₁ E₁.f
    (pushPt (E₁.act x) (E₁.act_over x) (idPt E₁)) (pushPt (E₁.act y) (E₁.act_over y) (idPt E₁))
    (k ≫ pullback.lift (act x) (act y) (by rw [act_over, act_over]))
    (by rw [Category.assoc, pullback.lift_fst, ← hact₁]; simp only [pushPt, mapPt_coe, idPt_coe, Category.id_comp])
    (by rw [Category.assoc, pullback.lift_snd, ← hact₁]; simp only [pushPt, mapPt_coe, idPt_coe, Category.id_comp])
  rw [← Category.assoc, ← h, ← hact₁]
  congr 1
  have := congrArg Subtype.val (E₁.act_add x y E₁.f (idPt E₁))
  simp only [pushPt, mapPt_coe, idPt_coe, Category.id_comp] at this
  exact this

theorem K₂_comp_m : K₂ ≫ m = (E₁.L.mul _ (p₁ E₁) (p₂ E₁)).1 ≫ k :=
  (mul_comp_eq σ f E₁ k hk m hmul₁ _ (p₁ E₁) (p₂ E₁) K₂ (by rw [hK₁, p₁_coe]) (by rw [hK₂, p₂_coe])).symm

theorem leg_comm :
    K₂ ≫ (pullback.lift (pullback.snd f f) (pullback.fst f f) pullback.condition.symm ≫ m) = K₂ ≫ m := by
  rw [K₂_comp_m σ f E₁ k hk m hm e he ι hι act act_over hmul₁ hone₁ hinv₁ hact₁ K₂ hK₁ hK₂ K₃ hK₃₁ hK₃₂, RelativeGroupLaw.IsCommutative.mul_comm E₁.comm _ (p₁ E₁) (p₂ E₁)]
  rw [← Category.assoc]
  exact (mul_comp_eq σ f E₁ k hk m hmul₁ _ (p₂ E₁) (p₁ E₁) _
    (by rw [Category.assoc, pullback.lift_fst, hK₂, p₂_coe]) (by rw [Category.assoc, pullback.lift_snd, hK₁, p₁_coe])).symm

theorem leg_act_hom (x : ↥Λ) :
    K₂ ≫ (pullback.lift (pullback.fst f f ≫ act x) (pullback.snd f f ≫ act x)
        (by simp only [Category.assoc, act_over]; exact pullback.condition) ≫ m) =
      K₂ ≫ (m ≫ act x) := by
  have hh := congrArg Subtype.val (E₁.act_hom x _ (p₁ E₁) (p₂ E₁))
  simp only [pushPt, mapPt_coe] at hh

  have h2 := mul_comp_eq σ f E₁ k hk m hmul₁ _
    (pushPt (E₁.act x) (E₁.act_over x) (p₁ E₁)) (pushPt (E₁.act x) (E₁.act_over x) (p₂ E₁))
    (K₂ ≫ pullback.lift (pullback.fst f f ≫ act x) (pullback.snd f f ≫ act x)
        (by simp only [Category.assoc, act_over]; exact pullback.condition))
    (by simp only [Category.assoc, pullback.lift_fst, pushPt, mapPt_coe, p₁_coe]; rw [hact₁, ← Category.assoc, hK₁, Category.assoc])
    (by simp only [Category.assoc, pullback.lift_snd, pushPt, mapPt_coe, p₂_coe]; rw [hact₁, ← Category.assoc, hK₂, Category.assoc])
  calc K₂ ≫ (pullback.lift (pullback.fst f f ≫ act x) (pullback.snd f f ≫ act x)
          (by simp only [Category.assoc, act_over]; exact pullback.condition) ≫ m)
      = (E₁.L.mul _ (pushPt (E₁.act x) (E₁.act_over x) (p₁ E₁)) (pushPt (E₁.act x) (E₁.act_over x) (p₂ E₁))).1 ≫ k := by
          rw [← Category.assoc]; exact h2.symm
    _ = ((E₁.L.mul _ (p₁ E₁) (p₂ E₁)).1 ≫ E₁.act x) ≫ k := by rw [hh]
    _ = (E₁.L.mul _ (p₁ E₁) (p₂ E₁)).1 ≫ k ≫ act x := by rw [Category.assoc, hact₁]
    _ = K₂ ≫ (m ≫ act x) := by
          rw [← Category.assoc, ← K₂_comp_m σ f E₁ k hk m hm e he ι hι act act_over hmul₁ hone₁ hinv₁ hact₁ K₂ hK₁ hK₂ K₃ hK₃₁ hK₃₂,
            Category.assoc]

theorem leg_assoc :
    K₃ ≫ (pullback.lift (pullback.fst (pullback.fst f f ≫ f) f ≫ m) (pullback.snd (pullback.fst f f ≫ f) f)
        (by rw [Category.assoc, hm]; exact pullback.condition) ≫ m) =
      K₃ ≫ (pullback.lift (pullback.fst (pullback.fst f f ≫ f) f ≫ pullback.fst f f)
        (pullback.lift (pullback.fst (pullback.fst f f ≫ f) f ≫ pullback.snd f f) (pullback.snd (pullback.fst f f ≫ f) f)
            (by rw [Category.assoc, ← pullback.condition (f := f) (g := f)]; exact pullback.condition) ≫ m)
        (by simp only [Category.assoc, hm, pullback.lift_fst_assoc]; congr 1; exact pullback.condition) ≫ m) := by

  have c1 : K₃ ≫ pullback.fst _ _ ≫ pullback.fst f f = (q₁ E₁).1 ≫ k := by
    rw [← Category.assoc, hK₃₁, Category.assoc, hK₁, q₁_coe, Category.assoc]
  have c2 : K₃ ≫ pullback.fst _ _ ≫ pullback.snd f f = (q₂ E₁).1 ≫ k := by
    rw [← Category.assoc, hK₃₁, Category.assoc, hK₂, q₂_coe, Category.assoc]
  have c3 : K₃ ≫ pullback.snd _ _ = (q₃ E₁).1 ≫ k := by rw [hK₃₂, q₃_coe]

  have h12 : K₃ ≫ pullback.fst _ _ ≫ m = (E₁.L.mul _ (q₁ E₁) (q₂ E₁)).1 ≫ k := by
    rw [← Category.assoc]
    exact (mul_comp_eq σ f E₁ k hk m hmul₁ _ (q₁ E₁) (q₂ E₁) _ (by rw [Category.assoc, c1]) (by rw [Category.assoc, c2])).symm
  have h23 : K₃ ≫ pullback.lift (pullback.fst (pullback.fst f f ≫ f) f ≫ pullback.snd f f) (pullback.snd (pullback.fst f f ≫ f) f)
            (by rw [Category.assoc, ← pullback.condition (f := f) (g := f)]; exact pullback.condition) ≫ m =
      (E₁.L.mul _ (q₂ E₁) (q₃ E₁)).1 ≫ k := by
    rw [← Category.assoc]
    exact (mul_comp_eq σ f E₁ k hk m hmul₁ _ (q₂ E₁) (q₃ E₁) _ (by rw [Category.assoc, pullback.lift_fst, c2])
      (by rw [Category.assoc, pullback.lift_snd, c3])).symm
  have L : K₃ ≫ (pullback.lift (pullback.fst (pullback.fst f f ≫ f) f ≫ m) (pullback.snd (pullback.fst f f ≫ f) f)
        (by rw [Category.assoc, hm]; exact pullback.condition) ≫ m) =
      (E₁.L.mul _ (E₁.L.mul _ (q₁ E₁) (q₂ E₁)) (q₃ E₁)).1 ≫ k := by
    rw [← Category.assoc]
    exact (mul_comp_eq σ f E₁ k hk m hmul₁ _ _ _ _ (by rw [Category.assoc, pullback.lift_fst, h12])
      (by rw [Category.assoc, pullback.lift_snd, c3])).symm
  have R' : K₃ ≫ (pullback.lift (pullback.fst (pullback.fst f f ≫ f) f ≫ pullback.fst f f)
        (pullback.lift (pullback.fst (pullback.fst f f ≫ f) f ≫ pullback.snd f f) (pullback.snd (pullback.fst f f ≫ f) f)
            (by rw [Category.assoc, ← pullback.condition (f := f) (g := f)]; exact pullback.condition) ≫ m)
        (by simp only [Category.assoc, hm, pullback.lift_fst_assoc]; congr 1; exact pullback.condition) ≫ m) =
      (E₁.L.mul _ (q₁ E₁) (E₁.L.mul _ (q₂ E₁) (q₃ E₁))).1 ≫ k := by
    rw [← Category.assoc]
    exact (mul_comp_eq σ f E₁ k hk m hmul₁ _ _ _ _ (by rw [Category.assoc, pullback.lift_fst, c1])
      (by rw [Category.assoc, pullback.lift_snd, h23])).symm
  rw [L, R', E₁.L.mul_assoc]

end Leg2
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_mul_assoc_comm_and_act_identities_of_forall_comp_eq_of_isPushout_of_isPullbackVia.GlueIdent"
end GlueIdent
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_mul_assoc_comm_and_act_identities_of_forall_comp_eq_of_isPushout_of_isPullbackVia.GlueIdent"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_mul_assoc_comm_and_act_identities_of_forall_comp_eq_of_isPushout_of_isPullbackVia.GlueIdent"

open GlueIdent

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B'']
    (φ' : B' →+* B) (φ'' : B'' →+* B)
    (hφ's : Function.Surjective φ') (hφ''s : Function.Surjective φ'')
    (hφ'n : IsNilpotent (RingHom.ker φ')) (hφ''n : IsNilpotent (RingHom.ker φ''))
    (E' : FakeEllipticCurve Λ N B') (E'' : FakeEllipticCurve Λ N B'') (EB : FakeEllipticCurve Λ N B)
    (h' : EB.A ⟶ E'.A) (hh' : FakeEllipticCurve.IsPullbackVia φ' E' EB h')
    (h'' : EB.A ⟶ E''.A) (hh'' : FakeEllipticCurve.IsPullbackVia φ'' E'' EB h'')
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of (pullbackRing φ' φ''))) [Flat f]
    (k' : E'.A ⟶ X) (hk' : CategoryTheory.IsPullback k' E'.f f (Spec.map (CommRingCat.ofHom (pullbackFst φ' φ''))))
    (k'' : E''.A ⟶ X) (hk'' : CategoryTheory.IsPullback k'' E''.f f (Spec.map (CommRingCat.ofHom (pullbackSnd φ' φ''))))
    (hcomm : h' ≫ k' = h'' ≫ k'') (hpo : IsPushout h' h'' k' k'')
    (m : pullback f f ⟶ X) (hm : m ≫ f = pullback.fst f f ≫ f)
    (e : Spec (CommRingCat.of (pullbackRing φ' φ'')) ⟶ X) (he : e ≫ f = 𝟙 _)
    (ι : X ⟶ X) (hι : ι ≫ f = f) (act : ↥Λ → (X ⟶ X)) (act_over : ∀ x : ↥Λ, act x ≫ f = f)
    (hmul' : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of B')) (P Q : SchemeHomOver t' E'.f),
        (E'.L.mul t' P Q).1 ≫ k' =
          pullback.lift (P.1 ≫ k') (Q.1 ≫ k')
            (by simp only [Category.assoc]; rw [hk'.w, ← Category.assoc, P.2, ← Category.assoc, Q.2]) ≫ m)
    (hone' : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of B')),
        (E'.L.one t').1 ≫ k' = (t' ≫ Spec.map (CommRingCat.ofHom (pullbackFst φ' φ''))) ≫ e)
    (hinv' : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of B')) (P : SchemeHomOver t' E'.f),
        (E'.L.inv t' P).1 ≫ k' = (P.1 ≫ k') ≫ ι)
    (hact' : ∀ x : ↥Λ, E'.act x ≫ k' = k' ≫ act x)
    (hmul'' : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of B'')) (P Q : SchemeHomOver t' E''.f),
        (E''.L.mul t' P Q).1 ≫ k'' =
          pullback.lift (P.1 ≫ k'') (Q.1 ≫ k'')
            (by simp only [Category.assoc]; rw [hk''.w, ← Category.assoc, P.2, ← Category.assoc, Q.2]) ≫ m)
    (hone'' : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of B'')),
        (E''.L.one t').1 ≫ k'' = (t' ≫ Spec.map (CommRingCat.ofHom (pullbackSnd φ' φ''))) ≫ e)
    (hinv'' : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of B'')) (P : SchemeHomOver t' E''.f),
        (E''.L.inv t' P).1 ≫ k'' = (P.1 ≫ k'') ≫ ι)
    (hact'' : ∀ x : ↥Λ, E''.act x ≫ k'' = k'' ≫ act x) :

      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (pullbackRing φ' φ''))) (x y z : SchemeHomOver t' f),
        pullback.lift (pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ m) z.1
            (by rw [Category.assoc, hm, pullback.lift_fst_assoc, x.2, z.2]) ≫ m =
          pullback.lift x.1 (pullback.lift y.1 z.1 (y.2.trans z.2.symm) ≫ m)
            (by rw [Category.assoc, hm, pullback.lift_fst_assoc, y.2, x.2]) ≫ m) ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (pullbackRing φ' φ''))) (x : SchemeHomOver t' f),
        pullback.lift (t' ≫ e) x.1 (by rw [Category.assoc, he, Category.comp_id, x.2]) ≫ m = x.1) ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (pullbackRing φ' φ''))) (x : SchemeHomOver t' f),
        pullback.lift x.1 (t' ≫ e) (by rw [Category.assoc, he, Category.comp_id, x.2]) ≫ m = x.1) ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (pullbackRing φ' φ''))) (x : SchemeHomOver t' f),
        pullback.lift (x.1 ≫ ι) x.1 (by rw [Category.assoc, hι]) ≫ m = t' ≫ e) ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (pullbackRing φ' φ''))) (x y : SchemeHomOver t' f),
        pullback.lift y.1 x.1 (y.2.trans x.2.symm) ≫ m = pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ m) ∧

      (∀ h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ, act ⟨1, h1⟩ = 𝟙 X) ∧
      (∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ), act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = act y ≫ act x) ∧
      (∀ (x : ↥Λ) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (pullbackRing φ' φ''))) (P Q : SchemeHomOver t' f),
        pullback.lift (P.1 ≫ act x) (Q.1 ≫ act x) (by rw [Category.assoc, act_over, Category.assoc, act_over, P.2, Q.2]) ≫ m =
          (pullback.lift P.1 Q.1 (P.2.trans Q.2.symm) ≫ m) ≫ act x) ∧
      (∀ (x y : ↥Λ) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (pullbackRing φ' φ''))) (P : SchemeHomOver t' f),
        P.1 ≫ act (x + y) =
          pullback.lift (P.1 ≫ act x) (P.1 ≫ act y) (by rw [Category.assoc, act_over, Category.assoc, act_over]) ≫ m) := by
  classical
  obtain ⟨sq', -, -, -⟩ := hh'
  obtain ⟨sq'', -, -, -⟩ := hh''

  haveI hfl1 : Flat (pullback.fst f f) := MorphismProperty.pullback_fst (P := @Flat) f f inferInstance
  haveI hfl2 : Flat (pullback.fst f f ≫ f) := inferInstance
  haveI hfl3 : Flat (pullback.fst (pullback.fst f f ≫ f) f) := MorphismProperty.pullback_fst (P := @Flat) _ f inferInstance
  haveI hfl4 : Flat (pullback.fst (pullback.fst f f ≫ f) f ≫ (pullback.fst f f ≫ f)) := inferInstance

  let K'₂ := pullback.map E'.f E'.f f f k' k' (Spec.map (CommRingCat.ofHom (pullbackFst φ' φ''))) hk'.w.symm hk'.w.symm
  let K''₂ := pullback.map E''.f E''.f f f k'' k'' (Spec.map (CommRingCat.ofHom (pullbackSnd φ' φ''))) hk''.w.symm hk''.w.symm
  let H'₂ := pullback.map EB.f EB.f E'.f E'.f h' h' (Spec.map (CommRingCat.ofHom φ')) sq'.w.symm sq'.w.symm
  let H''₂ := pullback.map EB.f EB.f E''.f E''.f h'' h'' (Spec.map (CommRingCat.ofHom φ'')) sq''.w.symm sq''.w.symm
  have hK'₂ := AlgebraicGeometry.isPullback_pullbackMap_fst_comp_of_isPullback_of_isPullback f f
    (Spec.map (CommRingCat.ofHom (pullbackFst φ' φ''))) E'.f E'.f k' k' hk' hk'
  have hK''₂ := AlgebraicGeometry.isPullback_pullbackMap_fst_comp_of_isPullback_of_isPullback f f
    (Spec.map (CommRingCat.ofHom (pullbackSnd φ' φ''))) E''.f E''.f k'' k'' hk'' hk''
  have hH'₂ := AlgebraicGeometry.isPullback_pullbackMap_fst_comp_of_isPullback_of_isPullback E'.f E'.f
    (Spec.map (CommRingCat.ofHom φ')) EB.f EB.f h' h' sq' sq'
  have hH''₂ := AlgebraicGeometry.isPullback_pullbackMap_fst_comp_of_isPullback_of_isPullback E''.f E''.f
    (Spec.map (CommRingCat.ofHom φ'')) EB.f EB.f h'' h'' sq'' sq''
  have hK'₂₁ : K'₂ ≫ pullback.fst f f = pullback.fst _ _ ≫ k' := pullback.lift_fst _ _ _
  have hK'₂₂ : K'₂ ≫ pullback.snd f f = pullback.snd _ _ ≫ k' := pullback.lift_snd _ _ _
  have hK''₂₁ : K''₂ ≫ pullback.fst f f = pullback.fst _ _ ≫ k'' := pullback.lift_fst _ _ _
  have hK''₂₂ : K''₂ ≫ pullback.snd f f = pullback.snd _ _ ≫ k'' := pullback.lift_snd _ _ _
  have hcomm₂ : H'₂ ≫ K'₂ = H''₂ ≫ K''₂ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hK'₂₁, Category.assoc, hK''₂₁, ← Category.assoc, ← Category.assoc,
        show H'₂ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ h' from pullback.lift_fst _ _ _,
        show H''₂ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ h'' from pullback.lift_fst _ _ _,
        Category.assoc, hcomm, Category.assoc]
    · rw [Category.assoc, hK'₂₂, Category.assoc, hK''₂₂, ← Category.assoc, ← Category.assoc,
        show H'₂ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ h' from pullback.lift_snd _ _ _,
        show H''₂ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ h'' from pullback.lift_snd _ _ _,
        Category.assoc, hcomm, Category.assoc]
  have PO₂ : IsPushout H'₂ H''₂ K'₂ K''₂ :=
    AlgebraicGeometry.isPushout_of_flat_of_isPullback_specMap_pullbackFst_pullbackSnd φ' φ'' hφ's hφ''s hφ'n hφ''n
      (pullback.fst f f ≫ f) (pullback.fst E'.f E'.f ≫ E'.f) (pullback.fst E''.f E''.f ≫ E''.f) (pullback.fst EB.f EB.f ≫ EB.f)
      K'₂ hK'₂ K''₂ hK''₂ H'₂ hH'₂ H''₂ hH''₂ hcomm₂

  let K'₃ := pullback.map (pullback.fst E'.f E'.f ≫ E'.f) E'.f (pullback.fst f f ≫ f) f K'₂ k'
    (Spec.map (CommRingCat.ofHom (pullbackFst φ' φ''))) hK'₂.w.symm hk'.w.symm
  let K''₃ := pullback.map (pullback.fst E''.f E''.f ≫ E''.f) E''.f (pullback.fst f f ≫ f) f K''₂ k''
    (Spec.map (CommRingCat.ofHom (pullbackSnd φ' φ''))) hK''₂.w.symm hk''.w.symm
  let H'₃ := pullback.map (pullback.fst EB.f EB.f ≫ EB.f) EB.f (pullback.fst E'.f E'.f ≫ E'.f) E'.f H'₂ h'
    (Spec.map (CommRingCat.ofHom φ')) hH'₂.w.symm sq'.w.symm
  let H''₃ := pullback.map (pullback.fst EB.f EB.f ≫ EB.f) EB.f (pullback.fst E''.f E''.f ≫ E''.f) E''.f H''₂ h''
    (Spec.map (CommRingCat.ofHom φ'')) hH''₂.w.symm sq''.w.symm
  have hK'₃ := AlgebraicGeometry.isPullback_pullbackMap_fst_comp_of_isPullback_of_isPullback (pullback.fst f f ≫ f) f
    (Spec.map (CommRingCat.ofHom (pullbackFst φ' φ''))) (pullback.fst E'.f E'.f ≫ E'.f) E'.f K'₂ k' hK'₂ hk'
  have hK''₃ := AlgebraicGeometry.isPullback_pullbackMap_fst_comp_of_isPullback_of_isPullback (pullback.fst f f ≫ f) f
    (Spec.map (CommRingCat.ofHom (pullbackSnd φ' φ''))) (pullback.fst E''.f E''.f ≫ E''.f) E''.f K''₂ k'' hK''₂ hk''
  have hH'₃ := AlgebraicGeometry.isPullback_pullbackMap_fst_comp_of_isPullback_of_isPullback (pullback.fst E'.f E'.f ≫ E'.f) E'.f
    (Spec.map (CommRingCat.ofHom φ')) (pullback.fst EB.f EB.f ≫ EB.f) EB.f H'₂ h' hH'₂ sq'
  have hH''₃ := AlgebraicGeometry.isPullback_pullbackMap_fst_comp_of_isPullback_of_isPullback (pullback.fst E''.f E''.f ≫ E''.f) E''.f
    (Spec.map (CommRingCat.ofHom φ'')) (pullback.fst EB.f EB.f ≫ EB.f) EB.f H''₂ h'' hH''₂ sq''
  have hK'₃₁ : K'₃ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ K'₂ := pullback.lift_fst _ _ _
  have hK'₃₂ : K'₃ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ k' := pullback.lift_snd _ _ _
  have hK''₃₁ : K''₃ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ K''₂ := pullback.lift_fst _ _ _
  have hK''₃₂ : K''₃ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ k'' := pullback.lift_snd _ _ _
  have hcomm₃ : H'₃ ≫ K'₃ = H''₃ ≫ K''₃ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hK'₃₁, Category.assoc, hK''₃₁, ← Category.assoc, ← Category.assoc,
        show H'₃ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ H'₂ from pullback.lift_fst _ _ _,
        show H''₃ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ H''₂ from pullback.lift_fst _ _ _,
        Category.assoc, hcomm₂, Category.assoc]
    · rw [Category.assoc, hK'₃₂, Category.assoc, hK''₃₂, ← Category.assoc, ← Category.assoc,
        show H'₃ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ h' from pullback.lift_snd _ _ _,
        show H''₃ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ h'' from pullback.lift_snd _ _ _,
        Category.assoc, hcomm, Category.assoc]
  have PO₃ : IsPushout H'₃ H''₃ K'₃ K''₃ :=
    AlgebraicGeometry.isPushout_of_flat_of_isPullback_specMap_pullbackFst_pullbackSnd φ' φ'' hφ's hφ''s hφ'n hφ''n
      (pullback.fst (pullback.fst f f ≫ f) f ≫ (pullback.fst f f ≫ f))
      (pullback.fst (pullback.fst E'.f E'.f ≫ E'.f) E'.f ≫ (pullback.fst E'.f E'.f ≫ E'.f))
      (pullback.fst (pullback.fst E''.f E''.f ≫ E''.f) E''.f ≫ (pullback.fst E''.f E''.f ≫ E''.f))
      (pullback.fst (pullback.fst EB.f EB.f ≫ EB.f) EB.f ≫ (pullback.fst EB.f EB.f ≫ EB.f))
      K'₃ hK'₃ K''₃ hK''₃ H'₃ hH'₃ H''₃ hH''₃ hcomm₃

  have Massoc := PO₃.hom_ext
    (leg_assoc (pullbackFst φ' φ'') f E' k' hk' m hm e he ι hι act act_over hmul' hone' hinv' hact' K'₂ hK'₂₁ hK'₂₂ K'₃ hK'₃₁ hK'₃₂)
    (leg_assoc (pullbackSnd φ' φ'') f E'' k'' hk'' m hm e he ι hι act act_over hmul'' hone'' hinv'' hact'' K''₂ hK''₂₁ hK''₂₂ K''₃ hK''₃₁ hK''₃₂)
  have Mone_mul : pullback.lift (f ≫ e) (𝟙 X) (by rw [Category.assoc, he, Category.comp_id, Category.id_comp]) ≫ m = 𝟙 X :=
    hpo.hom_ext
      (by rw [leg_one_mul (pullbackFst φ' φ'') f E' k' hk' m hm e he ι hι act act_over hmul' hone' hinv' hact' K'₂ hK'₂₁ hK'₂₂ K'₃ hK'₃₁ hK'₃₂, Category.comp_id])
      (by rw [leg_one_mul (pullbackSnd φ' φ'') f E'' k'' hk'' m hm e he ι hι act act_over hmul'' hone'' hinv'' hact'' K''₂ hK''₂₁ hK''₂₂ K''₃ hK''₃₁ hK''₃₂, Category.comp_id])
  have Mmul_one : pullback.lift (𝟙 X) (f ≫ e) (by rw [Category.assoc, he, Category.comp_id, Category.id_comp]) ≫ m = 𝟙 X :=
    hpo.hom_ext
      (by rw [leg_mul_one (pullbackFst φ' φ'') f E' k' hk' m hm e he ι hι act act_over hmul' hone' hinv' hact' K'₂ hK'₂₁ hK'₂₂ K'₃ hK'₃₁ hK'₃₂, Category.comp_id])
      (by rw [leg_mul_one (pullbackSnd φ' φ'') f E'' k'' hk'' m hm e he ι hι act act_over hmul'' hone'' hinv'' hact'' K''₂ hK''₂₁ hK''₂₂ K''₃ hK''₃₁ hK''₃₂, Category.comp_id])
  have Minv : pullback.lift ι (𝟙 X) (by rw [hι, Category.id_comp]) ≫ m = f ≫ e :=
    hpo.hom_ext
      (leg_inv (pullbackFst φ' φ'') f E' k' hk' m hm e he ι hι act act_over hmul' hone' hinv' hact' K'₂ hK'₂₁ hK'₂₂ K'₃ hK'₃₁ hK'₃₂)
      (leg_inv (pullbackSnd φ' φ'') f E'' k'' hk'' m hm e he ι hι act act_over hmul'' hone'' hinv'' hact'' K''₂ hK''₂₁ hK''₂₂ K''₃ hK''₃₁ hK''₃₂)
  have Mcomm : pullback.lift (pullback.snd f f) (pullback.fst f f) pullback.condition.symm ≫ m = m :=
    PO₂.hom_ext
      (leg_comm (pullbackFst φ' φ'') f E' k' hk' m hm e he ι hι act act_over hmul' hone' hinv' hact' K'₂ hK'₂₁ hK'₂₂ K'₃ hK'₃₁ hK'₃₂)
      (leg_comm (pullbackSnd φ' φ'') f E'' k'' hk'' m hm e he ι hι act act_over hmul'' hone'' hinv'' hact'' K''₂ hK''₂₁ hK''₂₂ K''₃ hK''₃₁ hK''₃₂)
  have Macthom : ∀ x : ↥Λ, pullback.lift (pullback.fst f f ≫ act x) (pullback.snd f f ≫ act x)
        (by simp only [Category.assoc, act_over]; exact pullback.condition) ≫ m = m ≫ act x := fun x =>
    PO₂.hom_ext
      (leg_act_hom (pullbackFst φ' φ'') f E' k' hk' m hm e he ι hι act act_over hmul' hone' hinv' hact' K'₂ hK'₂₁ hK'₂₂ K'₃ hK'₃₁ hK'₃₂ x)
      (leg_act_hom (pullbackSnd φ' φ'') f E'' k'' hk'' m hm e he ι hι act act_over hmul'' hone'' hinv'' hact'' K''₂ hK''₂₁ hK''₂₂ K''₃ hK''₃₁ hK''₃₂ x)
  have Mactadd : ∀ x y : ↥Λ, act (x + y) = pullback.lift (act x) (act y) (by rw [act_over, act_over]) ≫ m := fun x y =>
    hpo.hom_ext
      (leg_act_add (pullbackFst φ' φ'') f E' k' hk' m hm e he ι hι act act_over hmul' hone' hinv' hact' K'₂ hK'₂₁ hK'₂₂ K'₃ hK'₃₁ hK'₃₂ x y)
      (leg_act_add (pullbackSnd φ' φ'') f E'' k'' hk'' m hm e he ι hι act act_over hmul'' hone'' hinv'' hact'' K''₂ hK''₂₁ hK''₂₂ K''₃ hK''₃₁ hK''₃₂ x y)

  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro T t' x y z
    let w : T ⟶ pullback (pullback.fst f f ≫ f) f :=
      pullback.lift (pullback.lift x.1 y.1 (x.2.trans y.2.symm)) z.1 (by rw [pullback.lift_fst_assoc, x.2, z.2])
    have hw₁ : w ≫ pullback.fst _ _ = pullback.lift x.1 y.1 (x.2.trans y.2.symm) := pullback.lift_fst _ _ _
    have hw₂ : w ≫ pullback.snd _ _ = z.1 := pullback.lift_snd _ _ _
    have eL : pullback.lift (pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ m) z.1
          (by rw [Category.assoc, hm, pullback.lift_fst_assoc, x.2, z.2]) =
        w ≫ pullback.lift (pullback.fst (pullback.fst f f ≫ f) f ≫ m) (pullback.snd (pullback.fst f f ≫ f) f)
          (by rw [Category.assoc, hm]; exact pullback.condition) := by
      apply pullback.hom_ext
      · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, ← Category.assoc, hw₁]
      · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, hw₂]
    have eR : pullback.lift x.1 (pullback.lift y.1 z.1 (y.2.trans z.2.symm) ≫ m)
          (by rw [Category.assoc, hm, pullback.lift_fst_assoc, y.2, x.2]) =
        w ≫ pullback.lift (pullback.fst (pullback.fst f f ≫ f) f ≫ pullback.fst f f)
          (pullback.lift (pullback.fst (pullback.fst f f ≫ f) f ≫ pullback.snd f f) (pullback.snd (pullback.fst f f ≫ f) f)
            (by rw [Category.assoc, ← pullback.condition (f := f) (g := f)]; exact pullback.condition) ≫ m)
          (by simp only [Category.assoc, hm, pullback.lift_fst_assoc]; congr 1; exact pullback.condition) := by
      apply pullback.hom_ext
      · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, ← Category.assoc, hw₁, pullback.lift_fst]
      · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, ← Category.assoc]
        congr 1
        apply pullback.hom_ext
        · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, ← Category.assoc, hw₁, pullback.lift_snd]
        · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, hw₂]
    rw [eL, eR]
    exact (Category.assoc _ _ _).trans ((congrArg (w ≫ ·) Massoc).trans (Category.assoc _ _ _).symm)
  ·
    intro T t' x
    have ex : pullback.lift (t' ≫ e) x.1 (by rw [Category.assoc, he, Category.comp_id, x.2]) =
        x.1 ≫ pullback.lift (f ≫ e) (𝟙 X) (by rw [Category.assoc, he, Category.comp_id, Category.id_comp]) := by
      apply pullback.hom_ext
      · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, ← Category.assoc, x.2]
      · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, Category.comp_id]
    rw [ex, Category.assoc, Mone_mul, Category.comp_id]
  ·
    intro T t' x
    have ex : pullback.lift x.1 (t' ≫ e) (by rw [Category.assoc, he, Category.comp_id, x.2]) =
        x.1 ≫ pullback.lift (𝟙 X) (f ≫ e) (by rw [Category.assoc, he, Category.comp_id, Category.id_comp]) := by
      apply pullback.hom_ext
      · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, Category.comp_id]
      · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, ← Category.assoc, x.2]
    rw [ex, Category.assoc, Mmul_one, Category.comp_id]
  ·
    intro T t' x
    have ex : pullback.lift (x.1 ≫ ι) x.1 (by rw [Category.assoc, hι]) =
        x.1 ≫ pullback.lift ι (𝟙 X) (by rw [hι, Category.id_comp]) := by
      apply pullback.hom_ext
      · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst]
      · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, Category.comp_id]
    rw [ex, Category.assoc, Minv, ← Category.assoc, x.2]
  ·
    intro T t' x y
    have ex : pullback.lift y.1 x.1 (y.2.trans x.2.symm) =
        pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ pullback.lift (pullback.snd f f) (pullback.fst f f) pullback.condition.symm := by
      apply pullback.hom_ext
      · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, pullback.lift_snd]
      · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, pullback.lift_fst]
    rw [ex, Category.assoc, Mcomm]
  ·
    intro h1
    exact hpo.hom_ext
      (leg_act_one (pullbackFst φ' φ'') f E' k' hk' m hm e he ι hι act act_over hmul' hone' hinv' hact' K'₂ hK'₂₁ hK'₂₂ K'₃ hK'₃₁ hK'₃₂ h1)
      (leg_act_one (pullbackSnd φ' φ'') f E'' k'' hk'' m hm e he ι hι act act_over hmul'' hone'' hinv'' hact'' K''₂ hK''₂₁ hK''₂₂ K''₃ hK''₃₁ hK''₃₂ h1)
  ·
    intro x y h
    exact hpo.hom_ext
      (leg_act_mul (pullbackFst φ' φ'') f E' k' hk' m hm e he ι hι act act_over hmul' hone' hinv' hact' K'₂ hK'₂₁ hK'₂₂ K'₃ hK'₃₁ hK'₃₂ x y h)
      (leg_act_mul (pullbackSnd φ' φ'') f E'' k'' hk'' m hm e he ι hι act act_over hmul'' hone'' hinv'' hact'' K''₂ hK''₂₁ hK''₂₂ K''₃ hK''₃₁ hK''₃₂ x y h)
  ·
    intro x T t' P Q
    have ex : pullback.lift (P.1 ≫ act x) (Q.1 ≫ act x) (by rw [Category.assoc, act_over, Category.assoc, act_over, P.2, Q.2]) =
        pullback.lift P.1 Q.1 (P.2.trans Q.2.symm) ≫
          pullback.lift (pullback.fst f f ≫ act x) (pullback.snd f f ≫ act x)
            (by simp only [Category.assoc, act_over]; exact pullback.condition) := by
      apply pullback.hom_ext
      · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst]
      · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd]
    rw [ex, Category.assoc, Macthom, Category.assoc]
  ·
    intro x y T t' P
    rw [Mactadd, ← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst]
    · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_mul_assoc_comm_and_act_identities_of_forall_comp_eq_of_isPushout_of_isPullbackVia
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_mul_assoc_comm_and_act_identities_of_forall_comp_eq_of_isPushout_of_isPullbackVia (solution)
