-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_relFrobenius_of_isPullback_frobenius
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/8865c09f-b5fa-518c-a4b2-f9ccc33c533d

import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius
import Definitions.Def_AlgebraicGeometry_SchemeFrobenius
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_relFrobenius_of_isPullback_frobenius

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (k : Type u) [Field k] (ℓ : ℕ) [hℓ : Fact ℓ.Prime] [CharP k ℓ]
    (E Eℓ : FakeEllipticCurve Λ N k)
    (pr : Eℓ.A ⟶ E.A)
    (pr_isPullback : CategoryTheory.IsPullback pr Eℓ.f E.f (Spec.map (CommRingCat.ofHom (frobenius k ℓ))))
    (pr_mul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t' Eℓ.f),
      (Eℓ.L.mul t' P Q).1 ≫ pr =
        (E.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (frobenius k ℓ)))
          ⟨P.1 ≫ pr, by rw [Category.assoc, pr_isPullback.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ pr, by rw [Category.assoc, pr_isPullback.w, ← Category.assoc, Q.2]⟩).1)
    (pr_act : ∀ x : ↥Λ, Eℓ.act x ≫ pr = pr ≫ E.act x)
    (pr_lev : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t' Eℓ.f),
      FactorsThrough Eℓ.lev P → ∃ P₀ : T ⟶ E.C, P₀ ≫ E.lev = P.1 ≫ pr)
    (pr_lev' : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t' Eℓ.f),
      (∃ P₀ : T ⟶ E.C, P₀ ≫ E.lev = P.1 ≫ pr) → FactorsThrough Eℓ.lev P)
    (hA : (ℓ : Γ(E.A, ⊤)) = 0) :
    ∃ (F : E.A ⟶ Eℓ.A) (F_over : F ≫ Eℓ.f = E.f),
      F ≫ pr = E.A.frobenius ℓ 1 hℓ.out hA ∧
      (∀ (B : Type u) [CommRing B] [CharP B ℓ] (x : Spec (CommRingCat.of B) ⟶ E.A),
        x ≫ F ≫ pr = Spec.map (CommRingCat.ofHom (frobenius B ℓ)) ≫ x) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E.f),
        mapPt F F_over (E.L.mul t P Q) = Eℓ.L.mul t (mapPt F F_over P) (mapPt F F_over Q)) ∧
      (∀ x : ↥Λ, E.act x ≫ F = F ≫ Eℓ.act x) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E.f),
        FactorsThrough E.lev P → FactorsThrough Eℓ.lev (mapPt F F_over P)) := by

  have hk0 : (ℓ : k) = 0 := CharP.cast_eq_zero k ℓ
  have hS : (ℓ : Γ(Spec (CommRingCat.of k), ⊤)) = 0 := Scheme.natCast_eq_zero_ΓSpec hk0
  have hpow : ∀ (B : Type u) [CommRing B] [CharP B ℓ],
      powCharRingHom B ℓ 1 hℓ.out (CharP.cast_eq_zero B ℓ) = frobenius B ℓ := by
    intro B _ _; ext x; simp [frobenius, powCharRingHom_apply]
  have hSpecFrob : ∀ (B : Type u) [CommRing B] [CharP B ℓ] (hB : (ℓ : Γ(Spec (CommRingCat.of B), ⊤)) = 0),
      (Spec (CommRingCat.of B)).frobenius ℓ 1 hℓ.out hB = Spec.map (CommRingCat.ofHom (frobenius B ℓ)) := by
    intro B _ _ hB
    rw [← hpow B]
    exact Scheme.frobenius_Spec ℓ 1 hℓ.out (CharP.cast_eq_zero B ℓ)

  have w : E.A.frobenius ℓ 1 hℓ.out hA ≫ E.f = E.f ≫ Spec.map (CommRingCat.ofHom (frobenius k ℓ)) := by
    rw [← hSpecFrob k hS]
    exact Scheme.frobenius_comp E.f ℓ 1 hℓ.out hA hS

  refine ⟨pr_isPullback.lift (E.A.frobenius ℓ 1 hℓ.out hA) E.f w, pr_isPullback.lift_snd _ _ _,
    pr_isPullback.lift_fst _ _ _, ?_, ?_, ?_, ?_⟩
  ·
    intro B _ _ x
    have hB : (ℓ : Γ(Spec (CommRingCat.of B), ⊤)) = 0 := Scheme.natCast_eq_zero_ΓSpec (CharP.cast_eq_zero B ℓ)
    rw [pr_isPullback.lift_fst, ← hSpecFrob B hB]
    exact (Scheme.frobenius_comp x ℓ 1 hℓ.out hB hA).symm
  ·
    intro T t P Q
    have hT : (ℓ : Γ(T, ⊤)) = 0 := by rw [← map_natCast t.appTop.hom ℓ, hS, map_zero]
    have hψ : T.frobenius ℓ 1 hℓ.out hT ≫ t = t ≫ Spec.map (CommRingCat.ofHom (frobenius k ℓ)) := by
      rw [← hSpecFrob k hS]; exact Scheme.frobenius_comp t ℓ 1 hℓ.out hT hS
    apply Subtype.ext
    apply pr_isPullback.hom_ext
    ·
      have key : ∀ R₀ : SchemeHomOver t E.f,
          (mapPt (pr_isPullback.lift (E.A.frobenius ℓ 1 hℓ.out hA) E.f w) (pr_isPullback.lift_snd _ _ _) R₀).1 ≫ pr =
            T.frobenius ℓ 1 hℓ.out hT ≫ R₀.1 := by
        intro R₀
        show (R₀.1 ≫ _) ≫ pr = _
        rw [Category.assoc, pr_isPullback.lift_fst]
        exact (Scheme.frobenius_comp R₀.1 ℓ 1 hℓ.out hT hA).symm
      rw [key, pr_mul]
      have hP : (⟨(mapPt (pr_isPullback.lift (E.A.frobenius ℓ 1 hℓ.out hA) E.f w) (pr_isPullback.lift_snd _ _ _) P).1 ≫ pr,
          by rw [Category.assoc, pr_isPullback.w, ← Category.assoc, (mapPt _ _ P).2]⟩ :
            SchemeHomOver (t ≫ Spec.map (CommRingCat.ofHom (frobenius k ℓ))) E.f) =
          GoodReductionJacobian.schemeHomOverComp (T.frobenius ℓ 1 hℓ.out hT) hψ P := Subtype.ext (key P)
      have hQ : (⟨(mapPt (pr_isPullback.lift (E.A.frobenius ℓ 1 hℓ.out hA) E.f w) (pr_isPullback.lift_snd _ _ _) Q).1 ≫ pr,
          by rw [Category.assoc, pr_isPullback.w, ← Category.assoc, (mapPt _ _ Q).2]⟩ :
            SchemeHomOver (t ≫ Spec.map (CommRingCat.ofHom (frobenius k ℓ))) E.f) =
          GoodReductionJacobian.schemeHomOverComp (T.frobenius ℓ 1 hℓ.out hT) hψ Q := Subtype.ext (key Q)
      rw [hP, hQ, ← E.L.mul_natural t _ (T.frobenius ℓ 1 hℓ.out hT) hψ P Q]
      rfl
    ·
      rw [(mapPt _ _ (E.L.mul t P Q)).2, (Eℓ.L.mul t _ _).2]
  ·
    intro x
    apply pr_isPullback.hom_ext
    · rw [Category.assoc, pr_isPullback.lift_fst, Category.assoc, pr_act, ← Category.assoc, pr_isPullback.lift_fst]
      exact (Scheme.frobenius_comp (E.act x) ℓ 1 hℓ.out hA hA).symm
    · rw [Category.assoc, pr_isPullback.lift_snd, Category.assoc, Eℓ.act_over, pr_isPullback.lift_snd, E.act_over]
  ·
    intro T t P hP
    obtain ⟨P₀, hP₀⟩ := hP
    have hT : (ℓ : Γ(T, ⊤)) = 0 := by rw [← map_natCast t.appTop.hom ℓ, hS, map_zero]
    have hC : (ℓ : Γ(E.C, ⊤)) = 0 := by rw [← map_natCast (E.lev ≫ E.f).appTop.hom ℓ, hS, map_zero]
    refine pr_lev' t _ ⟨T.frobenius ℓ 1 hℓ.out hT ≫ P₀, ?_⟩
    show _ = (P.1 ≫ _) ≫ pr
    simp only [Category.assoc, pr_isPullback.lift_fst]
    rw [← Scheme.frobenius_comp P.1 ℓ 1 hℓ.out hT hA, ← hP₀]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_relFrobenius_of_isPullback_frobenius
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_relFrobenius_of_isPullback_frobenius (solution)
