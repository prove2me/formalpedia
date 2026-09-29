-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.forall_factorsThrough_imp_eq_one_imp_and_imp_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/cafa7a7e-4ab1-5a59-988b-5c998a09df42

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_equiv_schemeHomOver_of_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_forall_factorsThrough_imp_eq_one_imp_and_imp_of_isPullback

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

open GoodReductionJacobian

namespace TPBody

theorem coe_nsmulPt_eq_of_coe_eq {S : Type} [CommRing S] {A T : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) {t₀ t₁ : T ⟶ Spec (CommRingCat.of S)} (h : t₀ = t₁)
    (Y : SchemeHomOver t₀ f) (Y' : SchemeHomOver t₁ f) (hY : Y.1 = Y'.1) (j : ℕ) :
    (nsmulPt L t₀ j Y).1 = (nsmulPt L t₁ j Y').1 := by
  subst h
  obtain rfl : Y = Y' := Subtype.ext hY
  rfl

theorem coe_one_eq_of_eq {S : Type} [CommRing S] {A T : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) {t₀ t₁ : T ⟶ Spec (CommRingCat.of S)} (h : t₀ = t₁) :
    (L.one t₀).1 = (L.one t₁).1 := by
  subst h; rfl

end TPBody

open TPBody in
theorem solution
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) {N : ℕ} (m ℓ : ℕ) (L₀ : Submodule ℤ ℍ[ℚ, a, b])
    {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (u : FakeEllipticCurve.WithFullLevel Λ N m S) (u' : FakeEllipticCurve.WithFullLevel Λ N m S')
    (hu : FakeEllipticCurve.WithFullLevel.IsPullback φ u u') :

    (∀ (k : Type) [Field k] [IsAlgClosed k] (sk' : S' →+* k),
      (∀ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ →
        FactorsThrough u.1.lev
          (pushPt (u.1.act x) (u.1.act_over x)
            (nsmulPt u.1.L (geomPoint k (sk'.comp φ)) (m / ℓ) (FakeEllipticCurve.sectionAt u.2.P k (sk'.comp φ)))) →
        pushPt (u.1.act x) (u.1.act_over x)
            (nsmulPt u.1.L (geomPoint k (sk'.comp φ)) (m / ℓ) (FakeEllipticCurve.sectionAt u.2.P k (sk'.comp φ))) = u.1.L.one (geomPoint k (sk'.comp φ))) →
      (∀ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ →
        FactorsThrough u'.1.lev
          (pushPt (u'.1.act x) (u'.1.act_over x)
            (nsmulPt u'.1.L (geomPoint k sk') (m / ℓ) (FakeEllipticCurve.sectionAt u'.2.P k sk'))) →
        pushPt (u'.1.act x) (u'.1.act_over x)
            (nsmulPt u'.1.L (geomPoint k sk') (m / ℓ) (FakeEllipticCurve.sectionAt u'.2.P k sk')) = u'.1.L.one (geomPoint k sk'))) ∧

    (∀ (k : Type) [Field k] [IsAlgClosed k] (sk' : S' →+* k), (N : k) ≠ 0 →
      (∀ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ →
        FactorsThrough u'.1.lev
          (pushPt (u'.1.act x) (u'.1.act_over x)
            (nsmulPt u'.1.L (geomPoint k sk') (m / ℓ) (FakeEllipticCurve.sectionAt u'.2.P k sk'))) →
        pushPt (u'.1.act x) (u'.1.act_over x)
            (nsmulPt u'.1.L (geomPoint k sk') (m / ℓ) (FakeEllipticCurve.sectionAt u'.2.P k sk')) = u'.1.L.one (geomPoint k sk')) →
      (∀ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ →
        FactorsThrough u.1.lev
          (pushPt (u.1.act x) (u.1.act_over x)
            (nsmulPt u.1.L (geomPoint k (sk'.comp φ)) (m / ℓ) (FakeEllipticCurve.sectionAt u.2.P k (sk'.comp φ)))) →
        pushPt (u.1.act x) (u.1.act_over x)
            (nsmulPt u.1.L (geomPoint k (sk'.comp φ)) (m / ℓ) (FakeEllipticCurve.sectionAt u.2.P k (sk'.comp φ))) = u.1.L.one (geomPoint k (sk'.comp φ)))) := by
  obtain ⟨g, hg, hmul, hact, hlev, hP⟩ := hu
  refine ⟨fun k _ _ sk' hT x hx hfac => ?_, fun k _ _ sk' hN hT' x hx hfacR => ?_⟩
  ·
    obtain ⟨σ, hσ1, hσone, hσmul, hσinv, hσnsmul, hσact⟩ :=
      CerednikDrinfeld.QM.FakeEllipticCurve.exists_equiv_schemeHomOver_of_isPullback φ u.1 u'.1 g hg hmul hact
        (geomPoint k sk')
    have hbase : geomPoint k sk' ≫ Spec.map (CommRingCat.ofHom φ) = geomPoint k (sk'.comp φ) := by
      show Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp]; rfl
    have hcoe : (σ (pushPt (u'.1.act x) (u'.1.act_over x)
          (nsmulPt u'.1.L (geomPoint k sk') (m / ℓ) (FakeEllipticCurve.sectionAt u'.2.P k sk')))).1 =
        (pushPt (u.1.act x) (u.1.act_over x)
          (nsmulPt u.1.L (geomPoint k (sk'.comp φ)) (m / ℓ) (FakeEllipticCurve.sectionAt u.2.P k (sk'.comp φ)))).1 := by
      rw [hσact, hσnsmul]
      simp only [pushPt, mapPt_coe]
      congr 1
      refine coe_nsmulPt_eq_of_coe_eq u.1.L hbase _ _ ?_ (m / ℓ)
      rw [hσ1]
      simp only [FakeEllipticCurve.sectionAt, schemeHomOverComp_coe, Category.assoc, hP]
      rw [← Category.assoc, hbase]
    have hfacR : FactorsThrough u.1.lev (pushPt (u.1.act x) (u.1.act_over x)
          (nsmulPt u.1.L (geomPoint k (sk'.comp φ)) (m / ℓ) (FakeEllipticCurve.sectionAt u.2.P k (sk'.comp φ)))) := by
      obtain ⟨P₀, hP₀⟩ := hlev _ _ hfac
      exact ⟨P₀, by rw [hP₀, ← hσ1, hcoe]⟩
    have hR := hT x hx hfacR
    apply σ.injective
    rw [hσone]
    apply Subtype.ext
    rw [hcoe, hR]
    exact coe_one_eq_of_eq u.1.L hbase.symm
  ·
    obtain ⟨σ, hσ1, hσone, hσmul, hσinv, hσnsmul, hσact⟩ :=
      CerednikDrinfeld.QM.FakeEllipticCurve.exists_equiv_schemeHomOver_of_isPullback φ u.1 u'.1 g hg hmul hact
        (geomPoint k sk')
    have hbase : geomPoint k sk' ≫ Spec.map (CommRingCat.ofHom φ) = geomPoint k (sk'.comp φ) := by
      show Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp]; rfl
    have hcoe : (σ (pushPt (u'.1.act x) (u'.1.act_over x)
          (nsmulPt u'.1.L (geomPoint k sk') (m / ℓ) (FakeEllipticCurve.sectionAt u'.2.P k sk')))).1 =
        (pushPt (u.1.act x) (u.1.act_over x)
          (nsmulPt u.1.L (geomPoint k (sk'.comp φ)) (m / ℓ) (FakeEllipticCurve.sectionAt u.2.P k (sk'.comp φ)))).1 := by
      rw [hσact, hσnsmul]
      simp only [pushPt, mapPt_coe]
      congr 1
      refine coe_nsmulPt_eq_of_coe_eq u.1.L hbase _ _ ?_ (m / ℓ)
      rw [hσ1]
      simp only [FakeEllipticCurve.sectionAt, schemeHomOverComp_coe, Category.assoc, hP]
      rw [← Category.assoc, hbase]
    have hN0 : N ≠ 0 := fun h => hN (by rw [h, Nat.cast_zero])
    haveI : NeZero N := ⟨hN0⟩
    obtain ⟨e', -⟩ := u'.1.lev_fibre k sk' hN
    obtain ⟨e, -⟩ := u.1.lev_fibre k (sk'.comp φ) hN

    obtain ⟨c, hc1⟩ : ∃ c : {P : SchemeHomOver (geomPoint k sk') u'.1.f // FactorsThrough u'.1.lev P} →
        {R : SchemeHomOver (geomPoint k (sk'.comp φ)) u.1.f // FactorsThrough u.1.lev R},
        ∀ P, (c P).1.1 = (σ P.1).1 := by
      refine ⟨fun P => ⟨⟨(σ P.1).1, ?_⟩, ?_⟩, fun P => rfl⟩
      · rw [← hbase]; exact (σ P.1).2
      · obtain ⟨P₀, hP₀⟩ := hlev _ P.1 P.2
        exact ⟨P₀, by rw [hσ1]; exact hP₀⟩
    have hc_inj : Function.Injective c := fun P₁ P₂ h =>
      Subtype.ext (σ.injective (Subtype.ext
        ((hc1 P₁).symm.trans ((congrArg (fun R => R.1.1) h).trans (hc1 P₂)))))
    haveI : Finite {R : SchemeHomOver (geomPoint k (sk'.comp φ)) u.1.f // FactorsThrough u.1.lev R} :=
      Finite.of_equiv _ e
    have hcard : Nat.card {R : SchemeHomOver (geomPoint k (sk'.comp φ)) u.1.f // FactorsThrough u.1.lev R} ≤
        Nat.card {P : SchemeHomOver (geomPoint k sk') u'.1.f // FactorsThrough u'.1.lev P} :=
      ((Nat.card_congr e.symm).trans (Nat.card_congr e'.symm).symm).le
    obtain ⟨P₁, hP₁⟩ := (hc_inj.bijective_of_nat_card_le hcard).2 ⟨_, hfacR⟩
    have hP₁Q : P₁.1 = (pushPt (u'.1.act x) (u'.1.act_over x)
          (nsmulPt u'.1.L (geomPoint k sk') (m / ℓ) (FakeEllipticCurve.sectionAt u'.2.P k sk'))) :=
      σ.injective (Subtype.ext ((hc1 P₁).symm.trans ((congrArg (fun R => R.1.1) hP₁).trans hcoe.symm)))
    have hQ' := hT' x hx (hP₁Q ▸ P₁.2)
    apply Subtype.ext
    rw [← hcoe, hQ', hσone]
    exact coe_one_eq_of_eq u.1.L hbase

end S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_forall_factorsThrough_imp_eq_one_imp_and_imp_of_isPullback
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_forall_factorsThrough_imp_eq_one_imp_and_imp_of_isPullback (solution)
