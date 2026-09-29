-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.not_exists_isPullbackVia_algebraMap_dualNumber_of_forall_existsUnique_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/71cf7cc2-9fb8-5269-8168-36fd2831bd86

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isPullbackVia_id
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_not_exists_isPullbackVia_algebraMap_dualNumber_of_forall_existsUnique_smul

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

set_option maxHeartbeats 4000000 in
theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (k : Type) [Field k] [IsAlgClosed k] (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ]
    (hqq'u : IsUnit ((q * q' : ℕ) : k))
    (u : FakeEllipticCurve Λ 1 k)
    (v : FakeEllipticCurve Λ 1 (DualNumber k)) (gv : u.A ⟶ v.A)
    (hv : FakeEllipticCurve.IsPullbackVia (TrivSqZeroExt.fstHom k k k).toRingHom v u gv)
    (hgen : ∀ (t : FakeEllipticCurve Λ 1 (DualNumber k)) (gt : u.A ⟶ t.A),
        FakeEllipticCurve.IsPullbackVia (TrivSqZeroExt.fstHom k k k).toRingHom t u gt →
        (∃ c : k, ∀ (w : FakeEllipticCurve Λ 1 (DualNumber k)) (gw : u.A ⟶ w.A) (hw : w.A ⟶ v.A),
          FakeEllipticCurve.IsPullbackVia (TrivSqZeroExt.fstHom k k k).toRingHom w u gw →
          FakeEllipticCurve.IsPullbackVia (TrivSqZeroExt.map (R' := k) (c • (LinearMap.id : k →ₗ[k] k))).toRingHom v w hw →
          gw ≫ hw = gv →
          ∃ h : t.A ⟶ w.A, FakeEllipticCurve.IsPullbackVia (RingHom.id (DualNumber k)) w t h ∧ gt ≫ h = gw) ∧
        (∀ (c c' : k) (w w' : FakeEllipticCurve Λ 1 (DualNumber k)) (gw : u.A ⟶ w.A) (gw' : u.A ⟶ w'.A)
          (hw : w.A ⟶ v.A) (hw' : w'.A ⟶ v.A),
          FakeEllipticCurve.IsPullbackVia (TrivSqZeroExt.fstHom k k k).toRingHom w u gw →
          FakeEllipticCurve.IsPullbackVia (TrivSqZeroExt.map (R' := k) (c • (LinearMap.id : k →ₗ[k] k))).toRingHom v w hw →
          gw ≫ hw = gv →
          FakeEllipticCurve.IsPullbackVia (TrivSqZeroExt.fstHom k k k).toRingHom w' u gw' →
          FakeEllipticCurve.IsPullbackVia (TrivSqZeroExt.map (R' := k) (c' • (LinearMap.id : k →ₗ[k] k))).toRingHom v w' hw' →
          gw' ≫ hw' = gv →
          (∃ h : t.A ⟶ w.A, FakeEllipticCurve.IsPullbackVia (RingHom.id (DualNumber k)) w t h ∧ gt ≫ h = gw) →
          (∃ h' : t.A ⟶ w'.A, FakeEllipticCurve.IsPullbackVia (RingHom.id (DualNumber k)) w' t h' ∧ gt ≫ h' = gw') →
          c = c'))
    (w : FakeEllipticCurve Λ 1 (DualNumber k)) (gw : u.A ⟶ w.A)
    (hw : FakeEllipticCurve.IsPullbackVia (TrivSqZeroExt.fstHom k k k).toRingHom w u gw)
    (h : w.A ⟶ v.A) (hh : FakeEllipticCurve.IsPullbackVia (RingHom.id (DualNumber k)) v w h) (hgwh : gw ≫ h = gv) :
    ¬ ∃ h₀ : w.A ⟶ u.A,
        FakeEllipticCurve.IsPullbackVia (algebraMap k (DualNumber k)) u w h₀ ∧ gw ≫ h₀ = 𝟙 u.A := by
  rintro ⟨h₀, hh₀, hgh₀⟩
  obtain ⟨-, huniq⟩ := hgen w gw hw

  have hσ1 : (TrivSqZeroExt.map (R' := k) ((1 : k) • (LinearMap.id : k →ₗ[k] k))).toRingHom = RingHom.id (DualNumber k) := by
    apply RingHom.ext; intro x
    apply TrivSqZeroExt.ext <;> simp
  have hσ0 : (TrivSqZeroExt.map (R' := k) ((0 : k) • (LinearMap.id : k →ₗ[k] k))).toRingHom =
      (algebraMap k (DualNumber k)).comp (TrivSqZeroExt.fstHom k k k).toRingHom := by
    apply RingHom.ext; intro x
    apply TrivSqZeroExt.ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

  have h1 : FakeEllipticCurve.IsPullbackVia (TrivSqZeroExt.map (R' := k) ((1 : k) • (LinearMap.id : k →ₗ[k] k))).toRingHom
      v v (𝟙 v.A) := by
    rw [hσ1]
    exact CerednikDrinfeld.QM.FakeEllipticCurve.isPullbackVia_id (DualNumber k) v

  have h0 : FakeEllipticCurve.IsPullbackVia (TrivSqZeroExt.map (R' := k) ((0 : k) • (LinearMap.id : k →ₗ[k] k))).toRingHom
      v w (h₀ ≫ gv) := by
    rw [hσ0]
    obtain ⟨hc₀, hmul₀, hact₀, hlev₀⟩ := hh₀
    obtain ⟨hcv, hmulv, hactv, hlevv⟩ := hv
    have hbot : Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) ≫
        Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) =
        Spec.map (CommRingCat.ofHom ((algebraMap k (DualNumber k)).comp (TrivSqZeroExt.fstHom k k k).toRingHom)) := by
      rw [← Spec.map_comp]; rfl
    have hc : IsPullback (h₀ ≫ gv) w.f v.f
        (Spec.map (CommRingCat.ofHom ((algebraMap k (DualNumber k)).comp (TrivSqZeroExt.fstHom k k k).toRingHom))) := by
      rw [← hbot]; exact hc₀.paste_horiz hcv
    refine ⟨hc, ?_, ?_, ?_⟩
    · intro T t' P Q
      have mul_congr : ∀ (t₁ t₂ : T ⟶ Spec (CommRingCat.of (DualNumber k))) (h12 : t₁ = t₂) (x y : SchemeHomOver t₁ v.f),
          (v.L.mul t₁ x y).1 = (v.L.mul t₂ ⟨x.1, h12 ▸ x.2⟩ ⟨y.1, h12 ▸ y.2⟩).1 := by
        intro t₁ t₂ h12 x y; subst h12; rfl
      rw [← Category.assoc, hmul₀, hmulv, mul_congr _ _ (by rw [Category.assoc, hbot])]
      simp only [Category.assoc]
    · intro x
      rw [← Category.assoc, hact₀, Category.assoc, hactv, Category.assoc]
    · intro T t' P hP
      obtain ⟨P₁, hP₁⟩ := hlev₀ t' P hP
      obtain ⟨P₀, hP₀⟩ := hlevv (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))))
        ⟨P.1 ≫ h₀, by rw [Category.assoc, hc₀.w, ← Category.assoc, P.2]⟩ ⟨P₁, hP₁⟩
      exact ⟨P₀, by rw [hP₀, Category.assoc]⟩
  have h10 : (1 : k) = 0 :=
    huniq 1 0 v w gv gw (𝟙 v.A) (h₀ ≫ gv) hv h1 (Category.comp_id _) hw h0
      (by rw [← Category.assoc, hgh₀, Category.id_comp]) ⟨h, hh, hgwh⟩
      ⟨𝟙 w.A, CerednikDrinfeld.QM.FakeEllipticCurve.isPullbackVia_id (DualNumber k) w, Category.comp_id _⟩
  exact one_ne_zero h10

end S_CerednikDrinfeld_QM_FakeEllipticCurve_not_exists_isPullbackVia_algebraMap_dualNumber_of_forall_existsUnique_smul
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_not_exists_isPullbackVia_algebraMap_dualNumber_of_forall_existsUnique_smul (solution)
