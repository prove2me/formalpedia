-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.isPullback_Spec_map_factor_chartERing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/88053660-2e5c-5ac9-ae15-89ba9e9a1054

import Definitions.Def_CerednikDrinfeld_MumfordGlueLevel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_isPullback_Spec_map_factor_chartERing

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

namespace AffineCartAux

open CategoryTheory CategoryTheory.Limits

universe w

theorem isPushout_quotient_pow {R A : Type w} [CommRing R] [CommRing A] (φ : R →+* A) (a : R) {k m : ℕ}
    (hR : Ideal.span {a ^ m} ≤ Ideal.span {a ^ k}) (hA : Ideal.span {φ a ^ m} ≤ Ideal.span {φ a ^ k})
    (q : R ⧸ Ideal.span {a ^ k} →+* A ⧸ Ideal.span {φ a ^ k})
    (hq : q.comp (Ideal.Quotient.mk (Ideal.span {a ^ k})) = (Ideal.Quotient.mk (Ideal.span {φ a ^ k})).comp φ)
    (q' : R ⧸ Ideal.span {a ^ m} →+* A ⧸ Ideal.span {φ a ^ m})
    (hq' : q'.comp (Ideal.Quotient.mk (Ideal.span {a ^ m})) = (Ideal.Quotient.mk (Ideal.span {φ a ^ m})).comp φ) :
    IsPushout (CommRingCat.ofHom q') (CommRingCat.ofHom (Ideal.Quotient.factor hR))
      (CommRingCat.ofHom (Ideal.Quotient.factor hA)) (CommRingCat.ofHom q) := by
  have hq1 : ∀ x : R, q (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (φ x) := fun x => RingHom.congr_fun hq x
  have hq1' : ∀ x : R, q' (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (φ x) := fun x => RingHom.congr_fun hq' x
  have w : CommRingCat.ofHom q' ≫ CommRingCat.ofHom (Ideal.Quotient.factor hA) =
      CommRingCat.ofHom (Ideal.Quotient.factor hR) ≫ CommRingCat.ofHom q := by
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 1
    apply Ideal.Quotient.ringHom_ext
    ext x
    simp only [RingHom.comp_apply, hq1', Ideal.Quotient.factor_mk, hq1]

  have hker : ∀ (s : PushoutCocone (CommRingCat.ofHom q') (CommRingCat.ofHom (Ideal.Quotient.factor hR))),
      ∀ c ∈ Ideal.span {φ a ^ k}, (s.inl.hom.comp (Ideal.Quotient.mk (Ideal.span {φ a ^ m}))) c = 0 := by
    intro s c hc
    obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.mp hc
    have key : s.inl.hom (Ideal.Quotient.mk _ (φ a ^ k)) = 0 := by
      have h1 : Ideal.Quotient.mk (Ideal.span {φ a ^ m}) (φ a ^ k) = q' (Ideal.Quotient.mk _ (a ^ k)) := by
        rw [hq1', map_pow φ a k]
      have h2 := congrArg (fun (F : CommRingCat.of (R ⧸ Ideal.span {a ^ m}) ⟶ s.pt) => F.hom (Ideal.Quotient.mk _ (a ^ k)))
        s.condition
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
      rw [h1, h2, Ideal.Quotient.factor_mk,
        (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton (a ^ k))) :
          Ideal.Quotient.mk (Ideal.span {a ^ k}) (a ^ k) = 0), map_zero]
    show s.inl.hom (Ideal.Quotient.mk _ (d * φ a ^ k)) = 0
    rw [map_mul, map_mul, key, mul_zero]
  refine IsPushout.of_isColimit' ⟨w⟩ (PushoutCocone.IsColimit.mk w
    (fun s => CommRingCat.ofHom (Ideal.Quotient.lift (Ideal.span {φ a ^ k})
      (s.inl.hom.comp (Ideal.Quotient.mk (Ideal.span {φ a ^ m}))) (hker s)))
    (fun s => ?_) (fun s => ?_) (fun s m' h1 h2 => ?_))
  · apply CommRingCat.hom_ext
    rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom, CommRingCat.hom_ofHom]
    apply Ideal.Quotient.ringHom_ext
    ext y
    rw [RingHom.comp_apply, RingHom.comp_apply, Ideal.Quotient.factor_mk, Ideal.Quotient.lift_mk, RingHom.comp_apply]
  · apply CommRingCat.hom_ext
    rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom, CommRingCat.hom_ofHom]
    apply Ideal.Quotient.ringHom_ext
    ext x
    have h2 := congrArg (fun (F : CommRingCat.of (R ⧸ Ideal.span {a ^ m}) ⟶ s.pt) => F.hom (Ideal.Quotient.mk _ x)) s.condition
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom, Ideal.Quotient.factor_mk, hq1'] at h2
    rw [RingHom.comp_apply, RingHom.comp_apply, hq1, Ideal.Quotient.lift_mk, RingHom.comp_apply, h2, RingHom.comp_apply]
  · apply CommRingCat.hom_ext
    rw [CommRingCat.hom_ofHom]
    apply Ideal.Quotient.ringHom_ext
    ext y
    have h3 := congrArg (fun (F : CommRingCat.of (A ⧸ Ideal.span {φ a ^ m}) ⟶ s.pt) => F.hom (Ideal.Quotient.mk _ y)) h1
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom, Ideal.Quotient.factor_mk] at h3
    rw [RingHom.comp_apply, RingHom.comp_apply, Ideal.Quotient.lift_mk, RingHom.comp_apply, h3]

end AffineCartAux

theorem solution
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (r n : ℕ)
    (q : (𝒪 ⧸ Ideal.span {π ^ (n + 1)}) →+* ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})))
    (hq : q.comp (Ideal.Quotient.mk (Ideal.span {π ^ (n + 1)})) =
      (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})).comp (algebraMap 𝒪 (chartERing 𝒪 π r)))
    (q' : (𝒪 ⧸ Ideal.span {π ^ (n + 1 + 1)}) →+* ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1 + 1)})))
    (hq' : q'.comp (Ideal.Quotient.mk (Ideal.span {π ^ (n + 1 + 1)})) =
      (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1 + 1)})).comp (algebraMap 𝒪 (chartERing 𝒪 π r))) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
        (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap 𝒪 (chartERing 𝒪 π r) π) (Nat.le_succ (n + 1)))))))
      (Spec.map (CommRingCat.ofHom q))
      (Spec.map (CommRingCat.ofHom q'))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1))))))) := by
  exact AlgebraicGeometry.isPullback_SpecMap_of_isPushout _ _ _ _
    (AffineCartAux.isPushout_quotient_pow (algebraMap 𝒪 (chartERing 𝒪 π r)) π _ _ q hq q' hq')

end S_CerednikDrinfeld_FormalOmega_isPullback_Spec_map_factor_chartERing
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_isPullback_Spec_map_factor_chartERing (solution)
