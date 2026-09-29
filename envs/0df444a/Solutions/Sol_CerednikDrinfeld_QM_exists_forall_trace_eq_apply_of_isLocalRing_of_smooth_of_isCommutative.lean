-- Prove2me | solution 1 for CerednikDrinfeld.QM.exists_forall_trace_eq_apply_of_isLocalRing_of_smooth_of_isCommutative
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/4607c7cf-b8a5-5148-a063-d803a23a7530

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import Theorems.Thm_CerednikDrinfeld_QM_exists_cover_forall_trace_eq_algebraMap_of_smooth_of_isCommutative
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_exists_forall_trace_eq_apply_of_isLocalRing_of_smooth_of_isCommutative
p2m_attr_erase "instance" "MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid MvFormalGroup.instIsCommAddMv"
p2m_attr_erase "simp" "MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg' MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast MvFormalGroup.mk.injEq MvFormalGroup.nthSeries_zero MvFormalGroup.Hom.mk.sizeOf_spec MvFormalGroup.Hom.mk.injEq MvFormalGroup.mk.sizeOf_spec"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    {R : Type u} [CommRing R] [IsLocalRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (hL : L.IsCommutative) (hf : Smooth f)
    (act : ↥Λ → (A ⟶ A)) (act_over : ∀ x : ↥Λ, act x ≫ f = f)
    (act_hom : ∀ (x : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      pushPt (act x) (act_over x) (L.mul t P Q) = L.mul t (pushPt (act x) (act_over x) P) (pushPt (act x) (act_over x) Q)) :
    ∃ t : ↥Λ → R,
      ∀ (k : Type u) [Field k] (sk : R →+* k) (x : ↥Λ)
        (V : Type u) [AddCommGroup V] [Module k V] (τ : V → SchemeHomOver (tangentBase k sk) f),
        Function.Injective τ →
        (∀ P : SchemeHomOver (tangentBase k sk) f, P ∈ Set.range τ ↔ IsTangentVector L k sk P) →
        (∀ v w : V, τ (v + w) = L.mul (tangentBase k sk) (τ v) (τ w)) →
        (∀ (c : k) (v : V), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1) →
        ∀ Φ : V →ₗ[k] V, (∀ v : V, τ (Φ v) = pushPt (act x) (act_over x) (τ v)) →
          LinearMap.trace k V Φ = sk (t x) := by
  classical
  obtain ⟨n, c, hspan, hloc⟩ :=
    CerednikDrinfeld.QM.exists_cover_forall_trace_eq_algebraMap_of_smooth_of_isCommutative L hL hf act act_over act_hom

  have hex : ∃ i, IsUnit (c i) := by
    by_contra h
    push_neg at h
    have hle : Ideal.span (Set.range c) ≤ IsLocalRing.maximalIdeal R := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact (IsLocalRing.mem_maximalIdeal _).mpr (h i)
    rw [hspan] at hle
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top (top_le_iff.mp hle)
  obtain ⟨i, hi⟩ := hex
  haveI : IsLocalization.Away (c i) R :=
    IsLocalization.away_of_isUnit_of_bijective R hi Function.bijective_id
  obtain ⟨t, ht⟩ := hloc i R
  refine ⟨t, ?_⟩
  intro k _ sk x V _ _ τ hinj hrange hadd hsmul Φ hΦ
  letI : Algebra R k := sk.toAlgebra
  have hcomp : (algebraMap R k).comp (algebraMap R R) = sk := RingHom.ext fun r => rfl
  exact ht k sk hcomp x V τ hinj hrange hadd hsmul Φ hΦ

end S_CerednikDrinfeld_QM_exists_forall_trace_eq_apply_of_isLocalRing_of_smooth_of_isCommutative
end P2MW
export P2MW.S_CerednikDrinfeld_QM_exists_forall_trace_eq_apply_of_isLocalRing_of_smooth_of_isCommutative (solution)
