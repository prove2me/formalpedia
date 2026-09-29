-- Prove2me | solution 1 for FormalGroup.IsDrinfeldBasisAdic.exists_maximalIdeal_eq_span_pair_and_eval_eq_zero_of_lawIso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/d86e9a83-2457-5497-9791-d61542feb40a

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Theorems.Thm_FormalGroup_LawIso_exists_symm_subst_eq_X
import Theorems.Thm_FormalGroup_IsDrinfeldBasisAdic_map_iso
import Theorems.Thm_FormalGroup_IsDrinfeldBasisAdic_evalSeries_nthSeries_eq_zero
import Theorems.Thm_FormalGroup_exists_ringHom_evalSeries_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FormalGroup_IsDrinfeldBasisAdic_exists_maximalIdeal_eq_span_pair_and_eval_eq_zero_of_lawIso
p2m_attr_erase "instance" "MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid MvFormalGroup.instIsCommAddMv MvFormalGroup.instIsCommOfFormalGroup"
p2m_attr_erase "simp" "MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg' MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast MvFormalGroup.mk.injEq MvFormalGroup.nthSeries_zero MvFormalGroup.Hom.mk.sizeOf_spec MvFormalGroup.Hom.mk.injEq MvFormalGroup.mk.sizeOf_spec MvFormalGroup.e3_one MvFormalGroup.e3_zero MvFormalGroup.e3_two MvFormalGroup.e2_one MvFormalGroup.e2_zero FormalGroup.LawHom.ofMvHom_series MvFormalGroup.e1_apply FormalGroup.LawHom.toMvHom_toPowerSeries"

set_option autoImplicit false

open FormalGroup IsLocalRing

namespace DW2RIT

theorem isUnit_add_of_mem_maximalIdeal {R : Type*} [CommRing R] [IsLocalRing R] {m u : R}
    (hm : m ∈ maximalIdeal R) (hu : IsUnit u) : IsUnit (m + u) := by
  by_contra h
  have h' : m + u ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr h)
  have hu' : u ∈ maximalIdeal R := by
    have := Ideal.sub_mem _ h' hm
    rwa [add_sub_cancel_left] at this
  exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hu')) hu

end DW2RIT

theorem solution
    {R : Type*} [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]
    (F' F : FormalGroup R) (ψ : FormalGroup.LawIso F' F)
    (q : ℕ) (hq : 2 ≤ q) (x₀ x₁ : R) (hx₀ : x₀ ∈ maximalIdeal R) (hx₁ : x₁ ∈ maximalIdeal R)
    (hD : F.IsDrinfeldBasisAdic (maximalIdeal R) q x₀ x₁)
    (hmax : maximalIdeal R = Ideal.span {x₀, x₁})
    (P : Polynomial R) (U : PowerSeries R) (hU : IsUnit U)
    (hP : F'.nthSeries q = (P : PowerSeries R) * U) :
    ∃ y₀ y₁ : R, y₀ ∈ maximalIdeal R ∧ y₁ ∈ maximalIdeal R ∧
      maximalIdeal R = Ideal.span {y₀, y₁} ∧ P.eval y₀ = 0 ∧ P.eval y₁ = 0 := by
  obtain ⟨ψ', -, -⟩ := FormalGroup.LawIso.exists_symm_subst_eq_X ψ

  have hD' := FormalGroup.IsDrinfeldBasisAdic.map_iso (maximalIdeal R) F F' ψ' q x₀ x₁ hx₀ hx₁ hD

  have key : ∀ x ∈ maximalIdeal R, ∃ v : R, IsUnit v ∧ ψ'.toLawHom.appAdic (maximalIdeal R) x = x * v := by
    intro x hx
    obtain ⟨e, he, hep⟩ := FormalGroup.exists_ringHom_evalSeries_eq (maximalIdeal R) x hx
    obtain ⟨g, hg⟩ := PowerSeries.X_dvd_iff.mpr ψ'.constantCoeff_series
    have heX : e PowerSeries.X = x := by rw [← Polynomial.coe_X, hep, Polynomial.eval_X]
    have heC : ∀ c : R, e (PowerSeries.C c) = c := fun c => by rw [← Polynomial.coe_C, hep, Polynomial.eval_C]
    have hc1 : PowerSeries.constantCoeff g = PowerSeries.coeff 1 ψ'.series := by
      rw [hg, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← PowerSeries.coeff_succ_X_mul 0 g]
    refine ⟨e g, ?_, ?_⟩
    · rw [PowerSeries.eq_X_mul_shift_add_const g, map_add, map_mul, heX, heC]
      exact DW2RIT.isUnit_add_of_mem_maximalIdeal (Ideal.mul_mem_right _ _ hx) (hc1 ▸ ψ'.isUnit_coeff_one)
    · unfold FormalGroup.LawHom.appAdic FormalGroup.LawHom.app
      rw [he, hg, map_mul, heX]
  obtain ⟨v₀, hv₀, hy₀⟩ := key x₀ hx₀
  obtain ⟨v₁, hv₁, hy₁⟩ := key x₁ hx₁
  have hy₀m : ψ'.toLawHom.appAdic (maximalIdeal R) x₀ ∈ maximalIdeal R := by
    rw [hy₀]; exact Ideal.mul_mem_right _ _ hx₀
  have hy₁m : ψ'.toLawHom.appAdic (maximalIdeal R) x₁ ∈ maximalIdeal R := by
    rw [hy₁]; exact Ideal.mul_mem_right _ _ hx₁

  have hspan : maximalIdeal R =
      Ideal.span {ψ'.toLawHom.appAdic (maximalIdeal R) x₀, ψ'.toLawHom.appAdic (maximalIdeal R) x₁} := by
    apply le_antisymm
    · refine hmax.le.trans ?_
      rw [Ideal.span_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · refine Ideal.mem_span_pair.mpr ⟨(hv₀.unit⁻¹ : Rˣ), 0, ?_⟩
        rw [hy₀, zero_mul, _root_.add_zero, mul_comm, mul_assoc, IsUnit.mul_val_inv, mul_one]
      · refine Ideal.mem_span_pair.mpr ⟨0, (hv₁.unit⁻¹ : Rˣ), ?_⟩
        rw [hy₁, zero_mul, _root_.zero_add, mul_comm, mul_assoc, IsUnit.mul_val_inv, mul_one]
    · rw [Ideal.span_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact hy₀m
      · exact hy₁m

  have hroot : ∀ y ∈ maximalIdeal R,
      (letI : WithIdeal R := ⟨maximalIdeal R⟩; FormalGroup.evalSeries (F'.nthSeries q) y) = 0 → P.eval y = 0 := by
    intro y hy h0
    obtain ⟨e, he, hep⟩ := FormalGroup.exists_ringHom_evalSeries_eq (maximalIdeal R) y hy
    rw [he, hP, map_mul, hep] at h0
    exact (hU.map e).mul_left_eq_zero.mp h0
  obtain ⟨h0, h1⟩ := FormalGroup.IsDrinfeldBasisAdic.evalSeries_nthSeries_eq_zero (maximalIdeal R) F' q hq _ _
    hy₀m hy₁m hD'
  exact ⟨_, _, hy₀m, hy₁m, hspan, hroot _ hy₀m h0, hroot _ hy₁m h1⟩

end S_FormalGroup_IsDrinfeldBasisAdic_exists_maximalIdeal_eq_span_pair_and_eval_eq_zero_of_lawIso
end P2MW
export P2MW.S_FormalGroup_IsDrinfeldBasisAdic_exists_maximalIdeal_eq_span_pair_and_eval_eq_zero_of_lawIso (solution)
