-- Prove2me | solution 1 for GaloisRep.isPrincipalIdealRing_ratLocalizedAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/d02046b3-d124-5ba0-8ae3-9340f3a7dbab

import Definitions.Def_GaloisRep_Flat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRep_isPrincipalIdealRing_ratLocalizedAt

namespace SolB0A

open GaloisRep

private lemma mem_ratLocalizedAt_iff {p : ℕ} {q : ℚ} :
    q ∈ ratLocalizedAt p ↔ q.den.Coprime p := Iff.rfl

private def ratLocalizedAtMonoid (p : ℕ) : Submonoid ℤ where
  carrier := {z : ℤ | z ≠ 0 ∧ ((z : ℚ)⁻¹ ∈ ratLocalizedAt p)}
  one_mem' := by
    refine ⟨one_ne_zero, ?_⟩
    rw [Int.cast_one, inv_one, mem_ratLocalizedAt_iff]
    simp
  mul_mem' := by
    rintro a b ⟨ha0, ha⟩ ⟨hb0, hb⟩
    refine ⟨mul_ne_zero ha0 hb0, ?_⟩
    rw [Int.cast_mul, mul_inv]
    exact mul_mem ha hb

private lemma natCast_den_mem_ratLocalizedAtMonoid {p : ℕ} {q : ℚ} (hq : q ∈ ratLocalizedAt p) :
    ((q.den : ℤ)) ∈ ratLocalizedAtMonoid p := by
  refine ⟨Int.natCast_ne_zero.mpr q.den_nz, ?_⟩
  rw [mem_ratLocalizedAt_iff, Int.cast_natCast, Rat.inv_natCast_den_of_pos q.pos]
  exact hq

private scoped instance isLocalization (p : ℕ) :
    IsLocalization (ratLocalizedAtMonoid p) (ratLocalizedAt p) :=
  (isLocalization_iff (ratLocalizedAtMonoid p) (ratLocalizedAt p)).mpr
    ⟨by
      rintro ⟨z, hz0, hzi⟩
      refine isUnit_iff_exists_inv.mpr ⟨⟨(z : ℚ)⁻¹, hzi⟩, Subtype.ext ?_⟩
      push_cast
      exact mul_inv_cancel₀ (Int.cast_ne_zero.mpr hz0),
    by
      rintro ⟨x, hx⟩
      refine ⟨⟨x.num, ⟨(x.den : ℤ), natCast_den_mem_ratLocalizedAtMonoid hx⟩⟩, Subtype.ext ?_⟩
      push_cast
      exact (eq_div_iff (by exact_mod_cast x.den_nz)).mp (Rat.num_div_den x).symm,
    by
      intro a b h
      obtain rfl : a = b := Int.cast_injective (show ((a : ℚ)) = (b : ℚ) by
        exact_mod_cast congrArg Subtype.val h)
      exact ⟨1, rfl⟩⟩

end SolB0A
p2m_reactivate "P2MW.S_GaloisRep_isPrincipalIdealRing_ratLocalizedAt.SolB0A"

theorem solution (p : ℕ) :
    IsPrincipalIdealRing (GaloisRep.ratLocalizedAt p) := by
  refine ⟨fun I => ?_⟩
  obtain ⟨d, hd⟩ := Submodule.IsPrincipal.principal (Ideal.under ℤ I)
  refine ⟨⟨algebraMap ℤ (GaloisRep.ratLocalizedAt p) d, ?_⟩⟩
  conv_lhs => rw [← IsLocalization.map_under (SolB0A.ratLocalizedAtMonoid p)
    (GaloisRep.ratLocalizedAt p) I]
  rw [hd]
  change Ideal.map _ (Ideal.span {d}) = _
  rw [Ideal.map_span, Set.image_singleton]

#print axioms solution

end S_GaloisRep_isPrincipalIdealRing_ratLocalizedAt
end P2MW
export P2MW.S_GaloisRep_isPrincipalIdealRing_ratLocalizedAt (solution)
