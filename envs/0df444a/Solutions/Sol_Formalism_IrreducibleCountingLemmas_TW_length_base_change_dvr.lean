-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.TW.length_base_change_dvr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:52:03.931809+00:00
-- url     : https://prove2.me/submissions/6e3cb53a-b6c7-4af5-8756-8c131ac78fb3

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_CentralIdempotentIntegral
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_TWLengthBaseChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.TW
namespace Formalism.IrreducibleCountingLemmas.TW
theorem _root_.solution : LengthBaseChange := by
  intro O O' _ _ _ _ _ _ _ ϖ ϖ' u e hϖ hϖ' hmap he X _ _ _

  have hne : algebraMap O O' ϖ ≠ 0 := by
    rw [hmap]
    exact mul_ne_zero u.ne_zero (pow_ne_zero _ hϖ'.ne_zero)

  have hinj : Function.Injective (algebraMap O O') := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0
    obtain ⟨k, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
    rw [map_mul, map_pow] at hx
    rcases mul_eq_zero.mp hx with h | h
    · exact ((v.isUnit.map (algebraMap O O')).ne_zero) h
    · exact pow_ne_zero k hne h

  have hloc : IsLocalHom (algebraMap O O') := by
    refine ⟨fun x hx => ?_⟩
    by_contra hnu
    have hmem : x ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal x).mpr hnu
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hmem
    obtain ⟨y, rfl⟩ := hmem
    rw [map_mul] at hx
    have h1 : IsUnit (algebraMap O O' ϖ) := isUnit_of_mul_isUnit_left hx
    rw [hmap] at h1
    have h2 : IsUnit (ϖ' ^ e) := isUnit_of_mul_isUnit_right h1
    exact hϖ'.not_isUnit ((isUnit_pow_iff he.ne').mp h2)
  have : FaithfulSMul O O' := (faithfulSMul_iff_algebraMap_injective O O').mpr hinj
  have : Module.IsTorsionFree O O' := inferInstance
  have : Module.Flat O O' := inferInstance
  rw [IsLocalRing.length_baseChange O O' X, hϖ.maximalIdeal_eq, Ideal.map_span,
    Set.image_singleton, hmap]
  have hord : Module.length O' (O' ⧸ Ideal.span {(u : O') * ϖ' ^ e}) = (e : ℕ∞) := by
    change Ring.ord O' ((u : O') * ϖ' ^ e) = _
    rw [Ring.ord_mul_of_isUnit_left u.isUnit,
      Ring.ord_pow (mem_nonZeroDivisors_of_ne_zero hϖ'.ne_zero), Ring.ord_of_irreducible hϖ']
    simp
  rw [hord, mul_comm]
end Formalism.IrreducibleCountingLemmas.TW
