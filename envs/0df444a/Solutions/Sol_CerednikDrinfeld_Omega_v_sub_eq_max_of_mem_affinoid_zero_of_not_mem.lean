-- Prove2me | solution 1 for CerednikDrinfeld.Omega.v_sub_eq_max_of_mem_affinoid_zero_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/0de85e1c-95ab-5cc5-a9ba-9dc4951cb259

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_v_sub_eq_max_of_mem_affinoid_zero_of_not_mem

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem solution
    {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (ϖ₁ : PseudoUniformizer K₀ K) {z a : K} (hz : z ∈ affinoid ϖ₁ 0) (ha : a ∉ affinoid ϖ₁ 0) :
    Valued.v (z - a) = max 1 (Valued.v a) := by
  obtain ⟨hz1, hz2⟩ := (mem_affinoid_iff' ϖ₁ 0 z).1 hz
  simp only [pow_zero] at hz1 hz2
  rcases lt_or_ge 1 (Valued.v a) with hbig | hsmall
  ·
    rw [max_eq_right hbig.le, sub_eq_add_neg, Valuation.map_add_eq_of_lt_right _ (by rw [Valuation.map_neg]; exact hz1.trans_lt hbig),
      Valuation.map_neg]
  · rw [max_eq_left hsmall]

    have hnot : ¬ ∀ t : K₀, (1 : Γ₀) ≤ Valued.v (a - algebraMap K₀ K t) := by
      intro h
      apply ha
      rw [mem_affinoid_iff']
      simp only [pow_zero]
      exact ⟨hsmall, h⟩
    push_neg at hnot
    obtain ⟨t, ht⟩ := hnot
    have hzt : Valued.v (z - algebraMap K₀ K t) = 1 := by
      apply le_antisymm _ (hz2 t)
      have hvt : Valued.v (algebraMap K₀ K t) ≤ 1 := by
        by_contra hgt
        push_neg at hgt
        have : Valued.v (a - algebraMap K₀ K t) = Valued.v (algebraMap K₀ K t) := by
          rw [sub_eq_add_neg, Valuation.map_add_eq_of_lt_right _ (by rw [Valuation.map_neg]; exact hsmall.trans_lt hgt),
            Valuation.map_neg]
        rw [this] at ht
        exact absurd (hgt.trans ht) (lt_irrefl _)
      exact (Valuation.map_sub _ _ _).trans (max_le hz1 hvt)
    have : z - a = -(a - algebraMap K₀ K t) + (z - algebraMap K₀ K t) := by ring
    rw [this, Valuation.map_add_eq_of_lt_right _ (by rw [Valuation.map_neg, hzt]; exact ht), hzt]

end S_CerednikDrinfeld_Omega_v_sub_eq_max_of_mem_affinoid_zero_of_not_mem
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_v_sub_eq_max_of_mem_affinoid_zero_of_not_mem (solution)
