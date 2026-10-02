-- Prove2me | solution 1 for DiscreteConvex.IntegralConvexityC.prop_3_26_integrally_convex_set_hole_free
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T04:22:17.761924+00:00
-- url     : https://prove2.me/submissions/c39a1da5-fd08-4b2a-a39b-5db1790a61d2

import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityC_IntegrallyConvexSet
import Definitions.Def_DiscreteConvex_IntegralConvexityC_HoleFree

set_option autoImplicit false

namespace DiscreteConvex.IntegralConvexityC

theorem hf0f6_cc_le_zero {n : ℕ} (S : Set (Fin n → ℤ)) (X : Fin n → ℝ)
    (hX : X ∈ ConvexClosureSet S) : ConvexClosure (IndicatorZ S) X ≤ 0 := by
  unfold ConvexClosure
  refine sSup_le ?_
  rintro v ⟨p, a, h, rfl⟩
  have hsub : EmbedZR '' S ⊆ {w : Fin n → ℝ | (∑ i, p i * w i) ≤ -a} := by
    rintro _ ⟨y, hy, rfl⟩
    have h1 := h y
    simp only [IndicatorZ, hy, if_true] at h1
    have h1' : ((a + ∑ i, p i * (y i : ℝ) : ℝ) : EReal) ≤ ((0 : ℝ) : EReal) := h1
    have h2 : (a + ∑ i, p i * (y i : ℝ)) ≤ 0 := EReal.coe_le_coe_iff.mp h1'
    show (∑ i, p i * ((y i : ℝ))) ≤ -a
    linarith
  have hconv : Convex ℝ {w : Fin n → ℝ | (∑ i, p i * w i) ≤ -a} := by
    refine convex_halfSpace_le ?_ (-a)
    constructor
    · intro x y
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    · intro c x
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => by ring
  have hmem := convexHull_min hsub hconv hX
  have h3 : (a + ∑ i, p i * X i) ≤ 0 := by
    have : (∑ i, p i * X i) ≤ -a := hmem
    linarith
  exact_mod_cast h3

theorem hf0f6_one_le_lce {n : ℕ} (S : Set (Fin n → ℤ)) (x : Fin n → ℤ) (hx : x ∉ S) :
    (1 : EReal) ≤ LocalConvexExtension (IndicatorZ S) (EmbedZR x) := by
  unfold LocalConvexExtension
  refine le_sSup ⟨0, 1, ?_, ?_⟩
  · intro y hy
    have hyx : y = x := by
      funext i
      have := hy i
      simp only [EmbedZR, Int.floor_intCast, Int.ceil_intCast] at this
      omega
    subst hyx
    simp only [IndicatorZ, hx, if_false]
    exact le_top
  · simp

theorem hf0f6_main {n : ℕ} (S : Set (Fin n → ℤ))
    (hS : IntegrallyConvexSet S) : HoleFree S := by
  intro x
  constructor
  · intro hx
    exact subset_convexHull ℝ _ ⟨x, hx, rfl⟩
  · intro hX
    by_contra hx
    have h1 := hf0f6_one_le_lce S x hx
    have h2 := hf0f6_cc_le_zero S (EmbedZR x) hX
    have h3 := hS (EmbedZR x)
    rw [h3] at h1
    have : (1 : EReal) ≤ 0 := h1.trans h2
    exact absurd this (by norm_num)

end DiscreteConvex.IntegralConvexityC

open DiscreteConvex.IntegralConvexityC in
theorem solution {n : ℕ} (S : Set (Fin n → ℤ))
    (hS : IntegrallyConvexSet S) : HoleFree S := by
  exact DiscreteConvex.IntegralConvexityC.hf0f6_main S hS
