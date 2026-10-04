-- Prove2me | solution 1 for DiscreteConvex.IntegralConvexity.integral_local_to_global_optimality
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-02T11:31:58.968055+00:00
-- url     : https://prove2.me/submissions/ea7f85a5-6c25-4c2b-a291-19aef70935e0

import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexity_IntegrallyConvex
import Definitions.Def_DiscreteConvex_IntegralConvexity_DomZ
import Definitions.Def_DiscreteConvex_IntegralConvexity_IndicatorVec

namespace DiscreteConvex.IntegralConvexity.Thm321Aux

open DiscreteConvex.IntegralConvexity

/-- The convex closure lies below every chord between two points of finite value. -/
theorem convexClosure_le_segment {n : ℕ} (f : (Fin n → ℤ) → WithTop ℝ) (x y : Fin n → ℤ)
    (a b : ℝ) (hfx : f x = (a : WithTop ℝ)) (hfy : f y = (b : WithTop ℝ)) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ConvexClosure f (fun i => (x i : ℝ) + t * ((y i : ℝ) - x i)) ≤
      ((a + t * (b - a) : ℝ) : EReal) := by
  apply sSup_le
  rintro v ⟨p, α, hmin, rfl⟩
  have h1 := hmin x
  have h2 := hmin y
  rw [hfx] at h1
  rw [hfy] at h2
  have h1' : α + ∑ i, p i * (x i : ℝ) ≤ a := EReal.coe_le_coe_iff.mp h1
  have h2' : α + ∑ i, p i * (y i : ℝ) ≤ b := EReal.coe_le_coe_iff.mp h2
  apply EReal.coe_le_coe_iff.mpr
  have key : ∑ i, p i * ((x i : ℝ) + t * ((y i : ℝ) - x i)) =
      ∑ i, p i * (x i : ℝ) + t * (∑ i, p i * (y i : ℝ) - ∑ i, p i * (x i : ℝ)) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [key]
  nlinarith

/-- A constant lower bound of `f` on `N(z)` is a lower bound of the local convex extension. -/
theorem le_localConvexExtension_of_const {n : ℕ} (f : (Fin n → ℤ) → WithTop ℝ)
    (z : Fin n → ℝ) (c : ℝ) (h : ∀ y ∈ IntegralNeighborhood z, (c : WithTop ℝ) ≤ f y) :
    ((c : ℝ) : EReal) ≤ LocalConvexExtension f z := by
  apply le_sSup
  refine ⟨0, c, fun y hy => ?_, by simp⟩
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
  exact WithBot.coe_le_coe.mpr (h y hy)

end DiscreteConvex.IntegralConvexity.Thm321Aux

open DiscreteConvex.IntegralConvexity DiscreteConvex.IntegralConvexity.Thm321Aux

/-- Theorem 3.21 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.94). -/
theorem solution {n : ℕ} (f : (Fin n → ℤ) → WithTop ℝ)
    (hf : IntegrallyConvex f) (x : Fin n → ℤ) (hx : x ∈ DomZ f) :
    (∀ y : Fin n → ℤ, f x ≤ f y) ↔
      (∀ Y Z : Finset (Fin n),
        f x ≤ f (fun i => x i + IndicatorVec Y i - IndicatorVec Z i)) := by
  constructor
  · intro h Y Z
    exact h _
  · intro hloc
    by_contra hcon
    push_neg at hcon
    obtain ⟨y, hy⟩ := hcon
    obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp hx
    obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hy)
    have hba : b < a := by
      rw [← ha, ← hb] at hy
      exact_mod_cast hy
    set m : ℝ := ∑ i, |(y i : ℝ) - x i| + 1 with hm
    have hsum : 0 ≤ ∑ i, |(y i : ℝ) - x i| :=
      Finset.sum_nonneg (fun i _ => abs_nonneg ((y i : ℝ) - x i))
    have hm1 : 1 ≤ m := by linarith
    set t : ℝ := 1 / m with ht
    have ht0 : 0 < t := by positivity
    have ht1 : t ≤ 1 := by
      rw [ht, div_le_one (by linarith)]
      exact hm1
    have hstep : ∀ i, |t * ((y i : ℝ) - x i)| ≤ 1 := by
      intro i
      rw [abs_mul, abs_of_pos ht0]
      have : |(y i : ℝ) - x i| ≤ ∑ j, |(y j : ℝ) - x j| :=
        Finset.single_le_sum (f := fun j => |(y j : ℝ) - x j|) (fun j _ => abs_nonneg _)
          (Finset.mem_univ i)
      rw [ht, div_mul_eq_mul_div, one_mul, div_le_one (by linarith)]
      linarith
    set z : Fin n → ℝ := fun i => (x i : ℝ) + t * ((y i : ℝ) - x i) with hz
    have hN : ∀ w ∈ IntegralNeighborhood z, (a : WithTop ℝ) ≤ f w := by
      intro w hw
      have hbox : ∀ i, x i - 1 ≤ w i ∧ w i ≤ x i + 1 := by
        intro i
        obtain ⟨h1, h2⟩ := hw i
        have habs := abs_le.mp (hstep i)
        constructor
        · have : x i - 1 ≤ ⌊z i⌋ := by
            rw [Int.le_floor]
            push_cast
            simp only [hz]
            linarith
          omega
        · have : ⌈z i⌉ ≤ x i + 1 := by
            rw [Int.ceil_le]
            push_cast
            simp only [hz]
            linarith
          omega
      have hw_eq : w = fun i => x i + IndicatorVec (Finset.univ.filter (fun i => w i = x i + 1)) i
          - IndicatorVec (Finset.univ.filter (fun i => w i = x i - 1)) i := by
        funext i
        simp only [IndicatorVec, Finset.mem_filter, Finset.mem_univ, true_and]
        have := hbox i
        split_ifs <;> omega
      rw [ha, hw_eq]
      exact hloc _ _
    have hlow := le_localConvexExtension_of_const f z a hN
    have hup := convexClosure_le_segment f x y a b ha.symm hb.symm t ht0.le ht1
    rw [hf z] at hlow
    have := EReal.coe_le_coe_iff.mp (hlow.trans hup)
    nlinarith

