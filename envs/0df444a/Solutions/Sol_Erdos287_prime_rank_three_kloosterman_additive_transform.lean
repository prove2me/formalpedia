-- Prove2me | solution 1 for Erdos287.prime_rank_three_kloosterman_additive_transform
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T20:46:00.857682+00:00
-- url     : https://prove2.me/submissions/cc39c984-ad67-4247-965a-a7c000a8a66a

import Mathlib

set_option autoImplicit false

open Finset

private theorem unit_orthogonality (p : ℕ) [Fact p.Prime] (c : ZMod p) :
    (∑ u : (ZMod p)ˣ, ZMod.stdAddChar (c * (u : ZMod p))) =
      (if c = 0 then (p : ℂ) else 0) - 1 := by
  classical
  let f : ZMod p → ℂ := fun x => ZMod.stdAddChar (c * x)
  have hfull : (∑ x : ZMod p, f x) = if c = 0 then (p : ℂ) else 0 := by
    by_cases hc : c = 0
    · simp [f, hc, ZMod.card]
    · simpa [f, hc, AddChar.mulShift_apply] using
        AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar p hc)
  have hunits :
      (∑ u : (ZMod p)ˣ, f (u : ZMod p)) =
        ∑ x ∈ ({0} : Finset (ZMod p))ᶜ, f x := by
    calc
      _ = ∑ x : {x : ZMod p // x ≠ 0}, f x :=
        Fintype.sum_equiv unitsEquivNeZero _ _ (fun _ => rfl)
      _ = _ := (Finset.sum_subtype _ (fun x => by simp) f).symm
  rw [show (∑ u : (ZMod p)ˣ, ZMod.stdAddChar (c * (u : ZMod p))) =
    ∑ u : (ZMod p)ˣ, f (u : ZMod p) from rfl, hunits]
  have hsplit := ({0} : Finset (ZMod p)).sum_compl_add_sum f
  simp [f] at hsplit
  rw [← hfull]
  exact eq_sub_of_add_eq hsplit

/-- The additive Fourier transform of the raw rank-three prime Kloosterman
sum is a raw rank-two sum times the prime, with an exact constant term.
The argument `t` is the Fourier frequency divided by the unit dilation. -/
theorem solution (p : ℕ) [Fact p.Prime] (t : ZMod p) :
    (∑ u : (ZMod p)ˣ, ∑ v : (ZMod p)ˣ, ∑ w : (ZMod p)ˣ,
      ZMod.stdAddChar ((u : ZMod p) + (v : ZMod p) +
        (1 - t * (u : ZMod p) * (v : ZMod p)) * (w : ZMod p))) =
      (p : ℂ) * (if t = 0 then 0 else
        ∑ u : (ZMod p)ˣ, ZMod.stdAddChar ((u : ZMod p) + (t * (u : ZMod p))⁻¹)) - 1 := by
  classical
  let χ : AddChar (ZMod p) ℂ := ZMod.stdAddChar
  have hone : (∑ u : (ZMod p)ˣ, χ (u : ZMod p)) = -1 := by
    simpa [χ] using unit_orthogonality p (1 : ZMod p)
  have hsum :
      (∑ u : (ZMod p)ˣ, ∑ v : (ZMod p)ˣ, χ ((u : ZMod p) + (v : ZMod p))) = 1 := by
    simp only [AddChar.map_add_eq_mul, ← mul_sum, hone]
    rw [← sum_mul, hone, neg_mul_neg, one_mul]
  have hrow (u : (ZMod p)ˣ) :
      (∑ v : (ZMod p)ˣ, if t * (u : ZMod p) * (v : ZMod p) = 1 then
        χ ((u : ZMod p) + (v : ZMod p)) else 0) =
        if t = 0 then 0 else χ ((u : ZMod p) + (t * (u : ZMod p))⁻¹) := by
    by_cases ht : t = 0
    · simp [ht]
    have hc : t * (u : ZMod p) ≠ 0 := mul_ne_zero ht (Units.ne_zero u)
    let v₀ : (ZMod p)ˣ := Units.mk0 ((t * (u : ZMod p))⁻¹) (inv_ne_zero hc)
    have heq (v : (ZMod p)ˣ) : t * (u : ZMod p) * (v : ZMod p) = 1 ↔ v = v₀ := by
      rw [mul_eq_one_iff_inv_eq₀ hc, eq_comm]
      change (v : ZMod p) = (v₀ : ZMod p) ↔ v = v₀
      exact ⟨fun h => Units.ext h, fun h => congrArg (fun w : (ZMod p)ˣ => (w : ZMod p)) h⟩
    rw [if_neg ht]
    simp_rw [heq]
    rw [sum_ite_eq', if_pos (mem_univ _)]
    rfl
  have hform (u v : (ZMod p)ˣ) :
      χ ((u : ZMod p) + (v : ZMod p)) *
        ((if 1 - t * (u : ZMod p) * (v : ZMod p) = 0 then (p : ℂ) else 0) - 1) =
        (p : ℂ) * (if t * (u : ZMod p) * (v : ZMod p) = 1 then
          χ ((u : ZMod p) + (v : ZMod p)) else 0) -
          χ ((u : ZMod p) + (v : ZMod p)) := by
    simp only [sub_eq_zero, eq_comm (a := (1 : ZMod p))]
    split_ifs <;> ring
  change (∑ u : (ZMod p)ˣ, ∑ v : (ZMod p)ˣ, ∑ w : (ZMod p)ˣ, χ _) = _
  simp_rw [AddChar.map_add_eq_mul χ (_ + _) (_ * _), ← mul_sum]
  change (∑ u : (ZMod p)ˣ, ∑ v : (ZMod p)ˣ, χ (_ + _) *
    ∑ w : (ZMod p)ˣ, ZMod.stdAddChar (_ * (w : ZMod p))) = _
  simp_rw [unit_orthogonality, hform, sum_sub_distrib, hsum, ← mul_sum, hrow]
  by_cases ht : t = 0
  · simp only [if_pos ht, sum_const_zero, mul_zero]
  · simp only [if_neg ht]
    rfl

