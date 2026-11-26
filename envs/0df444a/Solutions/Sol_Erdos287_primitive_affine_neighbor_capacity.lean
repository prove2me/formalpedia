-- Prove2me | solution 1 for Erdos287.primitive_affine_neighbor_capacity
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T12:23:41.2108+00:00
-- url     : https://prove2.me/submissions/90cabe6e-8326-4fed-96e8-7aef6235fea6

import Mathlib

open Finset

set_option autoImplicit false

/-- For a fixed affine form and a fixed cofactor, the two signs give at
most two primitive affine forms producing a consecutive multiple. -/
theorem solution (S : Finset (ℕ × ℕ)) (a b L U : ℕ)
    (hprimitive : ∀ q ∈ S, q.1.Coprime q.2)
    (hneighbor : ∀ q ∈ S, ∃ (c d : ℕ) (side : Bool), c ∈ Finset.Icc L U ∧ 0 < d ∧
      c * a = d * q.1 ∧ (d : ℤ) * q.2 = (c : ℤ) * b + (if side then 1 else -1)) :
    S.card ≤ 2 * (U + 1 - L) := by
  classical
  choose! c d side hc hd hlinear hconstant using hneighbor
  let code (q : ℕ × ℕ) := (c q, side q)
  have hmap : Set.MapsTo code (↑S : Set (ℕ × ℕ))
      (↑(Icc L U ×ˢ (univ : Finset Bool)) : Set (ℕ × Bool)) := by
    intro q hq
    exact mem_product.mpr ⟨hc q hq, mem_univ _⟩
  have hinj : Set.InjOn code (↑S : Set (ℕ × ℕ)) := by
    intro q hq r hr he
    have hcof : c q = c r := congrArg Prod.fst he
    have hsign : side q = side r := congrArg Prod.snd he
    have hfirst : d q * q.1 = d r * r.1 := by
      rw [← hlinear q hq, ← hlinear r hr, hcof]
    have hsecond : d q * q.2 = d r * r.2 := by
      exact_mod_cast (show (d q : ℤ) * q.2 = (d r : ℤ) * r.2 by
        rw [hconstant q hq, hconstant r hr, hcof, hsign])
    have hmult := congrArg₂ Nat.gcd hfirst hsecond
    simp only [Nat.gcd_mul_left, (hprimitive q hq).gcd_eq_one,
      (hprimitive r hr).gcd_eq_one, mul_one] at hmult
    rw [← hmult] at hfirst hsecond
    exact Prod.ext (Nat.eq_of_mul_eq_mul_left (hd q hq) hfirst)
      (Nat.eq_of_mul_eq_mul_left (hd q hq) hsecond)
  calc
    S.card ≤ (Icc L U ×ˢ (univ : Finset Bool)).card := card_le_card_of_injOn code hmap hinj
    _ = 2 * (U + 1 - L) := by simp [mul_comm]

