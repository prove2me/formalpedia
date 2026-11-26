-- Prove2me | solution 1 for Erdos287.shared_prime_kloosterman_correlation_by_rank_two_sums
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T20:53:22.769939+00:00
-- url     : https://prove2.me/submissions/ab06b1c4-bf7c-4b78-a701-58f408374888

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

/-- The shared-prime rank-three correlation is an additive difference of the
two rank-two distributions, with an exact correction from the unit mask. -/
theorem solution (p : ℕ) [Fact p.Prime] (b₁ b₂ t : ZMod p) :
    let U := (ZMod p)ˣ × (ZMod p)ˣ
    let σ : U → ZMod p := fun u => (u.1 : ZMod p) + (u.2 : ZMod p)
    let π : U → ZMod p := fun u => (u.1 : ZMod p) * (u.2 : ZMod p)
    let A : ZMod p → ℂ := fun ℓ =>
      ∑ u : U, if b₁ / π u = ℓ then ZMod.stdAddChar (σ u) else 0
    let B : ZMod p → ℂ := fun ℓ =>
      ∑ v : U, if b₂ / π v = ℓ then ZMod.stdAddChar (-σ v) else 0
    (∑ u : U, ∑ v : U, ∑ h : (ZMod p)ˣ,
      ZMod.stdAddChar (σ u - σ v + (b₁ / π u - b₂ / π v - t) * (h : ZMod p))) =
      (p : ℂ) * (∑ ℓ : ZMod p, A ℓ * B (ℓ - t)) - 1 := by
  classical
  intro U σ π A B
  let χ : AddChar (ZMod p) ℂ := ZMod.stdAddChar
  have hpos : (∑ x : (ZMod p)ˣ, χ (x : ZMod p)) = -1 := by
    simpa [χ] using unit_orthogonality p (1 : ZMod p)
  have hneg : (∑ x : (ZMod p)ˣ, χ (-(x : ZMod p))) = -1 := by
    simpa [χ] using unit_orthogonality p (-1 : ZMod p)
  have hspos : (∑ u : U, χ (σ u)) = 1 := by
    change (∑ u : (ZMod p)ˣ × (ZMod p)ˣ, χ ((u.1 : ZMod p) + (u.2 : ZMod p))) = 1
    rw [Fintype.sum_prod_type]
    simp only [AddChar.map_add_eq_mul, ← mul_sum, hpos, ← sum_mul, neg_mul_neg, one_mul]
  have hsneg : (∑ v : U, χ (-σ v)) = 1 := by
    change (∑ u : (ZMod p)ˣ × (ZMod p)ˣ, χ (-((u.1 : ZMod p) + (u.2 : ZMod p)))) = 1
    rw [Fintype.sum_prod_type]
    simp only [neg_add, AddChar.map_add_eq_mul, ← mul_sum, hneg, ← sum_mul, neg_mul_neg, one_mul]
  have hall : (∑ u : U, ∑ v : U, χ (σ u - σ v)) = 1 := by
    simp only [sub_eq_add_neg, AddChar.map_add_eq_mul, ← mul_sum, hsneg, mul_one, hspos]
  have hconstraint (u v : U) :
      (∑ ℓ : ZMod p,
        (if b₁ / π u = ℓ then χ (σ u) else 0) *
        (if b₂ / π v = ℓ - t then χ (-σ v) else 0)) =
      if b₁ / π u - b₂ / π v - t = 0 then χ (σ u - σ v) else 0 := by
    simp only [ite_mul, zero_mul, eq_comm (a := b₁ / π u), sum_ite_eq', mem_univ, if_true]
    have heq : (b₂ / π v = b₁ / π u - t) ↔ b₁ / π u - b₂ / π v - t = 0 := by
      constructor <;> intro hh <;> linear_combination -hh
    by_cases h : b₂ / π v = b₁ / π u - t
    · rw [if_pos h, if_pos (heq.mp h), sub_eq_add_neg]
      exact (AddChar.map_add_eq_mul χ _ _).symm
    · rw [if_neg h, if_neg (fun hn => h (heq.mpr hn)), mul_zero]
  have hprod : (∑ ℓ : ZMod p, A ℓ * B (ℓ - t)) =
      ∑ u : U, ∑ v : U, if b₁ / π u - b₂ / π v - t = 0 then χ (σ u - σ v) else 0 := by
    change (∑ ℓ : ZMod p, (∑ u : U, _) * (∑ v : U, _)) = _
    simp_rw [sum_mul, mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro u hu
    rw [sum_comm]
    exact sum_congr rfl (fun v _ => hconstraint u v)
  have hrow (u v : U) :
      (∑ h : (ZMod p)ˣ, χ (σ u - σ v + (b₁ / π u - b₂ / π v - t) * (h : ZMod p))) =
      (p : ℂ) * (if b₁ / π u - b₂ / π v - t = 0 then χ (σ u - σ v) else 0) -
        χ (σ u - σ v) := by
    simp only [AddChar.map_add_eq_mul, ← mul_sum]
    change χ (σ u - σ v) * (∑ h : (ZMod p)ˣ, ZMod.stdAddChar (_ * (h : ZMod p))) = _
    rw [unit_orthogonality]
    split_ifs <;> ring
  change (∑ u : U, ∑ v : U, ∑ h : (ZMod p)ˣ, χ _) = _
  simp_rw [hrow, sum_sub_distrib, ← mul_sum, hall, hprod]

