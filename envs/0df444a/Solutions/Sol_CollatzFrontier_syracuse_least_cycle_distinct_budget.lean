-- Prove2me | solution 1 for CollatzFrontier.syracuse_least_cycle_distinct_budget
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-10-04T17:44:44.508701+00:00
-- url     : https://prove2.me/submissions/8c188af5-f0ae-4343-b8c0-4a1447008e8b

import Definitions.Def_syracuseStep
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Factorization.Basic

set_option autoImplicit false

namespace CollatzFrontierAux
open scoped BigOperators

/-- Every Syracuse step has an odd result, since its argument to `ordCompl` is positive. -/
theorem syracuseStep_odd (n : ℕ) : Odd (syracuseStep n) := by
  apply Nat.odd_iff.mpr
  have hnot : ¬ 2 ∣ syracuseStep n :=
    Nat.not_dvd_ordCompl Nat.prime_two (show 3 * n + 1 ≠ 0 by omega)
  have hne : syracuseStep n % 2 ≠ 0 := by
    intro hzero
    exact hnot (Nat.dvd_of_mod_eq_zero hzero)
  have hlt := Nat.mod_lt (syracuseStep n) (show 0 < 2 by decide)
  omega

theorem syracuse_iterate_odd (n : ℕ) (hn : Odd n) (i : ℕ) :
    Odd (syracuseStep^[i] n) := by
  cases i with
  | zero => exact hn
  | succ i =>
      rw [Function.iterate_succ_apply']
      exact syracuseStep_odd _

/-- Positivity is preserved along a positive Syracuse orbit. -/
theorem syracuse_iterate_pos (m i : ℕ) (hm : 0 < m) : 0 < syracuseStep^[i] m := by
  cases i with
  | zero => exact hm
  | succ i =>
      rw [Function.iterate_succ_apply']
      exact Nat.ordCompl_pos 2 (by omega)

/-- Distinct sorted odd naturals above `B` are spaced at least two apart. -/
theorem odd_finset_rank_lower (s : Finset ℕ) (B : ℕ)
    (hodd : ∀ x ∈ s, Odd x) (hB : ∀ x ∈ s, B ≤ x) :
    ∀ j (hj : j < s.card), B + 2 * j ≤ s.orderEmbOfFin rfl ⟨j, hj⟩ := by
  intro j
  induction j with
  | zero =>
      intro hj
      simpa using hB _ (s.orderEmbOfFin_mem rfl ⟨0, hj⟩)
  | succ j ih =>
      intro hj
      have hj' : j < s.card := by omega
      have hp := ih hj'
      have hlt := (s.orderEmbOfFin rfl).strictMono
        (show (⟨j, hj'⟩ : Fin s.card) < ⟨j + 1, hj⟩ from by exact_mod_cast Nat.lt_succ_self j)
      obtain ⟨u, hu⟩ := hodd _ (s.orderEmbOfFin_mem rfl ⟨j, hj'⟩)
      obtain ⟨v, hv⟩ := hodd _ (s.orderEmbOfFin_mem rfl ⟨j + 1, hj⟩)
      omega

/-- An exact rational product envelope for any finite set of positive odd states. -/
theorem odd_finset_ratio_product_bound (s : Finset ℕ) (B : ℕ) (hBpos : 0 < B)
    (hodd : ∀ x ∈ s, Odd x) (hB : ∀ x ∈ s, B ≤ x) :
    (∏ x ∈ s, (3 * (x : ℚ) + 1) / x) ≤
      ∏ i ∈ Finset.range s.card, (3 * ((B + 2 * i : ℕ) : ℚ) + 1) / ((B + 2 * i : ℕ) : ℚ) := by
  classical
  conv_lhs => rw [← s.map_orderEmbOfFin_univ rfl, Finset.prod_map]
  rw [Finset.prod_range]
  apply Finset.prod_le_prod
  · intro i _
    positivity
  · intro i _
    have hbound := odd_finset_rank_lower s B hodd hB i.val i.isLt
    have hxpos : (0 : ℚ) < s.orderEmbOfFin rfl i := by
      exact_mod_cast (lt_of_lt_of_le hBpos (hB _ (s.orderEmbOfFin_mem rfl i)))
    have hbpos : (0 : ℚ) < (B + 2 * i.val : ℕ) := by positivity
    have hcast : ((B + 2 * i.val : ℕ) : ℚ) ≤ s.orderEmbOfFin rfl i := by
      exact_mod_cast hbound
    apply (div_le_div_iff₀ hxpos hbpos).2
    change (3 * (s.orderEmbOfFin rfl i : ℚ) + 1) * ((B + 2 * i.val : ℕ) : ℚ) ≤
      (3 * ((B + 2 * i.val : ℕ) : ℚ) + 1) * (s.orderEmbOfFin rfl i : ℚ)
    nlinarith

/-- Least-period iterates are distinct, using Mathlib's minimal-period API. -/
theorem least_period_iterates_injective (m p : ℕ) (hp : 0 < p)
    (hcyc : syracuseStep^[p] m = m)
    (hmin : ∀ k : ℕ, 0 < k → k < p → syracuseStep^[k] m ≠ m) :
    Function.Injective (fun i : Fin p => syracuseStep^[i.val] m) := by
  have hperiod : Function.IsPeriodicPt syracuseStep p m := hcyc
  have hpos := hperiod.minimalPeriod_pos hp
  have hle := hperiod.minimalPeriod_le hp
  have heq : Function.minimalPeriod syracuseStep m = p := by
    by_contra hne
    have hlt : Function.minimalPeriod syracuseStep m < p := by omega
    exact hmin _ hpos hlt (Function.iterate_minimalPeriod (f := syracuseStep) (x := m))
  intro i j hij
  apply Fin.ext
  exact (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod (f := syracuseStep) (x := m)
    (by rw [heq]; exact i.isLt) (by rw [heq]; exact j.isLt)).mp hij

/-- Multiplying the exact rows around a positive periodic orbit. -/
theorem syracuse_cycle_product_identity (m p : ℕ) (hm : 0 < m)
    (hcyc : syracuseStep^[p] m = m) :
    2 ^ (∑ i ∈ Finset.range p, (3 * syracuseStep^[i] m + 1).factorization 2) *
      (∏ i ∈ Finset.range p, syracuseStep^[i] m) =
      ∏ i ∈ Finset.range p, (3 * syracuseStep^[i] m + 1) := by
  let b := fun i : ℕ => syracuseStep^[i] m
  have hs : (∏ i ∈ Finset.range p, b (i + 1)) = ∏ i ∈ Finset.range p, b i := by
    have hleft := Finset.prod_range_succ' b p
    have hright := Finset.prod_range_succ b p
    have hb0 : b 0 = m := rfl
    have hbp : b p = m := hcyc
    rw [hb0] at hleft
    rw [hbp] at hright
    nlinarith
  have hrow (i : ℕ) : 2 ^ ((3 * b i + 1).factorization 2) * b (i + 1) =
      3 * b i + 1 := by
    change 2 ^ ((3 * syracuseStep^[i] m + 1).factorization 2) *
      syracuseStep^[i + 1] m = 3 * syracuseStep^[i] m + 1
    rw [Function.iterate_succ_apply']
    exact Nat.ordProj_mul_ordCompl_eq_self (3 * syracuseStep^[i] m + 1) 2
  calc
    _ = (∏ i ∈ Finset.range p, 2 ^ ((3 * b i + 1).factorization 2)) *
        (∏ i ∈ Finset.range p, b (i + 1)) := by
      rw [Finset.prod_pow_eq_pow_sum, hs]
    _ = ∏ i ∈ Finset.range p, (2 ^ ((3 * b i + 1).factorization 2) * b (i + 1)) :=
      (Finset.prod_mul_distrib).symm
    _ = _ := Finset.prod_congr rfl (fun i _ => hrow i)

/-- Exact quotient form of the cycle product identity. -/
theorem syracuse_cycle_ratio_product (m p : ℕ) (hm : 0 < m)
    (hcyc : syracuseStep^[p] m = m) :
    (∏ i ∈ Finset.range p, (3 * (syracuseStep^[i] m : ℚ) + 1) / syracuseStep^[i] m) =
      (2 : ℚ) ^ (∑ i ∈ Finset.range p, (3 * syracuseStep^[i] m + 1).factorization 2) := by
  have hid := syracuse_cycle_product_identity m p hm hcyc
  have hcast : (∏ i ∈ Finset.range p, (3 * (syracuseStep^[i] m : ℚ) + 1)) =
      (2 : ℚ) ^ (∑ i ∈ Finset.range p, (3 * syracuseStep^[i] m + 1).factorization 2) *
        (∏ i ∈ Finset.range p, (syracuseStep^[i] m : ℚ)) := by exact_mod_cast hid.symm
  have hpos : (0 : ℚ) < ∏ i ∈ Finset.range p, (syracuseStep^[i] m : ℚ) := by
    apply Finset.prod_pos
    intro i _
    exact_mod_cast syracuse_iterate_pos m i hm
  rw [Finset.prod_div_distrib, hcast]
  exact mul_div_cancel_right₀ _ (ne_of_gt hpos)

end CollatzFrontierAux

open scoped BigOperators

/-- Distinct-state integer product budget for a realized least-period Syracuse cycle.
This uses a lower bound on every state, not a locally imported baseline theorem. -/
theorem solution (m p B : ℕ) (hm : 0 < m) (hp : 0 < p)
    (hBpos : 0 < B) (hcyc : syracuseStep^[p] m = m)
    (hmin : ∀ k : ℕ, 0 < k → k < p → syracuseStep^[k] m ≠ m)
    (hbaseline : ∀ i < p, B ≤ syracuseStep^[i] m) :
    2 ^ (∑ i ∈ Finset.range p, (3 * syracuseStep^[i] m + 1).factorization 2) *
      (∏ i ∈ Finset.range p, (B + 2 * i)) ≤
      ∏ i ∈ Finset.range p, (3 * (B + 2 * i) + 1) := by
  classical
  let f : Fin p → ℕ := fun i => syracuseStep^[i.val] m
  let s := Finset.univ.image f
  have hinj : Function.Injective f :=
    CollatzFrontierAux.least_period_iterates_injective m p hp hcyc hmin
  have hcard : s.card = p := by
    rw [Finset.card_image_of_injective _ hinj]
    simp
  have hom : Odd m := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
    rw [← hcyc, hk, Function.iterate_succ_apply']
    exact CollatzFrontierAux.syracuseStep_odd _
  have hos : ∀ x ∈ s, Odd x := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact CollatzFrontierAux.syracuse_iterate_odd m hom i
  have hbs : ∀ x ∈ s, B ≤ x := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact hbaseline i i.isLt
  have hbound := CollatzFrontierAux.odd_finset_ratio_product_bound s B hBpos hos hbs
  rw [hcard] at hbound
  change (∏ x ∈ Finset.univ.image f, (3 * (x : ℚ) + 1) / x) ≤ _ at hbound
  rw [Finset.prod_image hinj.injOn] at hbound
  change (∏ i : Fin p, (3 * (syracuseStep^[i.val] m : ℚ) + 1) / syracuseStep^[i.val] m) ≤ _ at hbound
  rw [← Finset.prod_range (n := p)
    (fun i : ℕ => (3 * (syracuseStep^[i] m : ℚ) + 1) / syracuseStep^[i] m)] at hbound
  rw [CollatzFrontierAux.syracuse_cycle_ratio_product m p hm hcyc] at hbound
  rw [Finset.prod_div_distrib] at hbound
  have hdpos : (0 : ℚ) < ∏ i ∈ Finset.range p, ((B + 2 * i : ℕ) : ℚ) := by
    apply Finset.prod_pos
    intro i _
    positivity
  have hmul := (le_div_iff₀ hdpos).mp hbound
  exact_mod_cast hmul

#print axioms solution
