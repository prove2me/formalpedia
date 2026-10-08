-- Prove2me | solution 1 for CollatzFrontier.syracuse_no_least_period_50275
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-10-04T17:44:45.429859+00:00
-- url     : https://prove2.me/submissions/a025c0d2-e70c-4127-a449-d973b426b797

import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_no_cycle_below_2310000
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Factorization.Basic

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace CollatzFrontierAux
open scoped BigOperators

/-! ### Oddness / positivity along the Syracuse orbit -/

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

theorem syracuse_iterate_pos (m i : ℕ) (hm : 0 < m) : 0 < syracuseStep^[i] m := by
  cases i with
  | zero => exact hm
  | succ i =>
      rw [Function.iterate_succ_apply']
      exact Nat.ordCompl_pos 2 (by omega)

/-! ### Distinct-state product budget (same content as `syracuse_least_cycle_distinct_budget`) -/

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

theorem syracuse_least_cycle_distinct_budget (m p B : ℕ) (hm : 0 < m) (hp : 0 < p)
    (hBpos : 0 < B) (hcyc : syracuseStep^[p] m = m)
    (hmin : ∀ k : ℕ, 0 < k → k < p → syracuseStep^[k] m ≠ m)
    (hbaseline : ∀ i < p, B ≤ syracuseStep^[i] m) :
    2 ^ (∑ i ∈ Finset.range p, (3 * syracuseStep^[i] m + 1).factorization 2) *
      (∏ i ∈ Finset.range p, (B + 2 * i)) ≤
      ∏ i ∈ Finset.range p, (3 * (B + 2 * i) + 1) := by
  classical
  let f : Fin p → ℕ := fun i => syracuseStep^[i.val] m
  let s := Finset.univ.image f
  have hinj : Function.Injective f := least_period_iterates_injective m p hp hcyc hmin
  have hcard : s.card = p := by
    rw [Finset.card_image_of_injective _ hinj]
    simp
  have hom : Odd m := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
    rw [← hcyc, hk, Function.iterate_succ_apply']
    exact syracuseStep_odd _
  have hos : ∀ x ∈ s, Odd x := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact syracuse_iterate_odd m hom i
  have hbs : ∀ x ∈ s, B ≤ x := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact hbaseline i i.isLt
  have hbound := odd_finset_ratio_product_bound s B hBpos hos hbs
  rw [hcard] at hbound
  change (∏ x ∈ Finset.univ.image f, (3 * (x : ℚ) + 1) / x) ≤ _ at hbound
  rw [Finset.prod_image hinj.injOn] at hbound
  change (∏ i : Fin p, (3 * (syracuseStep^[i.val] m : ℚ) + 1) / syracuseStep^[i.val] m) ≤ _ at hbound
  rw [← Finset.prod_range (n := p)
    (fun i : ℕ => (3 * (syracuseStep^[i] m : ℚ) + 1) / syracuseStep^[i] m)] at hbound
  rw [syracuse_cycle_ratio_product m p hm hcyc] at hbound
  rw [Finset.prod_div_distrib] at hbound
  have hdpos : (0 : ℚ) < ∏ i ∈ Finset.range p, ((B + 2 * i : ℕ) : ℚ) := by
    apply Finset.prod_pos
    intro i _
    positivity
  have hmul := (le_div_iff₀ hdpos).mp hbound
  exact_mod_cast hmul

/-! ### Affine transfer and the strict power gap -/

theorem syracuseStep_affine (e : ℕ) {b A c D q : ℕ}
    (hc : 3 * b + 1 = 2 ^ e * c)
    (hD : 3 * A = 2 ^ e * D)
    (hodd : ¬ 2 ∣ c + D * q) :
    syracuseStep (b + A * q) = c + D * q := by
  unfold syracuseStep
  have h : 3 * (b + A * q) + 1 = 2 ^ e * (c + D * q) := by
    calc
      3 * (b + A * q) + 1 = (3 * b + 1) + (3 * A) * q := by ring
      _ = 2 ^ e * (c + D * q) := by rw [hc, hD]; ring
  rw [h]
  exact Nat.ordCompl_pow_mul_of_not_dvd e Nat.prime_two hodd

theorem dyadic_chain_growth (a b : ℕ → ℕ) (k : ℕ)
    (hstep : ∀ i < k, 3 * b i + 1 = 2 ^ (a i) * b (i + 1)) :
    3 ^ k * b 0 ≤ 2 ^ (∑ i ∈ Finset.range k, a i) * b k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hp := ih (fun i hi => hstep i (by omega))
      rw [Finset.sum_range_succ, pow_add, pow_succ]
      calc
        _ ≤ 3 * (2 ^ (∑ i ∈ Finset.range k, a i) * b k) := by nlinarith [hp]
        _ ≤ 2 ^ (∑ i ∈ Finset.range k, a i) * (3 * b k + 1) := by
          calc
            _ ≤ 3 * (2 ^ (∑ i ∈ Finset.range k, a i) * b k) +
                2 ^ (∑ i ∈ Finset.range k, a i) := Nat.le_add_right _ _
            _ = _ := by ring
        _ = _ := by rw [hstep k (by omega)]; ring

theorem terminal_power_contraction (a b : ℕ → ℕ) (k e B : ℕ)
    (hstep : ∀ i < k, 3 * b i + 1 = 2 ^ (a i) * b (i + 1))
    (hfinal : 3 * b k + 1 = 2 ^ e * B)
    (hdesc : B ≤ b 0) :
    3 ^ (k + 1) < 2 ^ ((∑ i ∈ Finset.range k, a i) + e) := by
  have hp := dyadic_chain_growth a b k hstep
  have hpow : 0 < 2 ^ (∑ i ∈ Finset.range k, a i) := pow_pos (by decide) _
  have hx : 3 ^ (k + 1) * b 0 <
      2 ^ ((∑ i ∈ Finset.range k, a i) + e) * b 0 := by
    calc
      _ ≤ 3 * (2 ^ (∑ i ∈ Finset.range k, a i) * b k) := by rw [pow_succ]; nlinarith
      _ < 2 ^ (∑ i ∈ Finset.range k, a i) * (3 * b k + 1) := by nlinarith
      _ = 2 ^ ((∑ i ∈ Finset.range k, a i) + e) * B := by rw [hfinal, pow_add]; ring
      _ ≤ _ := Nat.mul_le_mul_left _ hdesc
  exact Nat.lt_of_mul_lt_mul_right hx

theorem syracuse_cycle_power_gap (m p : ℕ) (hp : 0 < p)
    (hcyc : syracuseStep^[p] m = m) :
    3 ^ p < 2 ^ (∑ i ∈ Finset.range p, (3 * syracuseStep^[i] m + 1).factorization 2) := by
  cases p with
  | zero => omega
  | succ k =>
      let a := fun i : ℕ => (3 * syracuseStep^[i] m + 1).factorization 2
      let b := fun i : ℕ => syracuseStep^[i] m
      have hstep (i : ℕ) : 3 * b i + 1 = 2 ^ (a i) * b (i + 1) := by
        change 3 * syracuseStep^[i] m + 1 =
          2 ^ ((3 * syracuseStep^[i] m + 1).factorization 2) * syracuseStep^[i + 1] m
        rw [Function.iterate_succ_apply']
        exact (Nat.ordProj_mul_ordCompl_eq_self (3 * syracuseStep^[i] m + 1) 2).symm
      have hc := terminal_power_contraction a b k (a k) (b (k + 1))
        (fun i _ => hstep i) (hstep k) (by change syracuseStep^[k + 1] m ≤ m; exact hcyc.le)
      simpa only [a, Finset.sum_range_succ] using hc

/-- Checked minimum possible total exponent for period 50275. -/
theorem exponent_floor_50275 : (2 : ℕ) ^ 79683 < 3 ^ 50275 := by decide +kernel

/-! ### Product-free sixth-power telescoping envelope (the cheap certificate route) -/

theorem sixth_power_ratio_bound (x : ℚ) (hx : 1 < x) :
    ((3 * x + 1) / x) ^ 6 ≤ (3 : ℚ) ^ 6 * ((x + 1) / (x - 1)) := by
  have hpoly : (3 * x) ^ 6 * (x + 1) - (3 * x + 1) ^ 6 * (x - 1) =
      243 * x ^ 5 + 675 * x ^ 4 + 405 * x ^ 3 + 117 * x ^ 2 + 17 * x + 1 := by ring
  have hpos : 0 ≤ 243 * x ^ 5 + 675 * x ^ 4 + 405 * x ^ 3 + 117 * x ^ 2 + 17 * x + 1 := by positivity
  rw [div_pow, ← mul_div_assoc]
  apply (div_le_div_iff₀ (pow_pos (by linarith) 6) (by linarith)).2
  nlinarith [hpoly]

theorem odd_spacing_product_telescopes (B : ℚ) (hB : 1 < B) (p : ℕ) :
    (∏ i ∈ Finset.range p, (B + 2 * i + 1) / (B + 2 * i - 1)) =
      (B + 2 * p - 1) / (B - 1) := by
  induction p with
  | zero => simp; exact (div_self (show B - 1 ≠ 0 from by linarith)).symm
  | succ p ih =>
      rw [Finset.prod_range_succ, ih]
      have hd : B + 2 * (p : ℚ) - 1 ≠ 0 := by
        have : (0 : ℚ) ≤ p := Nat.cast_nonneg p
        linarith
      have hb : B - 1 ≠ 0 := by linarith
      push_cast
      field_simp
      ring

theorem distinct_product_sixth_power_bound (B : ℚ) (hB : 1 < B) (p : ℕ) :
    (∏ i ∈ Finset.range p, (3 * (B + 2 * i) + 1) / (B + 2 * i)) ^ 6 ≤
      3 ^ (6 * p) * ((B + 2 * p - 1) / (B - 1)) := by
  rw [← Finset.prod_pow]
  have hb : (∏ i ∈ Finset.range p, ((3 * (B + 2 * i) + 1) / (B + 2 * i)) ^ 6) ≤
      ∏ i ∈ Finset.range p, (3 : ℚ) ^ 6 * ((B + 2 * i + 1) / (B + 2 * i - 1)) := by
    apply Finset.prod_le_prod
    · intro i _; positivity
    · intro i _
      exact sixth_power_ratio_bound _ (by have := Nat.cast_nonneg (α := ℚ) i; linarith)
  simpa only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
    ← pow_mul, odd_spacing_product_telescopes B hB p] using hb

theorem sixth_power_budget_of_distinct_budget (B p K : ℕ) (hB : 2 ≤ B)
    (hbudget : 2 ^ K * (∏ i ∈ Finset.range p, (B + 2 * i)) ≤
      ∏ i ∈ Finset.range p, (3 * (B + 2 * i) + 1)) :
    (B - 1) * 2 ^ (6 * K) ≤ (B + 2 * p - 1) * 3 ^ (6 * p) := by
  have hbq : (1 : ℚ) < B := by exact_mod_cast (show 1 < B from by omega)
  have hqpos : (0 : ℚ) < ∏ i ∈ Finset.range p, ((B + 2 * i : ℕ) : ℚ) := by
    apply Finset.prod_pos
    intro i _
    exact_mod_cast (show 0 < B + 2 * i from by omega)
  have hc : (2 : ℚ) ^ K * (∏ i ∈ Finset.range p, ((B + 2 * i : ℕ) : ℚ)) ≤
      ∏ i ∈ Finset.range p, (3 * ((B + 2 * i : ℕ) : ℚ) + 1) := by exact_mod_cast hbudget
  have hr := (le_div_iff₀ hqpos).2 hc
  rw [← Finset.prod_div_distrib] at hr
  push_cast at hr
  have hp := pow_le_pow_left₀ (by positivity : (0 : ℚ) ≤ 2 ^ K) hr 6
  have hb := distinct_product_sixth_power_bound (B : ℚ) hbq p
  have hfinal : (2 : ℚ) ^ (6 * K) ≤ 3 ^ (6 * p) * ((B + 2 * p - 1) / (B - 1)) := by
    rw [← pow_mul, Nat.mul_comm K 6] at hp
    exact hp.trans hb
  rw [← mul_div_assoc] at hfinal
  have hm := (le_div_iff₀ (show (0 : ℚ) < B - 1 from by linarith)).mp hfinal
  have hBsub : 1 ≤ B := by omega
  have hPsub : 1 ≤ B + 2 * p := by omega
  have hcast : (((B - 1) * 2 ^ (6 * K) : ℕ) : ℚ) ≤
      (((B + 2 * p - 1) * 3 ^ (6 * p) : ℕ) : ℚ) := by
    push_cast [Nat.cast_sub hBsub, Nat.cast_sub hPsub]
    nlinarith
  exact_mod_cast hcast

/-- The telescoped sixth-power envelope fails strictly at the candidate `(p,K)=(50275,79684)`. -/
theorem sixth_power_budget_50275_failure :
    (2310000 + 2 * 50275 - 1) * (3 : ℕ) ^ (6 * 50275) <
      (2310000 - 1) * (2 : ℕ) ^ (6 * 79684) := by
  decide +kernel

end CollatzFrontierAux

open scoped BigOperators

/-- No positive integer has least Syracuse period exactly 50275, unconditionally given the
already-PROVED platform baseline `syracuse_no_cycle_below_2310000`. -/
theorem solution (m : ℕ) (hm : 0 < m)
    (hcyc : syracuseStep^[50275] m = m)
    (hmin : ∀ k : ℕ, 0 < k → k < 50275 → syracuseStep^[k] m ≠ m) : False := by
  have hperiod : Function.IsPeriodicPt syracuseStep 50275 m := hcyc
  have hmem : m ∈ Function.periodicPts syracuseStep := ⟨50275, by decide, hperiod⟩
  have hfixed : Function.IsFixedPt syracuseStep 1 := by
    change syracuseStep 1 = 1
    simpa using CollatzFrontierAux.syracuseStep_affine 2 (b := 1) (A := 0) (c := 1) (D := 0) (q := 0)
      (by decide) (by decide) (by decide)
  have hbaseline : ∀ i < 50275, 2310000 ≤ syracuseStep^[i] m := by
    intro i hi
    by_contra hsmall
    have hzi : syracuseStep^[50275] (syracuseStep^[i] m) = syracuseStep^[i] m :=
      hperiod.apply_iterate i
    have hone : syracuseStep^[i] m = 1 := syracuse_no_cycle_below_2310000 _ 50275
      (CollatzFrontierAux.syracuse_iterate_pos m i hm) (by decide) (by omega) hzi
    have hzfix : Function.IsPeriodicPt syracuseStep 1 (syracuseStep^[i] m) := by
      rw [hone]
      exact hfixed.isPeriodicPt 1
    have hmfix := Function.isPeriodicPt_of_mem_periodicPts_of_isPeriodicPt_iterate hmem hzfix
    exact hmin 1 (by decide) (by decide) hmfix
  have hbudget := CollatzFrontierAux.syracuse_least_cycle_distinct_budget m 50275 2310000
    hm (by decide) (by decide) hcyc hmin hbaseline
  have hgap := CollatzFrontierAux.syracuse_cycle_power_gap m 50275 (by decide) hcyc
  have hSge : 79684 ≤ ∑ i ∈ Finset.range 50275, (3 * syracuseStep^[i] m + 1).factorization 2 := by
    by_contra h
    have hle : (∑ i ∈ Finset.range 50275, (3 * syracuseStep^[i] m + 1).factorization 2) ≤ 79683 := by
      omega
    have hpow : (2 : ℕ) ^ (∑ i ∈ Finset.range 50275, (3 * syracuseStep^[i] m + 1).factorization 2) ≤
        2 ^ 79683 := Nat.pow_le_pow_right (by decide) hle
    have h1 : (2 : ℕ) ^ (∑ i ∈ Finset.range 50275, (3 * syracuseStep^[i] m + 1).factorization 2) <
        3 ^ 50275 := lt_of_le_of_lt hpow CollatzFrontierAux.exponent_floor_50275
    exact (lt_asymm h1) hgap
  have hsixth := CollatzFrontierAux.sixth_power_budget_of_distinct_budget 2310000 50275
    (∑ i ∈ Finset.range 50275, (3 * syracuseStep^[i] m + 1).factorization 2) (by decide) hbudget
  have hpow6 : (2 : ℕ) ^ (6 * 79684) ≤
      2 ^ (6 * (∑ i ∈ Finset.range 50275, (3 * syracuseStep^[i] m + 1).factorization 2)) :=
    Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left 6 hSge)
  have hchain : (2310000 - 1) * 2 ^ (6 * 79684) ≤
      (2310000 + 2 * 50275 - 1) * 3 ^ (6 * 50275) :=
    le_trans (Nat.mul_le_mul_left (2310000 - 1) hpow6) hsixth
  exact absurd CollatzFrontierAux.sixth_power_budget_50275_failure (not_lt.mpr hchain)

#print axioms solution
