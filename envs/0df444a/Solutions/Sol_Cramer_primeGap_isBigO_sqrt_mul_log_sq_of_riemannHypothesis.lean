-- Prove2me | solution 1 for Cramer.primeGap_isBigO_sqrt_mul_log_sq_of_riemannHypothesis
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T00:42:03.734191+00:00
-- url     : https://prove2.me/submissions/7597c879-54f6-4a0d-aa53-bc3973fa56f0

import Theorems.Thm_LandauCriterion_psi_error_of_riemannHypothesis
import Theorems.Thm_LandauExplore_theta_error_of_psi_error
import Definitions.Def_LindelofHypothesis_GrowthAndZeroCounts

set_option autoImplicit false

open Real Filter Asymptotics

namespace CramerAux

/-- Under RH, `θ(t) - t = O(√t log² t)` for `t ≥ 2`. -/
lemma theta_bound (hRH : RiemannHypothesis) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 2 ≤ t → |Chebyshev.theta t - t| ≤ K * √t * (log t) ^ 2 := by
  obtain ⟨C, hC⟩ := LandauCriterion.psi_error_of_riemannHypothesis hRH
  have hpsi : LandauExplore.psiError C := fun x hx => hC x hx
  refine ⟨max C 0 + 4, by positivity, fun t ht => ?_⟩
  have h := LandauExplore.theta_error_of_psi_error hpsi ht
  have hlog2 : (1 : ℝ) / 2 ≤ log 2 := by have := Real.log_two_gt_d9; linarith
  have hlog : (1 : ℝ) / 2 ≤ log t := le_trans hlog2 (Real.log_le_log (by norm_num) ht)
  have hsq : 0 ≤ √t := sqrt_nonneg t
  have h2 : 2 * log t ≤ 4 * (log t) ^ 2 := by nlinarith
  have h3 : C * (log t) ^ 2 ≤ max C 0 * (log t) ^ 2 :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
  calc |Chebyshev.theta t - t| ≤ (C * (log t) ^ 2 + 2 * log t) * √t := h
    _ ≤ (max C 0 * (log t) ^ 2 + 4 * (log t) ^ 2) * √t :=
        mul_le_mul_of_nonneg_right (by linarith) hsq
    _ = (max C 0 + 4) * √t * (log t) ^ 2 := by ring

/-- If `θ` increases between `x` and `y`, there is a prime in `(x, y]`. -/
lemma exists_prime_of_theta_lt {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y)
    (h : Chebyshev.theta x < Chebyshev.theta y) : ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ y := by
  by_contra hne
  push_neg at hne
  have hy : 0 ≤ y := hx.trans hxy
  have hset : Nat.primesLE ⌊y⌋₊ = Nat.primesLE ⌊x⌋₊ := by
    ext p
    simp only [Nat.mem_primesLE]
    constructor
    · rintro ⟨hp, hpr⟩
      refine ⟨?_, hpr⟩
      have hpy : (p : ℝ) ≤ y := (Nat.le_floor_iff hy).mp hp
      by_contra hpx
      push_neg at hpx
      have : x < p := by
        have := (Nat.floor_lt hx).mp hpx
        exact this
      exact absurd hpy (not_le.mpr (hne p hpr this))
    · rintro ⟨hp, hpr⟩
      exact ⟨Nat.floor_le_floor hxy |>.trans' hp, hpr⟩
  rw [Chebyshev.theta_eq_sum_primesLE, Chebyshev.theta_eq_sum_primesLE, hset] at h
  exact lt_irrefl _ h

end CramerAux

open CramerAux in
theorem solution (hRH : RiemannHypothesis) :
    (fun n : ℕ => (LindelofHypothesis.primeGap n : ℝ)) =O[atTop]
      (fun n : ℕ => Real.sqrt (Nat.nth Nat.Prime n : ℝ) * Real.log (Nat.nth Nat.Prime n : ℝ) ^ 2) := by
  obtain ⟨K, hK0, hK⟩ := theta_bound hRH
  set A : ℝ := 10 * (K + 1) with hA
  have hApos : 0 < A := by positivity
  -- eventually `A log² x ≤ √x`
  have hev : ∀ᶠ x : ℝ in atTop, A * log x ^ 2 ≤ √x := by
    have hlo := isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)
    have := hlo.def (c := 1 / A) (by positivity)
    filter_upwards [this, eventually_ge_atTop (1 : ℝ)] with x hx hx1
    have hlx : 0 ≤ log x := Real.log_nonneg hx1
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hlx _),
      Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)] at hx
    rw [← Real.sqrt_eq_rpow] at hx
    rw [show log x ^ (2 : ℝ) = log x ^ 2 by norm_cast] at hx
    have := mul_le_mul_of_nonneg_left hx hApos.le
    rw [← mul_assoc, mul_one_div_cancel hApos.ne', one_mul] at this
    exact this
  obtain ⟨X0, hX0⟩ := eventually_atTop.mp hev
  -- a prime in every interval `(x, x + A √x log² x]` for large `x`
  have hprime : ∀ x : ℝ, max X0 4 ≤ x → ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ x + A * √x * log x ^ 2 := by
    intro x hx
    have hx4 : 4 ≤ x := le_trans (le_max_right _ _) hx
    have hxX : X0 ≤ x := le_trans (le_max_left _ _) hx
    set h := A * √x * log x ^ 2 with hh
    have hlogpos : 0 < log x := Real.log_pos (by linarith)
    have hsqpos : 0 < √x := Real.sqrt_pos.mpr (by linarith)
    have hsx : √x * √x = x := Real.mul_self_sqrt (by linarith)
    have hhx : h ≤ x := by
      have := hX0 x hxX
      calc h = (A * log x ^ 2) * √x := by rw [hh]; ring
        _ ≤ √x * √x := mul_le_mul_of_nonneg_right this hsqpos.le
        _ = x := hsx
    have hh0 : 0 ≤ h := by positivity
    -- bounds at `x + h`
    have hsq2 : √(x + h) ≤ 2 * √x := by
      rw [show (2 : ℝ) * √x = √(4 * x) by
        rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by linarith)
    have hlog2 : log (x + h) ≤ 2 * log x := by
      have h1 : log (x + h) ≤ log (x * x) := Real.log_le_log (by linarith) (by nlinarith)
      rw [Real.log_mul (by linarith) (by linarith)] at h1
      linarith
    have hlogxh : 0 ≤ log (x + h) := Real.log_nonneg (by linarith)
    have hlog2sq : log (x + h) ^ 2 ≤ 4 * log x ^ 2 := by nlinarith
    have hb1 := hK x (by linarith)
    have hb2 := hK (x + h) (by linarith)
    have hb2' : K * √(x + h) * log (x + h) ^ 2 ≤ 8 * K * √x * log x ^ 2 := by
      have := mul_le_mul hsq2 hlog2sq (sq_nonneg _) (by positivity)
      nlinarith
    have hpos : 0 < √x * log x ^ 2 := by positivity
    have hlt : Chebyshev.theta x < Chebyshev.theta (x + h) := by
      have e1 := (abs_le.mp hb1)
      have e2 := (abs_le.mp hb2)
      have : h = (10 * (K + 1)) * (√x * log x ^ 2) := by rw [hh, hA]; ring
      nlinarith
    exact exists_prime_of_theta_lt (by linarith) (by linarith) hlt
  -- pass to consecutive primes
  have hinf : (setOf Nat.Prime).Infinite := Nat.infinite_setOf_prime
  have hsm := Nat.nth_strictMono hinf
  refine Asymptotics.IsBigO.of_bound A ?_
  filter_upwards [eventually_ge_atTop ⌈max X0 4⌉₊] with n hn
  set p := Nat.nth Nat.Prime n with hp
  have hpn : n ≤ p := hsm.id_le n
  have hpX : max X0 4 ≤ (p : ℝ) := by
    have := Nat.le_ceil (max X0 4)
    have h2 : (⌈max X0 4⌉₊ : ℝ) ≤ p := by exact_mod_cast hn.trans hpn
    linarith
  obtain ⟨q, hq, hpq, hqle⟩ := hprime p hpX
  have hnext : Nat.nth Nat.Prime (n + 1) ≤ q := by
    by_contra hcon
    push_neg at hcon
    have := Nat.le_nth_of_lt_nth_succ hcon hq
    have : (q : ℝ) ≤ p := by exact_mod_cast this
    linarith
  have hle : p ≤ Nat.nth Nat.Prime (n + 1) := (hsm (Nat.lt_succ_self n)).le
  have hgap : (LindelofHypothesis.primeGap n : ℝ) ≤ A * √(p : ℝ) * log (p : ℝ) ^ 2 := by
    unfold LindelofHypothesis.primeGap
    rw [Nat.cast_sub hle]
    have : (Nat.nth Nat.Prime (n + 1) : ℝ) ≤ q := by exact_mod_cast hnext
    linarith
  have hp4 : (4 : ℝ) ≤ p := le_trans (le_max_right _ _) hpX
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by
    have : 0 ≤ log (p : ℝ) := Real.log_nonneg (by linarith)
    positivity)]
  calc (LindelofHypothesis.primeGap n : ℝ) ≤ A * √(p : ℝ) * log (p : ℝ) ^ 2 := hgap
    _ = A * (√(p : ℝ) * log (p : ℝ) ^ 2) := by ring
