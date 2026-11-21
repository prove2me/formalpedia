-- Prove2me | solution 1 for GRH.reduced_liouville_harmonic_le_of_modulus_one
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T01:32:54.032183+00:00
-- url     : https://prove2.me/submissions/9cea7a75-5adc-4606-ab8d-87021d0710e9

import Mathlib
import Definitions.Def_GRH_SquarefreeBilinear

open Finset ArithmeticFunction
open scoped BigOperators zeta Moebius

open GRH

private theorem harmonic_as_range (q U : ℕ) [NeZero q] :
    reducedLiouvilleHarmonic q U = ∑ n ∈ range (U+1),
      if Nat.Coprime n q then (liouville n : ℝ) / n else 0 := by
  classical
  unfold reducedLiouvilleHarmonic
  simp_rw [ZMod.isUnit_iff_coprime]
  have he : range (U+1) = insert 0 (Ioc 0 U) := by ext k; simp
  rw [he,sum_insert (by simp)]
  simp

private theorem divisor_indicator (k q : ℕ) [NeZero q] :
    (∑ d ∈ q.divisors, if d ∣ k then (moebius d : ℝ) else 0) =
      if Nat.Coprime k q then 1 else 0 := by
  classical
  have hg : k.gcd q ≠ 0 := Nat.ne_of_gt (Nat.gcd_pos_of_pos_right k (NeZero.pos q))
  have he : q.divisors.filter (fun d => d ∣ k) = (k.gcd q).divisors := by
    ext d
    simp [Nat.mem_divisors, NeZero.ne q, hg, Nat.dvd_gcd_iff, and_comm]
  rw [←sum_filter,he]
  have H := DFunLike.congr_fun moebius_mul_coe_zeta (k.gcd q)
  rw [coe_mul_zeta_apply,one_apply] at H
  change _ = if k.gcd q = 1 then 1 else 0
  split_ifs at H ⊢ with h <;> exact_mod_cast H

private theorem abs_moebius_as_product (d : ℕ) :
    (moebius d : ℝ) * (liouville d : ℝ) = |(moebius d : ℝ)| := by
  by_cases h : Squarefree d
  · rw [moebius_apply_of_squarefree h,liouville_apply h.ne_zero]
    push_cast
    rw [←sq, ←pow_mul, Nat.mul_comm, pow_mul]
    simp
  · simp [moebius_eq_zero_of_not_squarefree h]

private theorem sum_multiples_upto (N t : ℕ) (ht : 0 < t) (F : ℕ → ℝ) :
    (∑ k ∈ range (N+1), if t ∣ k then F k else 0) =
      ∑ j ∈ range (N/t+1), F (t*j) := by
  rw [←Finset.sum_filter]
  apply sum_bij' (fun k _ => k/t) (fun j _ => t*j)
  · intro k hk
    apply mem_range.mpr
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.le_of_lt_succ (mem_range.mp (mem_filter.mp hk).1)))
  · intro j hj
    apply mem_filter.mpr
    refine ⟨mem_range.mpr (Nat.lt_succ_of_le ?_),dvd_mul_right _ _⟩
    rw [mul_comm]
    exact (Nat.le_div_iff_mul_le ht).mp (Nat.le_of_lt_succ (mem_range.mp hj))
  · intro k hk
    exact Nat.mul_div_cancel' (mem_filter.mp hk).2
  · intro j _
    exact Nat.mul_div_cancel_left _ ht
  · intro k hk
    rw [Nat.mul_div_cancel' (mem_filter.mp hk).2]

private theorem sieve_identity (q U : ℕ) [NeZero q] :
    reducedLiouvilleHarmonic q U =
      ∑ d ∈ q.divisors, (|(moebius d : ℝ)| / (d:ℝ)) * reducedLiouvilleHarmonic 1 (U/d) := by
  classical
  let f (n : ℕ) : ℝ := (liouville n : ℝ) / n
  rw [harmonic_as_range]
  calc _ = ∑ k ∈ range (U+1), ∑ d ∈ q.divisors,
              if d ∣ k then (moebius d : ℝ) * f k else 0 := by
          apply sum_congr rfl
          intro k _
          calc _ = (∑ d ∈ q.divisors, if d ∣ k then (moebius d:ℝ) else 0) * f k := by
                    rw [divisor_indicator]; split_ifs <;> simp [f]
               _ = _ := by rw [sum_mul]; apply sum_congr rfl; intro d _; split_ifs <;> simp
       _ = ∑ d ∈ q.divisors, ∑ k ∈ range (U+1),
              if d ∣ k then (moebius d:ℝ) * f k else 0 := sum_comm
       _ = _ := by
          apply sum_congr rfl
          intro d hd
          rw [sum_multiples_upto U d (Nat.pos_of_mem_divisors hd),harmonic_as_range,mul_sum]
          apply sum_congr rfl
          intro j _
          simp only [f, liouville_apply_mul, Int.cast_mul, Nat.cast_mul,
            if_pos (Nat.coprime_one_right j), ←abs_moebius_as_product]
          ring

private theorem div_floor_power_bound (U d : ℕ) (hd : 0 < d) (σ : ℝ) (hσ : σ ≤ 1) :
    (((U / d : ℕ) : ℝ) + 1) ^ (σ - 1) / (d : ℝ) ≤
      ((U:ℝ)+1) ^ (σ-1) * (d:ℝ)^(-σ) := by
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have hn : U+1 ≤ (U/d+1)*d := by
    have h1 := Nat.mod_lt U hd
    have h2 := Nat.mod_add_div U d
    rw [Nat.add_mul,Nat.one_mul,Nat.mul_comm (U/d)] 
    omega
  have hx : ((U:ℝ)+1)/(d:ℝ) ≤ ((U/d:ℕ):ℝ)+1 := by
    apply (div_le_iff₀ hdR).mpr
    exact_mod_cast hn
  apply (div_le_div_of_nonneg_right
    (Real.rpow_le_rpow_of_nonpos (by positivity) hx (by linarith : σ-1 ≤ 0)) hdR.le).trans_eq
  rw [Real.div_rpow (by positivity) hdR.le,div_div]
  have hpow : (d:ℝ)^(σ-1) * (d:ℝ) = (d:ℝ)^σ := by
    rw [←Real.rpow_add_one hdR.ne']; congr 1; ring
  rw [hpow,Real.rpow_neg hdR.le,div_eq_mul_inv]

theorem solution
    (q : ℕ) [NeZero q] (σ C : ℝ) (hσ : σ ≤ 1) (hC : 0 ≤ C)
    (H : ∀ U : ℕ, |reducedLiouvilleHarmonic 1 U| ≤ C * ((U:ℝ)+1)^(σ-1))
    (U : ℕ) :
    |reducedLiouvilleHarmonic q U| ≤
      (C * ∑ d ∈ q.divisors, |(moebius d:ℝ)| * (d:ℝ)^(-σ)) * ((U:ℝ)+1)^(σ-1) := by
  classical
  rw [sieve_identity]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc _ ≤ ∑ d ∈ q.divisors, C * ((U:ℝ)+1)^(σ-1) * (|(moebius d:ℝ)| * (d:ℝ)^(-σ)) := by
          apply sum_le_sum
          intro d hd
          have hdn := Nat.pos_of_mem_divisors hd
          have hpos : (0:ℝ) < d := by exact_mod_cast hdn
          rw [abs_mul,abs_of_nonneg (div_nonneg (abs_nonneg _) hpos.le)]
          apply (mul_le_mul_of_nonneg_left (H _) (div_nonneg (abs_nonneg _) hpos.le)).trans
          calc _ = (|(moebius d:ℝ)| * C) * (((U/d:ℕ)+1:ℝ)^(σ-1)/d) := by ring
               _ ≤ (|(moebius d:ℝ)| * C) * (((U:ℝ)+1)^(σ-1) * (d:ℝ)^(-σ)) :=
                 mul_le_mul_of_nonneg_left (div_floor_power_bound U d hdn σ hσ)
                   (mul_nonneg (abs_nonneg _) hC)
               _ = _ := by ring
       _ = _ := by rw [←mul_sum]; ring

