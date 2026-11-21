-- Prove2me | solution 1 for GRH.liouville_harmonic_le_of_moebius_harmonic_le
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T01:36:11.507793+00:00
-- url     : https://prove2.me/submissions/e0a148b3-d98f-4af0-8574-fbc156dbe62f

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

private theorem square_divisor_iff {d r a : ℕ} (hr : r ≠ 0) (ha : Squarefree a) :
    d^2 ∣ r^2*a ↔ d ∣ r := by
  by_cases hd : d = 0
  · simp [hd,hr,ha.ne_zero]
  constructor
  · intro h
    apply (Nat.factorization_le_iff_dvd hd hr).mp
    have h' := (Nat.factorization_le_iff_dvd (pow_ne_zero _ hd)
      (mul_ne_zero (pow_ne_zero _ hr) ha.ne_zero)).mpr h
    intro p
    have hle := h' p
    rw [Nat.factorization_mul (pow_ne_zero _ hr) ha.ne_zero,Nat.factorization_pow,
        Nat.factorization_pow] at hle
    simp only [Finsupp.add_apply,Finsupp.smul_apply,nsmul_eq_mul] at hle
    have := ha.natFactorization_le_one p
    omega
  · intro h
    exact dvd_trans (pow_dvd_pow_of_dvd h _) (dvd_mul_right _ _)

private theorem liouville_square {d : ℕ} (hd : d ≠ 0) : liouville (d^2) = 1 := by
  rw [pow_two,liouville_apply_mul,liouville_apply hd,←pow_two,←pow_mul,Nat.mul_comm,pow_mul]
  norm_num

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

private theorem liouville_from_squares (k U : ℕ) (hkU : k ≤ U) :
    liouville k = ∑ d ∈ range (U+1), if d^2 ∣ k then moebius (k/d^2) else 0 := by
  by_cases hk : k = 0
  · simp [hk]
  obtain ⟨a,r,ha,hr,he,hsq⟩ := Nat.sq_mul_squarefree_of_pos (Nat.pos_of_ne_zero hk)
  have hrd : r^2 ∣ k := he ▸ dvd_mul_right _ _
  have hrk : r ∣ k := (dvd_pow_self r two_ne_zero).trans hrd
  have hrU : r ∈ range (U+1) := mem_range.mpr <| Nat.lt_succ_of_le <|
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hk) hrk).trans hkU
  rw [sum_eq_single_of_mem r hrU, if_pos hrd, ←he, Nat.mul_div_cancel_left a (pow_pos hr _),
    liouville_apply_mul, liouville_square hr.ne', one_mul, liouville_apply ha.ne',
    moebius_apply_of_squarefree hsq]
  intro d _ hdr
  split_ifs with hd
  · apply moebius_eq_zero_of_not_squarefree
    intro hs
    have hd0 : d ≠ 0 := by rintro rfl; simp_all
    have hed : d^2 * (k/d^2) = k := Nat.mul_div_cancel' hd
    apply hdr
    apply Nat.dvd_antisymm
    · exact (square_divisor_iff hr.ne' hsq).mp (he ▸ hd)
    · apply (square_divisor_iff hd0 hs).mp
      simpa only [hed] using hrd
  · rfl

private theorem harmonic_squares (U : ℕ) :
    reducedLiouvilleHarmonic 1 U =
    ∑ d ∈ range (U+1), (∑ j ∈ range (U/d^2+1), (moebius j : ℝ) / j) / (d:ℝ)^2 := by
  classical
  rw [harmonic_as_range]
  let f (d k : ℕ) : ℝ := (moebius (k/d^2) : ℝ) / k
  calc _ = ∑ k ∈ range (U+1), ∑ d ∈ range (U+1), if d^2 ∣ k then f d k else 0 := by
          apply sum_congr rfl
          intro k hk
          have he := liouville_from_squares k U (Nat.le_of_lt_succ (mem_range.mp hk))
          rw [if_pos (Nat.coprime_one_right k),he,Int.cast_sum,Finset.sum_div]
          apply sum_congr rfl
          intro d _
          by_cases h : d^2 ∣ k <;> simp [h,f]
       _ = ∑ d ∈ range (U+1), ∑ k ∈ range (U+1), if d^2 ∣ k then f d k else 0 := sum_comm
       _ = _ := by
          apply sum_congr rfl
          intro d _
          by_cases hd : d = 0
          · simp [f,hd]
          have hdp := pow_pos (Nat.pos_of_ne_zero hd) 2
          rw [sum_multiples_upto U (d^2) hdp,Finset.sum_div]
          apply sum_congr rfl
          intro j _
          simp only [f,Nat.mul_div_cancel_left _ hdp,Nat.cast_mul,Nat.cast_pow]
          ring

theorem solution
    (σ C : ℝ) (hhalf : 1/2 < σ) (hone : σ ≤ 1) (hC : 0 ≤ C)
    (H : ∀ U : ℕ, |∑ j ∈ range (U+1), (moebius j : ℝ) / j| ≤ C * ((U:ℝ)+1)^(σ-1))
    (U : ℕ) :
    |reducedLiouvilleHarmonic 1 U| ≤
      (C * ∑' d : ℕ, ((d:ℝ)^(2*σ))⁻¹) * ((U:ℝ)+1)^(σ-1) := by
  classical
  let w (d : ℕ) := ((d:ℝ)^(2*σ))⁻¹
  have hsum : Summable w := Real.summable_nat_rpow_inv.mpr (by linarith)
  let K := C*((U:ℝ)+1)^(σ-1)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hw (d : ℕ) : 0 ≤ w d := by dsimp [w]; positivity
  rw [harmonic_squares]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc _ ≤ ∑ d ∈ range (U+1), K*w d := by
          apply sum_le_sum
          intro d _
          by_cases hd : d = 0
          · simpa [hd] using mul_nonneg hK (hw 0)
          have hdpos : (0:ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
          rw [abs_div,abs_of_nonneg (sq_nonneg (d:ℝ))]
          apply (div_le_div_of_nonneg_right (H _) (sq_nonneg _)).trans
          have he := div_floor_power_bound U (d^2) (pow_pos (Nat.pos_of_ne_zero hd) _) σ hone
          rw [Nat.cast_pow] at he
          have hp : ((d:ℝ)^2)^(-σ) = w d := by
            dsimp [w]; rw [Real.rpow_neg (sq_nonneg _),Real.rpow_mul hdpos.le]; norm_num
          rw [hp] at he
          calc _ = C * ((((U/d^2):ℕ)+1:ℝ)^(σ-1)/(d:ℝ)^2) := by ring
               _ ≤ _ := by dsimp [K]; simpa only [mul_assoc] using mul_le_mul_of_nonneg_left he hC
       _ = K*∑ d ∈ range (U+1), w d := (mul_sum ..).symm
       _ ≤ K*∑' d, w d := mul_le_mul_of_nonneg_left (hsum.sum_le_tsum _ (fun i _ => hw i)) hK
       _ = _ := by dsimp [w,K]; ring

