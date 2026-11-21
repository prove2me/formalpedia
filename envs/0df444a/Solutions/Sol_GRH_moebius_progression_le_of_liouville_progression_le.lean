-- Prove2me | solution 1 for GRH.moebius_progression_le_of_liouville_progression_le
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T00:26:13.315832+00:00
-- url     : https://prove2.me/submissions/b5f502fa-6756-43ab-a8d6-535a8ff91315

import Mathlib

open Finset ArithmeticFunction
open scoped BigOperators zeta Moebius


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

private theorem moebius_square_sum (k N : ℕ) (hkN : k ≤ N) :
    moebius k = ∑ d ∈ range (N+1),
      if d^2 ∣ k then moebius d * liouville (k/d^2) else 0 := by
  by_cases hk : k = 0
  · simp [hk]
  obtain ⟨a,r,ha,hr,hra,hsq⟩ := Nat.sq_mul_squarefree_of_pos (Nat.pos_of_ne_zero hk)
  have hdiv (d : ℕ) : d^2 ∣ k ↔ d ∣ r := hra ▸ square_divisor_iff hr.ne' hsq
  have hrk : r ∣ k := by rw [←hra]; exact (dvd_pow_self r two_ne_zero).trans (dvd_mul_right _ _)
  have hrN : r ≤ N := (Nat.le_of_dvd (Nat.pos_of_ne_zero hk) hrk).trans hkN
  have hset : (range (N+1)).filter (fun d => d^2 ∣ k) = r.divisors := by
    ext d
    simp only [mem_filter,mem_range,Nat.mem_divisors,hdiv]
    constructor
    · rintro ⟨_,h⟩; exact ⟨h,hr.ne'⟩
    · rintro ⟨h,_⟩; exact ⟨Nat.lt_succ_of_le ((Nat.le_of_dvd hr h).trans hrN),h⟩
  rw [←Finset.sum_filter,hset]
  calc moebius k = (if r = 1 then 1 else 0) * liouville k := by
          by_cases hr1 : r = 1
          · have hka : k = a := by simpa [hr1] using hra.symm
            simp [hr1,hka,moebius_apply_of_squarefree hsq,liouville_apply ha.ne']
          · have hns : ¬Squarefree k := by
              intro h
              have hrr : r*r ∣ k := by rw [←hra,pow_two]; exact dvd_mul_right _ _
              exact hr1 (Nat.isUnit_iff.mp (h r hrr))
            simp [hr1,moebius_eq_zero_of_not_squarefree hns]
       _ = (∑ d ∈ r.divisors, moebius d) * liouville k := by
          have H := DFunLike.congr_fun moebius_mul_coe_zeta r
          rw [coe_mul_zeta_apply,one_apply] at H
          rw [H]
       _ = _ := by
          rw [sum_mul]
          apply sum_congr rfl
          intro d hd
          have hdk := (hdiv d).mpr (Nat.dvd_of_mem_divisors hd)
          have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
          have hl : liouville k = liouville (k/d^2) := by
            calc liouville k = liouville ((k/d^2)*d^2) := by rw [Nat.div_mul_cancel hdk]
                 _ = _ := by rw [liouville_apply_mul,liouville_square hd0,mul_one]
          rw [hl]

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

private theorem moebius_progression_sieve (q : ℕ) [NeZero q] (a : ZMod q) (N : ℕ) :
    (∑ k ∈ range (N+1), if (k : ZMod q) = a then (moebius k : ℝ) else 0) =
    ∑ d ∈ range (N+1), (moebius d : ℝ) *
      ∑ j ∈ range (N/d^2+1), if ((d^2*j:ℕ):ZMod q) = a then (liouville j : ℝ) else 0 := by
  classical
  let F (d k : ℕ) : ℝ := (moebius d:ℝ) * (if (k:ZMod q) = a then (liouville (k/d^2):ℝ) else 0)
  calc _ = ∑ k ∈ range (N+1), ∑ d ∈ range (N+1), if d^2 ∣ k then F d k else 0 := by
          apply sum_congr rfl
          intro k hk
          by_cases hka : (k:ZMod q) = a
          · simp only [hka,if_true,F]
            exact_mod_cast moebius_square_sum k N (Nat.le_of_lt_succ (mem_range.mp hk))
          · simp [hka,F]
       _ = ∑ d ∈ range (N+1), ∑ k ∈ range (N+1), if d^2 ∣ k then F d k else 0 := sum_comm
       _ = _ := by
          apply sum_congr rfl
          intro d hd
          by_cases hd0 : d = 0
          · simp [hd0,F]
          rw [sum_multiples_upto N (d^2) (pow_pos (Nat.pos_of_ne_zero hd0) _),mul_sum]
          apply sum_congr rfl
          intro j hj
          simp only [F,Nat.mul_div_cancel_left _ (pow_pos (Nat.pos_of_ne_zero hd0) _)]

private theorem bound_permuted_class (q : ℕ) [NeZero q] (a t : ZMod q) (ha : IsUnit a)
    (N : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (H : ∀ c : ZMod q, IsUnit c →
      |∑ j ∈ range (N+1), if (j:ZMod q) = c then (liouville j:ℝ) else 0| ≤ b) :
    |∑ j ∈ range (N+1), if t*(j:ZMod q) = a then (liouville j:ℝ) else 0| ≤ b := by
  classical
  by_cases ht : IsUnit t
  · let u := ht.unit
    have hu : (u : ZMod q) = t := ht.unit_spec
    let c : ZMod q := (↑u⁻¹ : ZMod q)*a
    have hc : IsUnit c := u⁻¹.isUnit.mul ha
    have hi (j : ℕ) : t*(j:ZMod q) = a ↔ (j:ZMod q) = c := by
      rw [←hu]
      change (u : ZMod q) * (j : ZMod q) = a ↔ (j : ZMod q) = (↑u⁻¹ : ZMod q) * a
      constructor
      · intro h
        exact ((u.inv_mul_eq_iff_eq_mul).mpr h.symm).symm
      · intro h
        exact ((u.inv_mul_eq_iff_eq_mul).mp h.symm).symm
    simpa only [hi] using H c hc
  · have hn (j : ℕ) : t*(j:ZMod q) ≠ a := fun h => ht (isUnit_of_mul_isUnit_left (h ▸ ha))
    simpa [hn] using hb

theorem solution
    (q : ℕ) [NeZero q] (σ C : ℝ) (hσ : 1/2 < σ) (hC : 0 ≤ C)
    (H : ∀ a : ZMod q, IsUnit a → ∀ N : ℕ,
      |∑ j ∈ range (N+1), if (j:ZMod q)=a then (liouville j:ℝ) else 0| ≤ C*((N:ℝ)+1)^σ)
    (a : ZMod q) (ha : IsUnit a) (N : ℕ) :
    |∑ k ∈ range (N+1), if (k:ZMod q)=a then (moebius k:ℝ) else 0| ≤
      (C * (2:ℝ)^σ * ∑' d : ℕ, ((d:ℝ)^(2*σ))⁻¹) * ((N:ℝ)+1)^σ := by
  classical
  let w (d : ℕ) := ((d:ℝ)^(2*σ))⁻¹
  have hσ0 : 0 ≤ σ := by linarith
  have hsum : Summable w := Real.summable_nat_rpow_inv.mpr (by linarith)
  have hw (d : ℕ) : 0 ≤ w d := by dsimp [w]; positivity
  let K := C*(2:ℝ)^σ*((N:ℝ)+1)^σ
  have hK : 0 ≤ K := by dsimp [K]; positivity
  rw [moebius_progression_sieve]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc _ ≤ ∑ d ∈ range (N+1), K*w d := by
          apply sum_le_sum
          intro d hd
          by_cases hd0 : d = 0
          · simpa [hd0] using mul_nonneg hK (hw 0)
          by_cases hdn : d^2 ≤ N
          · let t : ZMod q := (d^2 : ℕ)
            have hperm := bound_permuted_class q a t ha (N/d^2) (C*((N/d^2:ℕ)+1:ℝ)^σ)
              (by positivity) (fun c hc => H c hc _)
            have ht (j : ℕ) : ((d^2*j:ℕ):ZMod q) = t*(j:ZMod q) := by simp [t]
            simp_rw [ht]
            rw [abs_mul]
            have habs : |(moebius d:ℝ)| ≤ 1 := by exact_mod_cast (abs_moebius_le_one (n:=d))
            apply (mul_le_mul habs hperm (abs_nonneg _) zero_le_one).trans
            rw [one_mul]
            have hdpos : (0:ℝ)<d := by exact_mod_cast Nat.pos_of_ne_zero hd0
            have hds : (0:ℝ)<(d:ℝ)^2 := sq_pos_of_pos hdpos
            have hdiv : (N/d^2:ℕ) ≤ (N:ℝ)/(d:ℝ)^2 := by
              apply (le_div_iff₀ hds).mpr
              exact_mod_cast Nat.div_mul_le_self N (d^2)
            have hsN : (d:ℝ)^2 ≤ N := by exact_mod_cast hdn
            have hx : (N/d^2:ℕ)+1 ≤ (2*((N:ℝ)+1))/(d:ℝ)^2 := by
              apply (le_div_iff₀ hds).mpr
              have hb := (le_div_iff₀ hds).mp hdiv
              nlinarith
            have hp := Real.rpow_le_rpow (by positivity) hx hσ0
            apply (mul_le_mul_of_nonneg_left hp hC).trans_eq
            dsimp [K,w]
            rw [Real.div_rpow (by positivity) (by positivity),Real.mul_rpow (by positivity) (by positivity)]
            have hpower : ((d:ℝ)^2) ^ σ = (d:ℝ)^(2*σ) := by
              rw [Real.rpow_mul hdpos.le]
              norm_num
            rw [hpower]
            ring
          · have hzero : N / d^2 = 0 := Nat.div_eq_of_lt (lt_of_not_ge hdn)
            simp [hzero, mul_nonneg hK (hw d)]
       _ = K * ∑ d ∈ range (N+1), w d := (mul_sum ..).symm
       _ ≤ K * ∑' d, w d := mul_le_mul_of_nonneg_left (hsum.sum_le_tsum _ (fun i _ => hw i)) hK
       _ = _ := by dsimp [K,w]; ring

