-- Prove2me | solution 1 for GRH.reduced_moebius_harmonic_le_of_liouville_harmonic_le
-- status  : ACCEPTED   (prove)
-- author  : @pragyan
-- created : 2026-11-21T01:58:17.090846+00:00
-- url     : https://prove2.me/submissions/9a935e9f-4fc3-4041-acc4-21b4b557f038

import Mathlib
import Definitions.Def_GRH_MoebiusBilinear

/-!
Finite square-divisor reindexing adapted from marozols's Apache-2.0 Prove2Me
proofs of GRH.moebius_progression_le_of_liouville_progression_le and
GRH.liouville_harmonic_le_of_moebius_harmonic_le.
-/
open Finset ArithmeticFunction GRH
open scoped BigOperators zeta Moebius

private theorem harmonic_as_range (q U : ℕ) [NeZero q] :
    reducedLiouvilleHarmonic q U = ∑ n ∈ range (U+1),
      if Nat.Coprime n q then (liouville n : ℝ) / n else 0 := by
  classical
  unfold reducedLiouvilleHarmonic
  simp_rw [ZMod.isUnit_iff_coprime]
  have he : range (U+1) = insert 0 (Ioc 0 U) := by ext k; simp
  rw [he,sum_insert (by simp)]
  simp

private theorem moebius_harmonic_as_range (q U : ℕ) [NeZero q] :
    reducedMoebiusHarmonic q U = ∑ n ∈ range (U+1),
      if Nat.Coprime n q then (moebius n : ℝ) / n else 0 := by
  classical
  unfold reducedMoebiusHarmonic
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


private theorem moebius_harmonic_squares (q U : ℕ) [NeZero q] :
    reducedMoebiusHarmonic q U =
      ∑ d ∈ range (U+1), if Nat.Coprime d q then
        (moebius d : ℝ) * reducedLiouvilleHarmonic q (U/d^2) / (d : ℝ)^2 else 0 := by
  classical
  rw [moebius_harmonic_as_range]
  let F (d k : ℕ) : ℝ := (moebius d : ℝ) *
    (if Nat.Coprime k q then (liouville (k/d^2) : ℝ) / (k : ℝ) else 0)
  calc
    _ = ∑ k ∈ range (U+1), ∑ d ∈ range (U+1), if d^2 ∣ k then F d k else 0 := by
      apply sum_congr rfl
      intro k hk
      by_cases hka : Nat.Coprime k q
      · rw [if_pos hka, moebius_square_sum k U (Nat.le_of_lt_succ (mem_range.mp hk)),
          Int.cast_sum, Finset.sum_div]
        apply sum_congr rfl
        intro d _
        by_cases hd : d^2 ∣ k <;> simp [F, hka, hd, Int.cast_mul, mul_div_assoc]
      · simp [hka,F]
    _ = ∑ d ∈ range (U+1), ∑ k ∈ range (U+1), if d^2 ∣ k then F d k else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro d _
      by_cases hd : d = 0
      · simp [hd,F]
      have hdp : 0 < d^2 := pow_pos (Nat.pos_of_ne_zero hd) 2
      rw [sum_multiples_upto U (d^2) hdp]
      by_cases hdq : Nat.Coprime d q
      · rw [if_pos hdq, harmonic_as_range, Finset.mul_sum, Finset.sum_div]
        apply sum_congr rfl
        intro j _
        simp only [F, Nat.mul_div_cancel_left _ hdp, Nat.cast_mul, Nat.cast_pow,
          Nat.coprime_mul_iff_left, Nat.coprime_pow_left_iff (by norm_num : 0 < 2),
          hdq, true_and]
        split_ifs <;> simp_all <;> ring
      · rw [if_neg hdq]
        apply sum_eq_zero
        intro j _
        simp [F, Nat.coprime_mul_iff_left,
          Nat.coprime_pow_left_iff (by norm_num : 0 < 2), hdq]

theorem solution
    (q : ℕ) [NeZero q] (σ C : ℝ) (hhalf : 1/2 < σ) (hone : σ ≤ 1) (hC : 0 ≤ C)
    (H : ∀ U : ℕ, |reducedLiouvilleHarmonic q U| ≤ C * ((U : ℝ)+1)^(σ-1))
    (U : ℕ) :
    |reducedMoebiusHarmonic q U| ≤
      (C * ∑' d : ℕ, ((d : ℝ)^(2*σ))⁻¹) * ((U : ℝ)+1)^(σ-1) := by
  classical
  let w (d : ℕ) := ((d : ℝ)^(2*σ))⁻¹
  have hsum : Summable w := Real.summable_nat_rpow_inv.mpr (by linarith)
  let K := C*((U : ℝ)+1)^(σ-1)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hw (d : ℕ) : 0 ≤ w d := by dsimp [w]; positivity
  rw [moebius_harmonic_squares]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ d ∈ range (U+1), K*w d := by
      apply sum_le_sum
      intro d _
      by_cases hd : d = 0
      · simpa [hd] using mul_nonneg hK (hw 0)
      by_cases hdq : Nat.Coprime d q
      · rw [if_pos hdq, abs_div, abs_mul, abs_of_nonneg (sq_nonneg (d : ℝ))]
        have habs : |(moebius d : ℝ)| ≤ 1 := by exact_mod_cast (abs_moebius_le_one (n := d))
        have hnum := mul_le_mul habs (H (U/d^2)) (abs_nonneg _) zero_le_one
        rw [one_mul] at hnum
        apply (div_le_div_of_nonneg_right hnum (sq_nonneg _)).trans
        have hdpos : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
        have he := div_floor_power_bound U (d^2) (pow_pos (Nat.pos_of_ne_zero hd) _) σ hone
        rw [Nat.cast_pow] at he
        have hp : ((d : ℝ)^2)^(-σ) = w d := by
          dsimp [w]
          rw [Real.rpow_neg (sq_nonneg _), Real.rpow_mul hdpos.le]
          norm_num
        rw [hp] at he
        calc
          _ = C * ((((U/d^2) : ℕ)+1 : ℝ)^(σ-1)/(d : ℝ)^2) := by ring
          _ ≤ _ := by dsimp [K]; simpa only [mul_assoc] using mul_le_mul_of_nonneg_left he hC
      · simpa [hdq] using mul_nonneg hK (hw d)
    _ = K * ∑ d ∈ range (U+1), w d := (mul_sum ..).symm
    _ ≤ K * ∑' d, w d := mul_le_mul_of_nonneg_left (hsum.sum_le_tsum _ (fun i _ => hw i)) hK
    _ = _ := by dsimp [w,K]; ring
