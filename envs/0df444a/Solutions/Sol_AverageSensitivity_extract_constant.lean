-- Prove2me | solution 1 for AverageSensitivity.extract_constant
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-16T12:52:20.211394+00:00
-- url     : https://prove2.me/submissions/e6d000f0-1aac-4898-87ba-4e200bb8521d

import Mathlib
import Definitions.Def_AverageSensitivity_Constants3762


open scoped BigOperators
namespace AverageSensitivity



theorem abs_walk_step (n j : ℕ) :
    |2*(j:ℝ)-(n:ℝ)-1|+|2*(j:ℝ)-(n:ℝ)+1| =
      2*|2*(j:ℝ)-(n:ℝ)| + if 2*j=n then 2 else 0 := by
  split_ifs with h
  · have he : 2*(j:ℝ)=(n:ℝ) := by exact_mod_cast h
    norm_num [he]
  · by_cases hlt : 2*j<n
    · have hr : 2*(j:ℝ)+1 ≤ (n:ℝ) := by exact_mod_cast hlt
      rw [abs_of_nonpos (by linarith),abs_of_nonpos (by linarith),abs_of_nonpos (by linarith)]
      ring
    · have hgt : n+1≤2*j := by omega
      have hr : (n:ℝ)+1≤2*(j:ℝ) := by exact_mod_cast hgt
      rw [abs_of_nonneg (by linarith),abs_of_nonneg (by linarith),abs_of_nonneg (by linarith)]
      ring

theorem rawMAD_succ (n : ℕ) :
    rawMAD (n+1) = 2*rawMAD n +
      ∑ j ∈ Finset.range (n+1), (n.choose j : ℝ)*(if 2*j=n then 2 else 0) := by
  unfold rawMAD
  rw [Finset.sum_choose_succ_mul (fun j _ => |2*(j:ℝ)-((n+1:ℕ):ℝ)|) n]
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ j ∈ Finset.range (n+1), (n.choose j : ℝ)*
        (2*|2*(j:ℝ)-(n:ℝ)|+(if 2*j=n then 2 else 0)) := by
      apply Finset.sum_congr rfl
      intro j _
      push_cast
      have h := abs_walk_step n j
      have he : 2*((j:ℝ)+1)-((n:ℝ)+1)=2*(j:ℝ)-(n:ℝ)+1 := by ring
      rw [he]
      rw [show 2*(j:ℝ)-((n:ℝ)+1)=2*(j:ℝ)-(n:ℝ)-1 by ring]
      rw [← mul_add, h]
    _ = _ := by
      simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intros
      ring

theorem rawMAD_succ_even (k : ℕ) :
    rawMAD (2*k+1) = 2*rawMAD (2*k)+2*((2*k).choose k : ℝ) := by
  rw [rawMAD_succ]
  congr 1
  rw [Finset.sum_eq_single k]
  · simp
    ring
  · intro j _ hj
    have h : ¬2*j=2*k := by omega
    simp [h]
  · simp
    omega

theorem rawMAD_succ_odd (k : ℕ) :
    rawMAD (2*k+2) = 2*rawMAD (2*k+1) := by
  have h := rawMAD_succ (2*k+1)
  have hz : (∑ j ∈ Finset.range (2*k+1+1), ((2*k+1).choose j : ℝ)*
      (if 2*j=2*k+1 then 2 else 0))=0 := by
    apply Finset.sum_eq_zero
    intro j _
    have he : ¬2*j=2*k+1 := by omega
    simp [he]
  simpa only [hz,add_zero] using h

theorem rawMAD_even (k : ℕ) :
    rawMAD (2*k) = 2*(k:ℝ)*(Nat.centralBinom k : ℝ) := by
  induction k with
  | zero => norm_num [rawMAD, Nat.centralBinom]
  | succ k ih =>
    have he := rawMAD_succ_even k
    have ho := rawMAD_succ_odd k
    have hc : ((k:ℝ)+1)*(Nat.centralBinom (k+1):ℝ) =
        2*(2*(k:ℝ)+1)*(Nat.centralBinom k:ℝ) := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ k
    rw [show 2*(k+1)=2*k+2 by omega,ho,he,ih]
    simp only [Nat.cast_add,Nat.cast_one,Nat.centralBinom] at *
    nlinarith

theorem rawMAD_odd (k : ℕ) :
    rawMAD (2*k+1) = 2*(2*(k:ℝ)+1)*(Nat.centralBinom k : ℝ) := by
  rw [rawMAD_succ_even,rawMAD_even]
  simp only [Nat.centralBinom]
  ring




theorem mad_even (k : ℕ) : mad (2*k) = (k:ℝ)*central k := by
  simp only [mad,rawMAD_even,central,pow_mul]
  norm_num
  ring

theorem mad_odd (k : ℕ) : mad (2*k+1) = (2*(k:ℝ)+1)*central k/2 := by
  simp only [mad,rawMAD_odd,central,pow_add,pow_mul]
  norm_num
  ring

theorem central_step (k : ℕ) :
    (2*(k:ℝ)+2)*central (k+1) = (2*(k:ℝ)+1)*central k := by
  have hc : ((k:ℝ)+1)*(Nat.centralBinom (k+1):ℝ) =
        2*(2*(k:ℝ)+1)*(Nat.centralBinom k:ℝ) := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ k
  unfold central
  rw [pow_succ]
  field_simp
  nlinarith

end AverageSensitivity


open scoped BigOperators
namespace AverageSensitivity

theorem central_tail (k : ℕ) (hk : 10 ≤ k) :
    central k ^ 2 * ((157/50:ℝ)*(k:ℝ)+1727/2150) ≤ 1 := by
  induction k, hk using Nat.le_induction with
  | base => norm_num [central, Nat.centralBinom, Nat.choose]
  | succ k hk ih =>
    have hc := central_step k
    have hkR : (10:ℝ)≤(k:ℝ) := by exact_mod_cast hk
    have hgap : 0 ≤ (2*(k:ℝ)+2)^2*((157/50:ℝ)*(k:ℝ)+1727/2150) -
        (2*(k:ℝ)+1)^2*((157/50:ℝ)*((k:ℝ)+1)+1727/2150) := by
      nlinarith
    have hmul := mul_nonneg (sq_nonneg (central k)) hgap
    have hpos : 0 < (2*(k:ℝ)+2)^2 := sq_pos_of_pos (by positivity)
    have he : (2*(k:ℝ)+2)^2 * (central (k+1)^2 *
        ((157/50:ℝ)*((k:ℝ)+1)+1727/2150)) =
        central k^2*((2*(k:ℝ)+1)^2*((157/50:ℝ)*((k:ℝ)+1)+1727/2150)) := by
      calc
        _ = ((2*(k:ℝ)+2)*central (k+1))^2 *
            ((157/50:ℝ)*((k:ℝ)+1)+1727/2150) := by ring
        _ = ((2*(k:ℝ)+1)*central k)^2 *
            ((157/50:ℝ)*((k:ℝ)+1)+1727/2150) := by rw [hc]
        _ = _ := by ring
    have hi := mul_le_mul_of_nonneg_left ih hpos.le
    push_cast
    apply (mul_le_mul_iff_right₀ hpos).mp
    nlinarith [he]

theorem mad_nonneg (n : ℕ) : 0 ≤ mad n := by
  unfold mad rawMAD
  positivity

theorem mad_tail_squared (n : ℕ) (hn : 20 ≤ n) :
    64*mad n^2 ≤ (34400/3297:ℝ)*(n:ℝ) := by
  let k := n/2
  have hk : 10 ≤ k := by dsimp [k]; omega
  have hkR : (10:ℝ)≤(k:ℝ) := by exact_mod_cast hk
  have htail := central_tail k hk
  have hL : 0≤(157/50:ℝ)*(k:ℝ)+1727/2150 := by positivity
  have hcentral : 0≤central k^2 := sq_nonneg _
  have hform : n=2*k ∨ n=2*k+1 := by dsimp [k]; omega
  rcases hform with he | ho
  · rw [he,mad_even]
    push_cast
    have hlinear : 64*(k:ℝ)^2 ≤ (34400/3297:ℝ)*(2*(k:ℝ))*
        ((157/50:ℝ)*(k:ℝ)+1727/2150) := by nlinarith [sq_nonneg (k:ℝ)]
    calc
      _ = 64*(k:ℝ)^2*central k^2 := by ring
      _ ≤ ((34400/3297:ℝ)*(2*(k:ℝ))*((157/50:ℝ)*(k:ℝ)+1727/2150))*central k^2 :=
        mul_le_mul_of_nonneg_right hlinear hcentral
      _ = (34400/3297:ℝ)*(2*(k:ℝ))*(central k^2*((157/50:ℝ)*(k:ℝ)+1727/2150)) := by ring
      _ ≤ (34400/3297:ℝ)*(2*(k:ℝ))*1 := mul_le_mul_of_nonneg_left htail (by positivity)
      _ = _ := by ring
  · rw [ho,mad_odd]
    push_cast
    have hlinear : 16*(2*(k:ℝ)+1) ≤ (34400/3297:ℝ)*
        ((157/50:ℝ)*(k:ℝ)+1727/2150) := by nlinarith
    have hlinear2 := mul_le_mul_of_nonneg_right hlinear (show 0≤2*(k:ℝ)+1 by positivity)
    calc
      _ = (16*(2*(k:ℝ)+1)*(2*(k:ℝ)+1))*central k^2 := by ring
      _ ≤ ((34400/3297:ℝ)*((157/50:ℝ)*(k:ℝ)+1727/2150)*(2*(k:ℝ)+1))*central k^2 :=
        mul_le_mul_of_nonneg_right hlinear2 hcentral
      _ = (34400/3297:ℝ)*(2*(k:ℝ)+1)*(central k^2*((157/50:ℝ)*(k:ℝ)+1727/2150)) := by ring
      _ ≤ (34400/3297:ℝ)*(2*(k:ℝ)+1)*1 := mul_le_mul_of_nonneg_left htail (by positivity)
      _ = _ := by ring

theorem small_numeric (n : ℕ) (hn : 15 ≤ n) (hn' : n < 20) :
    (8*mad n+2)^2 ≤ (1881/500:ℝ)^2*(n:ℝ) := by
  interval_cases n <;>
    norm_num [mad,rawMAD,Finset.sum_range_succ,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem extract_constant (n d : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d)
    (A : ℝ) (htrivial : A ≤ (n:ℝ))
    (hrefined : A ≤ 8*(d:ℝ)*mad n+2*(d:ℝ)^2) :
    A ≤ (1881/500:ℝ)*(d:ℝ)*Real.sqrt (n:ℝ) := by
  have hs0 := Real.sqrt_nonneg (n:ℝ)
  have hs2 := Real.sq_sqrt (Nat.cast_nonneg n)
  have hn0 : (0:ℝ)≤(n:ℝ) := Nat.cast_nonneg n
  have hd0 : (1:ℝ)≤(d:ℝ) := by exact_mod_cast hd
  by_cases ht : (n:ℝ) ≤ (1881/500:ℝ)^2*(d:ℝ)^2
  · have hscale : Real.sqrt (n:ℝ) ≤ (1881/500:ℝ)*(d:ℝ) := by
      nlinarith
    have hm := mul_le_mul_of_nonneg_right hscale hs0
    nlinarith
  · have hscale : (1881/500:ℝ)*(d:ℝ) < Real.sqrt (n:ℝ) := by
      nlinarith
    by_cases hlarge : 20 ≤ n
    · have hm2 := mad_tail_squared n hlarge
      have hm0 := mad_nonneg n
      have hcoef : (34400/3297:ℝ) < (1881/500-2/(1881/500):ℝ)^2 := by norm_num
      have hmn := mul_le_mul_of_nonneg_right hcoef.le hn0
      have hmad : 8*mad n ≤ (1881/500-2/(1881/500):ℝ)*Real.sqrt (n:ℝ) := by
        have hsquare : (8*mad n)^2 ≤
            ((1881/500-2/(1881/500):ℝ)*Real.sqrt (n:ℝ))^2 := by
          simp only [mul_pow,hs2]
          nlinarith
        have hpos : 0 ≤ (1881/500-2/(1881/500):ℝ)*Real.sqrt (n:ℝ) := by positivity
        nlinarith
      have hi : 8*mad n+2*(d:ℝ) ≤ (1881/500:ℝ)*Real.sqrt (n:ℝ) := by
        nlinarith
      have hm := mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg d)
      nlinarith
    · have hnR : (n:ℝ)≤19 := by exact_mod_cast (show n≤19 by omega)
      have hd1 : d=1 := by
        by_contra he
        have hd2 : (2:ℝ)≤(d:ℝ) := by exact_mod_cast (show 2≤d by omega)
        nlinarith [sq_nonneg ((d:ℝ)-2)]
      subst d
      norm_num at ht hscale hrefined ⊢
      have hn15 : 15≤n := by
        have : (14:ℝ)<(n:ℝ) := by nlinarith
        exact_mod_cast this
      have hm2 := small_numeric n hn15 (by omega)
      have hm0 := mad_nonneg n
      have hsquare : (8*mad n+2)^2 ≤ ((1881/500:ℝ)*Real.sqrt (n:ℝ))^2 := by
        rw [mul_pow,hs2]
        exact hm2
      have hpos : 0≤(1881/500:ℝ)*Real.sqrt (n:ℝ) := by positivity
      nlinarith

end AverageSensitivity

theorem solution : type_of% @AverageSensitivity.extract_constant := @AverageSensitivity.extract_constant
