-- Prove2me | solution 1 for DetDLP.D3Stopped.d3_stopped_schedule_poly
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T06:05:00.652439+00:00
-- url     : https://prove2.me/submissions/57e0d926-3f92-4d2a-b9d3-3dfa51b1a6c0

import Definitions.Def_DetDLP_D3StoppedSchedule
set_option autoImplicit false
open DetDLP.D3Stopped DetDLP.AppendixD4
private theorem term_bound (S j : ℕ) :
    (((S : ℝ) / (8 : ℝ)^j) / Real.sqrt (width S j : ℝ)) * Real.sqrt (level S : ℝ) ≤
      512 * S * (1/2 : ℝ)^j := by
  let L := level S; let u := width S j
  change _ / Real.sqrt (u:ℝ) * Real.sqrt (L:ℝ) ≤ _
  by_cases hu : u=0
  · simp [hu]
  have hb : 0 < 131072*2^j := by positivity
  have hdiv : L / (131072*2^j) = u := (Nat.div_div_eq_div_mul ..).symm
  have hlt : L < (u+1)*(131072*2^j) := (Nat.div_lt_iff_lt_mul hb).1 (by omega)
  have hu' : u+1 ≤ 2*u := by omega
  have hle := hlt.le.trans (Nat.mul_le_mul_right (131072*2^j) hu')
  have hr : (L:ℝ) ≤ (2*(u:ℝ))*(131072*(2:ℝ)^j) := by exact_mod_cast hle
  have hu0 : 0 < (u:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hu
  have hj : 1 ≤ (2:ℝ)^j := one_le_pow₀ (by norm_num)
  have hs := Real.sq_sqrt hu0.le
  have ht := Real.sq_sqrt (show (0:ℝ) ≤ L by positivity)
  have h1 : Real.sqrt (L:ℝ) ≤ (512*(2:ℝ)^j)*Real.sqrt (u:ℝ) := by
    apply le_of_pow_le_pow_left₀ (n:=2) (by decide) (by positivity)
    rw [mul_pow,hs,ht,mul_pow]
    nlinarith [mul_nonneg (sub_nonneg.mpr hj) (show 0 ≤ (u:ℝ)*(2:ℝ)^j by positivity)]
  calc
    _ ≤ (((S:ℝ)/8^j)/Real.sqrt (u:ℝ))*((512*2^j)*Real.sqrt (u:ℝ)) := by gcongr
    _ = 512*S*(1/4:ℝ)^j := by
      have he : (1/4:ℝ)^j = (2:ℝ)^j/8^j := by rw [← div_pow]; norm_num
      rw [he]; field_simp [ne_of_gt (Real.sqrt_pos.2 hu0)]
    _ ≤ _ := by gcongr; norm_num
private theorem geometric (n : ℕ) : ∑ j : Fin n, (1/2 : ℝ)^j.val ≤ 2 := by
  rw [Fin.sum_univ_eq_sum_range]; have h := geom_sum_mul_neg (1/2:ℝ) n
  nlinarith [show (0:ℝ) ≤ (1/2:ℝ)^n by positivity]
private theorem thresh_work (S : ℕ) (hS : 2 ≤ S) : (threshold S:ℝ) * Real.sqrt (level S:ℝ) ≤ 4*S := by
  let L := level S; let r := L.sqrt
  have hL : 0 < L := (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).2 (by omega)
  have hr : 1 ≤ r := Nat.le_sqrt.2 (by omega)
  have hLS : L ≤ S := Nat.clog_le_of_le_pow (Nat.lt_pow_self (n:=S) (by decide : 1 < 2)).le
  have hrs : r ≤ S := (Nat.sqrt_le_self L).trans hLS
  have hh : threshold S * r ≤ S+r := by
    unfold threshold; change (S+r-1)/max 1 r*r ≤ _; rw [max_eq_right hr]; exact (Nat.div_mul_le_self ..).trans (Nat.sub_le ..)
  have ht := Nat.lt_succ_sqrt' L
  have hrt : Real.sqrt (L:ℝ) ≤ 2*(r:ℝ) := by
    apply (Real.sqrt_le_iff).2; refine ⟨by positivity,?_⟩
    have : (L:ℝ) < ((r:ℝ)+1)^2 := by exact_mod_cast ht
    have hr1 : (1:ℝ) ≤ r := by exact_mod_cast hr
    nlinarith [sq_nonneg ((r:ℝ)-1)]
  change _ * Real.sqrt (L:ℝ) ≤ _
  have h' : (threshold S:ℝ)*r ≤ S+(r:ℝ) := by exact_mod_cast hh
  have h'' : (r:ℝ) ≤ S := by exact_mod_cast hrs
  nlinarith [mul_le_mul_of_nonneg_left hrt (show 0 ≤ (threshold S:ℝ) by positivity)]
theorem solution (C S M d₀ : ℕ) (hS : 2 ≤ S) :
    exponent (schedule C S M d₀) S ≤ 1028*S/Real.sqrt (level S : ℝ) := by
  have hL : 0 < level S := (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).2 (by omega)
  apply (le_div_iff₀ (Real.sqrt_pos.2 (by exact_mod_cast hL))).2
  let s := schedule C S M d₀
  change (s.H + ∑ j : Fin s.D, (S:ℝ)/8^(d₀+j.val)/Real.sqrt (width S (d₀+j.val):ℝ)) * _ ≤ _
  rw [add_mul,Finset.sum_mul]
  have ht : (s.H:ℝ)*Real.sqrt (level S:ℝ) ≤ 4*S := le_trans (by gcongr; exact_mod_cast min_le_right M (threshold S)) (thresh_work S hS)
  have hsum : (∑ j : Fin s.D, ((S:ℝ)/8^(d₀+j.val)/Real.sqrt (width S (d₀+j.val):ℝ))*Real.sqrt (level S:ℝ)) ≤ 512*S*2 := calc
    _ ≤ ∑ j : Fin s.D, 512*(S:ℝ)*(1/2:ℝ)^j.val := by
      apply Finset.sum_le_sum; intro j _; apply (term_bound S _).trans
      exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)) (by positivity)
    _ ≤ _ := by rw [← Finset.mul_sum]; gcongr; exact geometric _
  linarith
