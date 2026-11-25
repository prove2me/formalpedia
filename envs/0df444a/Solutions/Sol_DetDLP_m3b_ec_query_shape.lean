-- Prove2me | solution 1 for DetDLP.m3b_ec_query_shape
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T21:21:53.893481+00:00
-- url     : https://prove2.me/submissions/ef2979cb-e699-4d4b-9b1d-35edc7fc4fe9

import Definitions.Def_DetDLP_W3_Separator
import Theorems.Thm_DetDLP_hasse_ec_point_count_bound

set_option autoImplicit false
set_option maxHeartbeats 400000
open DetDLP

private theorem block_sq (b : ℕ) (hb : 2 ≤ b) : blockCount b * blockCount b ≤ 8*b := by
  let c := Nat.clog 2 (b+2)
  have hc : c ≤ b+2 := Nat.clog_le_of_le_pow (Nat.le_of_lt (b+2).lt_two_pow_self)
  let r := (c:ℝ)^((1:ℝ)/4)
  have r0 : 0 ≤ r := Real.rpow_nonneg (by positivity) _
  have r4 : r^4 = c := by dsimp [r]; rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
  have r2 : r^2 ≤ (c:ℝ)+1 := by nlinarith [sq_nonneg (r^2-1)]
  have hr := Nat.ceil_lt_add_one r0
  by_cases h : 2 ≤ ⌈r⌉₊
  · change max 2 ⌈r⌉₊ * max 2 ⌈r⌉₊ ≤ _; rw [max_eq_right h]
    have hc' : (c:ℝ) ≤ (b:ℝ)+2 := by exact_mod_cast hc
    have hb' : (2:ℝ) ≤ b := by exact_mod_cast hb
    have hsq : (⌈r⌉₊:ℝ)^2 ≤ (r+1)^2 := by nlinarith [mul_nonneg (show 0 ≤ r+1-⌈r⌉₊ by linarith) (show 0 ≤ r+1+⌈r⌉₊ by positivity)]
    exact_mod_cast (show (⌈r⌉₊:ℝ)*(⌈r⌉₊:ℝ) ≤ 8*b by nlinarith [sq_nonneg (r-1)])
  · change max 2 ⌈r⌉₊ * max 2 ⌈r⌉₊ ≤ _; rw [max_eq_left (by omega)]; omega

private theorem dims {p g : ℕ} (p67 : 67 < p) (g64 : 64 ≤ g) (pg : p ≤ 2*(g-1)) (gp : g-1 ≤ 2*p) :
    let b := bitLen p; let m := blockCount b; let T := hashThreshold p (g-1) m g; let k := Nat.clog 2 (2*T)
    4*m*k ≤ 2000*b ∧ b ≤ 4*m*k ∧ 1 ≤ k := by
  let b := bitLen p
  let m := blockCount b
  let Q := qStar m g
  let T := hashThreshold p (g-1) m g
  let k := Nat.clog 2 (2*T)
  have mb : 2 ≤ m := le_max_left ..
  have pb : p ≤ 2^b := Nat.le_pow_clog (by decide) _
  have hb : 2 ≤ b := by by_contra! h; have := Nat.pow_le_pow_right (by decide : 0<2) (show b ≤ 1 by omega); omega
  have hq : 4096*m ≤ Q := le_max_left ..
  have hpR : (0:ℝ) < (g-1:ℕ) := by exact_mod_cast (show 0 < g-1 by omega)
  have ht : T ≤ 2*Q := by
    apply Nat.ceil_le.mpr; apply (div_le_iff₀ hpR).mpr
    push_cast; have h : (p:ℝ) ≤ 2*((g-1:ℕ):ℝ) := by exact_mod_cast pg
    nlinarith [mul_le_mul_of_nonneg_right h (show (0:ℝ) ≤ Q by positivity)]
  have qt : Q ≤ 2*T := by
    have h := Nat.le_ceil ((p:ℝ)*Q/((g-1:ℕ):ℝ)); change _ ≤ (T:ℝ) at h
    have h2 := (div_le_iff₀ hpR).mp h
    have hg : ((g-1:ℕ):ℝ) ≤ 2*(p:ℝ) := by exact_mod_cast gp
    have pR : (0:ℝ) < p := by exact_mod_cast (show 0<p by omega)
    have hr : (p:ℝ)*Q ≤ p*(2*(T:ℝ)) := by nlinarith [mul_le_mul_of_nonneg_left hg (show (0:ℝ) ≤ T by positivity)]
    exact_mod_cast (le_of_mul_le_mul_left hr pR)
  have hk : 2*T ≤ 2^k := Nat.le_pow_clog (by decide) _
  have kpos : 1 ≤ k := by
    by_contra! h
    have kz : k=0 := by omega
    rw [kz,pow_zero] at hk; omega
  have root (v : ℕ) : ⌈(16*(g:ℝ))^((1:ℝ)/m)⌉₊ ≤ v ↔ 16*g ≤ v^m := by
    rw [Nat.ceil_le,one_div,Real.rpow_inv_le_iff_of_pos (by positivity) (by positivity) (by exact_mod_cast (show 0 < m by omega)),Real.rpow_natCast]; norm_cast
  have powQ : 16*g ≤ Q^m := (root Q).mp (le_max_right ..)
  have blo : b ≤ k*m := Nat.clog_le_of_le_pow (by calc
    p ≤ 16*g := by omega
    _ ≤ Q^m := powQ
    _ ≤ (2^k)^m := Nat.pow_le_pow_left (qt.trans hk) _
    _ = 2^(k*m) := (pow_mul ..).symm)
  let n := 12 + m + ((b+6)/m+1)
  have qbound : Q ≤ 2^n := by
    apply max_le
    · have h : 4096*m ≤ 2^12*2^m := Nat.mul_le_mul_left 4096 (Nat.le_of_lt m.lt_two_pow_self)
      have hn : 12+m ≤ n := Nat.le_add_right _ _
      exact (h.trans_eq (pow_add 2 12 m).symm).trans (Nat.pow_le_pow_right (by decide) hn)
    · apply (root _).mpr
      have gg : 16*g ≤ 2^(b+6) := by rw [pow_add]; norm_num; omega
      have divr := Nat.mod_add_div (b+6) m
      have rem := Nat.mod_lt (b+6) (show 0 < m by omega)
      have nn : b+6 ≤ n*m := by dsimp [n]; nlinarith
      exact gg.trans ((Nat.pow_le_pow_right (by decide) nn).trans_eq (pow_mul ..))
  have kup : k ≤ 2+n := Nat.clog_le_of_le_pow (by rw [pow_add]; norm_num; omega)
  have hsq := block_sq b hb
  change m*m ≤ 8*b at hsq
  have hmb : m ≤ 8*b := by nlinarith
  have ddiv := Nat.div_mul_le_self (b+6) m
  have mk := Nat.mul_le_mul_left m kup
  change 4*m*k ≤ 2000*b ∧ b ≤ 4*m*k ∧ 1 ≤ k
  dsimp only [n] at mk; exact ⟨by nlinarith,by nlinarith,kpos⟩

theorem solution (q : w3_Query) (hq : w3_ecQueries q) : 4*q.m*q.k ≤ 2000*q.b ∧ q.b ≤ 4*q.m*q.k ∧ 1 ≤ q.k := by
  obtain ⟨p,ip,E,hE,_,_,_,p67,g64,hNZ,hM,S,F,hF,P,y,pre,rfl⟩ := hq
  letI := ecPointFintype E
  let g := Fintype.card E.toAffine.Point
  have hasse := hasse_ec_point_count_bound p (by omega) E
  change |(g:ℝ)-((p:ℝ)+1)| ≤ 2*Real.sqrt p at hasse
  have h := abs_le.mp hasse
  have hp : (67:ℝ) < p := by exact_mod_cast p67
  have sq := Real.sq_sqrt (show (0:ℝ) ≤ p by positivity)
  have r : 4*Real.sqrt p ≤ p := by nlinarith [sq_nonneg (Real.sqrt (p:ℝ)-4), Real.sqrt_nonneg (p:ℝ)]
  have hg : ((g-1:ℕ):ℝ) = (g:ℝ)-1 := by rw [Nat.cast_sub (by change 1 ≤ Fintype.card E.toAffine.Point; omega),Nat.cast_one]
  apply dims p67 g64
  · exact_mod_cast (show (p:ℝ) ≤ 2*((g-1:ℕ):ℝ) by rw [hg]; linarith [h.1])
  · exact_mod_cast (show ((g-1:ℕ):ℝ) ≤ 2*(p:ℝ) by rw [hg]; linarith [h.2])
