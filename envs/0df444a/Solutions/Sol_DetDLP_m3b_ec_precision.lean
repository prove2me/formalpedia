-- Prove2me | solution 1 for DetDLP.m3b_ec_precision
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T21:24:21.636442+00:00
-- url     : https://prove2.me/submissions/ca1778ae-9a57-44da-a23f-94894e7bea4f

import Definitions.Def_DetDLP_W3_Separator
import Theorems.Thm_DetDLP_hasse_ec_point_count_bound

set_option autoImplicit false
set_option maxHeartbeats 400000
open DetDLP

private theorem precision_bound {b m k g p : ℕ} (hb : 2 ≤ b) (hm : 2 ≤ m) (hport : 4*m*k ≤ 2000*b)
    (mb : m ≤ b+2) (pb : p ≤ 2^b) (gg : g ≤ 2*p+1) :
    2+4*m*k+dFilt (2*m)*Nat.clog 2 (2*(2*m)*g+2) ≤ 100000000*m*b := by
  have h1 : m ≤ 2^(b+1) := by rw [pow_succ]; have := b.lt_two_pow_self; omega
  have h2 : g ≤ 2^(b+2) := by rw [pow_add]; norm_num; omega
  have h3 := Nat.mul_le_mul h1 h2
  rw [← pow_add] at h3
  have hc : Nat.clog 2 (2*(2*m)*g+2) ≤ (b+1+(b+2))+3 := Nat.clog_le_of_le_pow (by rw [pow_add]; norm_num; nlinarith [Nat.two_pow_pos (b+1+(b+2))])
  have hmc := Nat.mul_le_mul_left (dFilt (2*m)) hc
  unfold dFilt at *; nlinarith [Nat.mul_le_mul_left m hb,Nat.mul_le_mul_right b hm]

theorem solution (q : w3_Query) (hq : w3_ecQueries q) (hport : 4*q.m*q.k ≤ 2000*q.b) :
    w3_precision q ≤ 100000000*q.m*q.b := by
  obtain ⟨p,ip,E,hE,_,_,_,p67,g64,hNZ,hM,S,F,hF,P,y,pre,rfl⟩ := hq
  letI := ecPointFintype E
  let g := Fintype.card E.toAffine.Point
  let b := bitLen p
  let m := blockCount b
  have pb : p ≤ 2^b := Nat.le_pow_clog (by decide) p
  have hb : 2 ≤ b := by by_contra! h; have := Nat.pow_le_pow_right (by decide : 0<2) (show b ≤ 1 by omega); omega
  have mc : Nat.clog 2 (b+2) ≤ b+2 := Nat.clog_le_of_le_pow (Nat.le_of_lt (b+2).lt_two_pow_self)
  have mb : m ≤ b+2 := by
    apply max_le (by omega); apply Nat.ceil_le.mpr
    rw [one_div,Real.rpow_inv_le_iff_of_pos (by positivity) (by positivity) (by norm_num)]
    norm_cast; exact mc.trans (Nat.le_self_pow (by decide : 4 ≠ 0) _)
  have hg := hasse_ec_point_count_bound p (by omega) E
  change |(g:ℝ)-((p:ℝ)+1)| ≤ 2*Real.sqrt p at hg
  have sq := Real.sq_sqrt (show (0:ℝ) ≤ p by positivity)
  have r : 2*Real.sqrt p ≤ p := by
    have hp : (67:ℝ)<p := by exact_mod_cast p67
    nlinarith [sq_nonneg (Real.sqrt (p:ℝ)-2)]
  have gg : g ≤ 2*p+1 := by exact_mod_cast (show (g:ℝ) ≤ 2*p+1 by linarith [(abs_le.mp hg).2])
  exact precision_bound hb (le_max_left ..) hport mb pb gg
