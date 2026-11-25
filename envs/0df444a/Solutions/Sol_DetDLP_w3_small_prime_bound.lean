-- Prove2me | solution 1 for DetDLP.w3_small_prime_bound
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T00:33:21.688797+00:00
-- url     : https://prove2.me/submissions/8c1faf2b-242f-4428-b4f3-56c70c773a9d

import Definitions.Def_DetDLP_W3_Driver
import Theorems.Thm_DetDLP_hasse_ec_point_count_bound

set_option autoImplicit false
open DetDLP

private theorem DetDLP.w3_block_linear (b : ℕ) : blockCount b ≤ b+2 := by
  have hlog : 1 ≤ Nat.clog 2 (b+2) := Nat.clog_pos (by decide) (by omega)
  have hle : Nat.clog 2 (b+2) ≤ b+2 := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self (n := b+2)).le
  apply max_le (by omega)
  apply Nat.ceil_le.mpr
  have h1 : (1 : ℝ) ≤ (Nat.clog 2 (b+2) : ℝ) := by exact_mod_cast hlog
  simpa only [Nat.cast_add,Nat.cast_ofNat] using (Real.rpow_le_self_of_one_le h1 (by norm_num : (1:ℝ)/4 ≤ 1)).trans (Nat.cast_le.mpr hle)

private theorem DetDLP.w3_linear_exp {b : ℕ} (h : 32 ≤ b) : 16384*(b+2)+512 ≤ 2^(b-1) := by
  induction b, h using Nat.le_induction with
  | base => decide
  | succ b hb ih =>
    have hpred : b = (b-1)+1 := by omega
    simp only [Nat.succ_sub_succ_eq_sub,Nat.sub_zero]
    calc 16384 * (b+1+2) + 512 ≤ 2 * (16384*(b+2)+512) := by omega
         _ ≤ 2 * 2^(b-1) := Nat.mul_le_mul_left 2 ih
         _ = 2^b := by conv_rhs => rw [hpred,pow_succ]; rw [Nat.mul_comm]

private theorem DetDLP.w3_bound_from_quarter {p M : ℕ} (hp : 1 < p) (hM : p ≤ 4*M+256)
    (hs : ¬w3_large p M) : p ≤ 2^32 := by
  let b := bitLen p
  by_contra! hx
  have hb : 32 < b := (Nat.lt_clog_iff_pow_lt (by decide)).mpr hx
  have hpow := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) hp
  change 2^(b-1) < p at hpow
  have he := w3_linear_exp hb.le
  have hm := w3_block_linear b
  apply hs
  change 67 < p ∧ 64 ≤ M ∧ 4096*blockCount b ≤ M-1
  omega

theorem solution :
    (∀ (p : ℕ) [Fact p.Prime], ¬w3_large p (p-1) → p ≤ 2^32) ∧
    (∀ (p : ℕ) [Fact p.Prime], 3 < p → ∀ (E : WeierstrassCurve (ZMod p)) [E.IsElliptic],
      letI := ecPointFintype E; ¬w3_large p (Fintype.card E.toAffine.Point) → p ≤ 2^32) := by
  constructor
  · intro p hp h; exact w3_bound_from_quarter hp.out.one_lt (by omega) h
  · intro p hp hp3 E hE
    letI := ecPointFintype E
    let M := Fintype.card E.toAffine.Point
    change ¬w3_large p M → _
    intro hs
    apply w3_bound_from_quarter hp.out.one_lt (M := M) _ hs
    have h := (abs_le.mp (hasse_ec_point_count_bound p hp3 E)).1
    change -(2*Real.sqrt (p:ℝ)) ≤ (M:ℝ)-((p:ℝ)+1) at h
    have h2 := Real.sq_sqrt (Nat.cast_nonneg p)
    have h4 : (p:ℝ) ≤ 4*(M:ℝ)+256 := by nlinarith [sq_nonneg (Real.sqrt (p:ℝ)-4)]
    exact_mod_cast h4
