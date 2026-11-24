-- Prove2me | solution 1 for BB6Kit.params_synth
-- status  : ACCEPTED   (prove)
-- author  : @alon yuval
-- created : 2026-11-23T23:14:01.234792+00:00
-- url     : https://prove2.me/submissions/7b0da14c-b9a9-4759-b77c-fda75a7a44bf

import Mathlib
import Definitions.Def_BB6Kit

namespace BB6KitSy

theorem bK_le (K R S x y z w : ℕ) (hR : 2 ≤ R) (hS : 2 ≤ S) (hy : 0 < y) (hw : 0 < w) :
    0 < BB6Kit.bK K R S R x y z w ∧
    BB6Kit.bK K R S R x y z w ≤ (((y : ℝ) + x) * ((R : ℝ) - 1) / 2) *
      (((w : ℝ) * ((S : ℝ) - 1) + (z : ℝ) * ((R : ℝ) - 1)) / 2) := by
  unfold BB6Kit.bK
  have hy' : (y : ℝ) ≠ 0 := by exact_mod_cast hy.ne'
  have hw' : (w : ℝ) ≠ 0 := by exact_mod_cast hw.ne'
  have e1 : (y : ℝ) * (((R : ℝ) - 1) / 2 + (x : ℝ) / y * (((R : ℝ) - 1) / 2)) =
      ((y : ℝ) + x) * ((R : ℝ) - 1) / 2 := by
    field_simp
  have e2 : (w : ℝ) * (((S : ℝ) - 1) / 2 + (z : ℝ) / w * (((R : ℝ) - 1) / 2)) =
      ((w : ℝ) * ((S : ℝ) - 1) + (z : ℝ) * ((R : ℝ) - 1)) / 2 := by
    field_simp
  rw [e1, e2]
  have hP : (1 : ℝ) ≤ ∏ k ∈ Finset.Ico 1 K, ((k.factorial : ℝ) ^ (K - k)) := by
    calc (1 : ℝ) = ∏ k ∈ Finset.Ico 1 K, (1 : ℝ) := by simp
      _ ≤ _ := by
        apply Finset.prod_le_prod
        · intro i _; norm_num
        · intro i _
          apply one_le_pow₀
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero i)
  have hden : (0 : ℝ) ≤ (K : ℝ) * ((K : ℝ) - 1) * ((K : ℝ) + 1) := by
    rcases Nat.eq_zero_or_pos K with h | h
    · subst h; simp
    · have : (1 : ℝ) ≤ K := by exact_mod_cast h
      have : (0:ℝ) ≤ (K : ℝ) - 1 := by linarith
      positivity
  have hexp : -(12 : ℝ) / ((K : ℝ) * ((K : ℝ) - 1) * ((K : ℝ) + 1)) ≤ 0 := by
    rw [neg_div]; exact neg_nonpos.mpr (div_nonneg (by norm_num) hden)
  have hF1 := Real.rpow_le_one_of_one_le_of_nonpos hP hexp
  have hF0 : 0 < (∏ k ∈ Finset.Ico 1 K, ((k.factorial : ℝ) ^ (K - k))) ^
      (-(12 : ℝ) / ((K : ℝ) * ((K : ℝ) - 1) * ((K : ℝ) + 1))) := Real.rpow_pos_of_pos (by linarith) _
  have hR' : (2:ℝ) ≤ R := by exact_mod_cast hR
  have hS' : (2:ℝ) ≤ S := by exact_mod_cast hS
  have hy1 : (1:ℝ) ≤ y := by exact_mod_cast hy
  have hw1 : (1:ℝ) ≤ w := by exact_mod_cast hw
  have hA : 0 < ((y : ℝ) + x) * ((R : ℝ) - 1) / 2 := by
    have : (0:ℝ) ≤ x := by positivity
    apply div_pos (mul_pos (by linarith) (by linarith)) (by norm_num)
  have hB : 0 < ((w : ℝ) * ((S : ℝ) - 1) + (z : ℝ) * ((R : ℝ) - 1)) / 2 := by
    have : (0:ℝ) ≤ (z : ℝ) * ((R : ℝ) - 1) := mul_nonneg (by positivity) (by linarith)
    have : (0:ℝ) < (w : ℝ) * ((S : ℝ) - 1) := mul_pos (by linarith) (by linarith)
    linarith
  refine ⟨mul_pos (mul_pos hA hB) hF0, ?_⟩
  calc _ ≤ (((y : ℝ) + x) * ((R : ℝ) - 1) / 2) * (((w : ℝ) * ((S : ℝ) - 1) + (z : ℝ) * ((R : ℝ) - 1)) / 2) * 1 :=
        mul_le_mul_of_nonneg_left hF1 (mul_pos hA hB).le
    _ = _ := by ring

theorem log_le_lin (x : ℝ) (hx : 0 < x) : Real.log x ≤ x / 32 + 5 / 2 := by
  have h1 : Real.log x = Real.log (x / 32) + Real.log 32 := by
    rw [← Real.log_mul (by positivity) (by norm_num)]; congr 1; ring
  have h2 := Real.log_le_sub_one_of_pos (by positivity : (0:ℝ) < x / 32)
  have h3 : Real.log (32 : ℝ) = 5 * Real.log 2 := by
    rw [show (32:ℝ) = 2 ^ 5 by norm_num, Real.log_pow]; norm_num
  have := Real.log_two_lt_d9
  linarith

theorem big21 (n : ℕ) (hn : 60 ≤ n) : 2 ^ 21 * n ^ 2 < 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    have h : (m + 1) ^ 2 ≤ 2 * m ^ 2 := by nlinarith
    calc 2 ^ 21 * (m + 1) ^ 2 ≤ 2 * (2 ^ 21 * m ^ 2) := by nlinarith
      _ < 2 * 2 ^ m := by omega
      _ = 2 ^ (m + 1) := by ring

end BB6KitSy

set_option maxHeartbeats 2000000 in
theorem solution (n i k c : ℕ) (hn : 60 ≤ n) (hi : 2 ^ n ≤ i) (hi' : i < 2 ^ (n + 1))
    (hc : 0 < c) (hc4 : c ≤ 4 * i) (hk2 : 2 ≤ k) (hk : k ≤ 2 * i + 2) :
    5 * (BB6Kit.GK (BB6Kit.fN n) (BB6Kit.fL n) (BB6Kit.fR n) (BB6Kit.fS n) (BB6Kit.fR n) (BB6Kit.fR n) * Real.log ((2 : ℕ) : ℝ) + BB6Kit.GK (BB6Kit.fN n) (BB6Kit.fL n) (BB6Kit.fR n) (BB6Kit.fS n) (BB6Kit.fR n) (BB6Kit.fS n) * Real.log ((c) : ℝ) + BB6Kit.GK (BB6Kit.fN n) (BB6Kit.fL n) (BB6Kit.fR n) (BB6Kit.fS n) (BB6Kit.fR n) (BB6Kit.fR n) * Real.log ((3 : ℕ) : ℝ)) + Real.log ((BB6Kit.fN n).factorial : ℝ) + ((BB6Kit.fN n) : ℝ) * Real.log 2 + ((BB6Kit.fN n) : ℝ) * (((BB6Kit.fK n) : ℝ) - 1) / 3 * Real.log (BB6Kit.bK (BB6Kit.fK n) (BB6Kit.fR n) (BB6Kit.fS n) (BB6Kit.fR n) ((k - 1 : ℕ) / Nat.gcd (k - 1 : ℕ) (i)) ((i) / Nat.gcd (k - 1 : ℕ) (i)) ((1 : ℕ) / Nat.gcd (1 : ℕ) (i)) ((i) / Nat.gcd (1 : ℕ) (i))) + 0.001 <
      ((BB6Kit.fN n) : ℝ) ^ 2 / (2 * ((BB6Kit.fK n) : ℝ)) * (1 - 2 / (3 * ((BB6Kit.fL n) : ℝ)) - 2 / (3 * ((BB6Kit.fK n) : ℝ) * (BB6Kit.fL n)) - 1 / (3 * ((BB6Kit.fL n) : ℝ) ^ 2) -
        16 / (3 * ((BB6Kit.fK n) : ℝ) ^ 2 * (BB6Kit.fL n))) * Real.log 4 := by
  simp only [Nat.cast_ofNat]
  -- natural-number shapes
  have hK : BB6Kit.fK n = 2 ^ 23 * n ^ 2 := rfl
  have hL : BB6Kit.fL n = 8 * n := rfl
  have hR1 : BB6Kit.fR1 n = 2 ^ 20 * n ^ 2 := by
    show 2 ^ 23 * n ^ 2 / 8 = _
    rw [show 2 ^ 23 * n ^ 2 = 2 ^ 20 * n ^ 2 * 8 by ring]; exact Nat.mul_div_cancel _ (by norm_num)
  have hR2 : BB6Kit.fR2 n = 2 ^ 17 * n ^ 2 := by
    show 2 ^ 23 * n ^ 2 / 64 = _
    rw [show 2 ^ 23 * n ^ 2 = 2 ^ 17 * n ^ 2 * 64 by ring]; exact Nat.mul_div_cancel _ (by norm_num)
  have hR3 : BB6Kit.fR3 n = 2 ^ 18 * n ^ 2 := by
    show 2 ^ 23 * n ^ 2 / 32 = _
    rw [show 2 ^ 23 * n ^ 2 = 2 ^ 18 * n ^ 2 * 32 by ring]; exact Nat.mul_div_cancel _ (by norm_num)
  have hR : BB6Kit.fR n = 1441792 * n ^ 2 + 1 := by
    show BB6Kit.fR1 n + BB6Kit.fR2 n + BB6Kit.fR3 n + 1 = _
    rw [hR1, hR2, hR3]; ring
  have hS : BB6Kit.fS n = 65536 * n + 81 := by
    show BB6Kit.fS1 n + BB6Kit.fS2 n + BB6Kit.fS3 n + 1 = _
    show 80 + 2 ^ 15 * n + 2 ^ 15 * n + 1 = _
    ring
  have hN : BB6Kit.fN n = 4 * n * (2 ^ 23 * n ^ 2) * (2 ^ 23 * n ^ 2 + 1) := by
    show BB6Kit.fK n * (BB6Kit.fK n + 1) * BB6Kit.fL n / 2 = _
    rw [hK, hL, show 2 ^ 23 * n ^ 2 * (2 ^ 23 * n ^ 2 + 1) * (8 * n) =
      4 * n * (2 ^ 23 * n ^ 2) * (2 ^ 23 * n ^ 2 + 1) * 2 by ring]
    exact Nat.mul_div_cancel _ (by norm_num)
  have hi0 : 0 < i := lt_of_lt_of_le (by positivity) hi
  -- b bound (natural-number arguments)
  have hd : 0 < Nat.gcd (k - 1) i := Nat.gcd_pos_of_pos_right _ hi0
  have hy : 0 < i / Nat.gcd (k - 1) i := Nat.div_pos (Nat.le_of_dvd hi0 (Nat.gcd_dvd_right _ _)) hd
  have hRge : 2 ≤ BB6Kit.fR n := by
    rw [hR]; have : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  have hSge : 2 ≤ BB6Kit.fS n := by rw [hS]; omega
  have hg1 : Nat.gcd 1 i = 1 := Nat.gcd_one_left i
  obtain ⟨hb0, hb⟩ := BB6KitSy.bK_le (BB6Kit.fK n) (BB6Kit.fR n) (BB6Kit.fS n) ((k - 1) / Nat.gcd (k - 1) i)
    (i / Nat.gcd (k - 1) i) (1 / Nat.gcd 1 i) (i / Nat.gcd 1 i) hRge hSge hy (by rw [hg1]; simpa using hi0)
  rw [hg1, Nat.div_one, Nat.div_one] at hb
  have hxle : (((k - 1) / Nat.gcd (k - 1) i : ℕ) : ℝ) ≤ 2 * (i : ℝ) + 1 := by
    have : (k - 1) / Nat.gcd (k - 1) i ≤ 2 * i + 1 := le_trans (Nat.div_le_self _ _) (by omega)
    exact_mod_cast this
  have hyle : ((i / Nat.gcd (k - 1) i : ℕ) : ℝ) ≤ (i : ℝ) := by exact_mod_cast Nat.div_le_self _ _
  -- real variables
  have hx : (60:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0:ℝ) < (n : ℝ) := by linarith only [hx]
  have hxsq : (3600:ℝ) ≤ (n:ℝ) ^ 2 := by nlinarith only [hx]
  have hx2 : 60 * (n:ℝ) ≤ (n:ℝ) ^ 2 := by
    rw [sq]; exact mul_le_mul_of_nonneg_right hx (by linarith only [hx])
  have hx3 : 60 * (n:ℝ) ^ 2 ≤ (n:ℝ) ^ 3 := by
    have := mul_le_mul_of_nonneg_right hx (sq_nonneg (n:ℝ))
    calc 60 * (n:ℝ) ^ 2 ≤ (n:ℝ) * (n:ℝ) ^ 2 := this
      _ = (n:ℝ) ^ 3 := by ring
  have h5 : (1:ℝ) ≤ (n:ℝ) ^ 5 := one_le_pow₀ (by linarith only [hx])
  have hx53 : 3600 * (n:ℝ) ^ 3 ≤ (n:ℝ) ^ 5 := by
    have := mul_le_mul_of_nonneg_left hxsq (pow_pos hn0 3).le
    calc 3600 * (n:ℝ) ^ 3 = (n:ℝ) ^ 3 * 3600 := by ring
      _ ≤ (n:ℝ) ^ 3 * (n:ℝ) ^ 2 := this
      _ = (n:ℝ) ^ 5 := by ring
  have hKr : (BB6Kit.fK n : ℝ) = 2 ^ 23 * (n : ℝ) ^ 2 := by rw [hK]; push_cast; ring
  have hLr : (BB6Kit.fL n : ℝ) = 8 * (n : ℝ) := by rw [hL]; push_cast; ring
  have hRr : (BB6Kit.fR n : ℝ) = 1441792 * (n : ℝ) ^ 2 + 1 := by rw [hR]; push_cast; ring
  have hSr : (BB6Kit.fS n : ℝ) = 65536 * (n : ℝ) + 81 := by rw [hS]; push_cast; ring
  have hNr : (BB6Kit.fN n : ℝ) = 4 * (n : ℝ) * (2 ^ 23 * (n : ℝ) ^ 2) * (2 ^ 23 * (n : ℝ) ^ 2 + 1) := by
    rw [hN]; push_cast; ring
  have hiR : (i : ℝ) < 2 ^ (n + 1) := by exact_mod_cast hi'
  have hiR0 : (0:ℝ) < i := by exact_mod_cast hi0
  have l2lo := Real.log_two_gt_d9
  have l2hi := Real.log_two_lt_d9
  have l3 : Real.log 3 ≤ 1.14 := by
    have h1 : Real.log 3 = Real.log 4 + Real.log (3 / 4) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
    have h2 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have h3 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 3 / 4)
    linarith
  have l30 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hlogx := BB6KitSy.log_le_lin (n : ℝ) (by linarith)
  have hlogi : Real.log (i : ℝ) ≤ ((n : ℝ) + 1) * Real.log 2 := by
    have := Real.log_le_log hiR0 hiR.le
    rw [Real.log_pow] at this; push_cast at this; linarith
  have hc1 : (1:ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
  have hlogc0 : 0 ≤ Real.log (c : ℝ) := Real.log_nonneg hc1
  have hlogc : Real.log (c : ℝ) ≤ ((n : ℝ) + 3) * Real.log 2 := by
    have h1 : (c : ℝ) ≤ (2:ℝ) ^ (n + 3) := by
      have : c ≤ 2 ^ (n + 3) := by
        have : 2 ^ (n + 3) = 4 * 2 ^ (n + 1) := by ring
        omega
      exact_mod_cast this
    have h2 := Real.log_le_log (by linarith) h1
    rw [Real.log_pow] at h2; push_cast at h2; exact h2
  -- log b bound
  have hlogb : Real.log (BB6Kit.bK (BB6Kit.fK n) (BB6Kit.fR n) (BB6Kit.fS n) (BB6Kit.fR n)
      ((k - 1) / Nat.gcd (k - 1) i) (i / Nat.gcd (k - 1) i) (1 / Nat.gcd 1 i) (i / Nat.gcd 1 i)) ≤
      Real.log 2 + 2 * (((n : ℝ) + 1) * Real.log 2) + (21 * Real.log 2 + 2 * Real.log n) +
        (17 * Real.log 2 + Real.log n) := by
    rw [hg1, Nat.div_one, Nat.div_one]
    rw [hg1, Nat.div_one, Nat.div_one] at hb0
    have hRn : (BB6Kit.fR n : ℝ) ≤ 2 ^ 21 * (n : ℝ) ^ 2 := by rw [hRr]; linarith only [hxsq]
    have hSn : (BB6Kit.fS n : ℝ) ≤ 2 ^ 17 * (n : ℝ) := by rw [hSr]; linarith only [hx]
    have hR1r : (1:ℝ) ≤ (BB6Kit.fR n : ℝ) := by rw [hRr]; linarith only [hxsq]
    have hS1r : (1:ℝ) ≤ (BB6Kit.fS n : ℝ) := by rw [hSr]; linarith only [hx]
    have hRiS : (BB6Kit.fR n : ℝ) ≤ (i : ℝ) * (BB6Kit.fS n : ℝ) := by
      have h1 : BB6Kit.fR n ≤ i := by
        have h21 := BB6KitSy.big21 n hn
        rw [hR]
        have hi2 := hi
        generalize n ^ 2 = m at h21 ⊢
        generalize 2 ^ n = P at h21 hi2
        omega
      have h1r : (BB6Kit.fR n : ℝ) ≤ (i : ℝ) := by exact_mod_cast h1
      have hi1 : (0:ℝ) ≤ (i : ℝ) := hiR0.le
      have := mul_le_mul_of_nonneg_left hS1r hi1
      linarith only [h1r, this]
    have hbub : BB6Kit.bK (BB6Kit.fK n) (BB6Kit.fR n) (BB6Kit.fS n) (BB6Kit.fR n)
        ((k - 1) / Nat.gcd (k - 1) i) (i / Nat.gcd (k - 1) i) 1 i ≤
        2 * (i : ℝ) ^ 2 * (BB6Kit.fR n : ℝ) * (BB6Kit.fS n : ℝ) := by
      refine le_trans hb ?_
      have hA : (((i / Nat.gcd (k - 1) i : ℕ) : ℝ) + (((k - 1) / Nat.gcd (k - 1) i : ℕ) : ℝ)) *
          ((BB6Kit.fR n : ℝ) - 1) / 2 ≤ 2 * (i : ℝ) * (BB6Kit.fR n : ℝ) := by
        have : (((i / Nat.gcd (k - 1) i : ℕ) : ℝ) + (((k - 1) / Nat.gcd (k - 1) i : ℕ) : ℝ)) ≤ 3 * (i : ℝ) + 1 := by
          linarith
        have hR1' : (0:ℝ) ≤ (BB6Kit.fR n : ℝ) - 1 := by linarith only [hR1r]
        have hm := mul_le_mul_of_nonneg_right this hR1'
        have hi1 : (1:ℝ) ≤ (i : ℝ) := by exact_mod_cast hi0
        have hiR' := mul_le_mul_of_nonneg_right hi1 (by linarith only [hR1r] : (0:ℝ) ≤ (BB6Kit.fR n : ℝ))
        nlinarith only [hm, hi1, hR1r, hiR']
      have hB : ((i : ℝ) * ((BB6Kit.fS n : ℝ) - 1) + ((1 : ℕ) : ℝ) * ((BB6Kit.fR n : ℝ) - 1)) / 2 ≤
          (i : ℝ) * (BB6Kit.fS n : ℝ) := by
        push_cast; nlinarith only [hRiS, hiR0]
      have hA0 : (0:ℝ) ≤ (((i / Nat.gcd (k - 1) i : ℕ) : ℝ) + (((k - 1) / Nat.gcd (k - 1) i : ℕ) : ℝ)) *
          ((BB6Kit.fR n : ℝ) - 1) / 2 := by
        have : (0:ℝ) ≤ (((i / Nat.gcd (k - 1) i : ℕ) : ℝ) + (((k - 1) / Nat.gcd (k - 1) i : ℕ) : ℝ)) := by positivity
        apply div_nonneg (mul_nonneg this (by linarith)) (by norm_num)
      calc _ ≤ (2 * (i : ℝ) * (BB6Kit.fR n : ℝ)) * ((i : ℝ) * (BB6Kit.fS n : ℝ)) :=
            mul_le_mul hA hB (by
              have := mul_nonneg hiR0.le (by linarith only [hS1r] : (0:ℝ) ≤ (BB6Kit.fS n : ℝ) - 1)
              push_cast; linarith only [this, hR1r]) (by positivity)
        _ = _ := by ring
    have hpos2 : (0:ℝ) < 2 * (i : ℝ) ^ 2 * (BB6Kit.fR n : ℝ) * (BB6Kit.fS n : ℝ) := by positivity
    calc _ ≤ Real.log (2 * (i : ℝ) ^ 2 * (BB6Kit.fR n : ℝ) * (BB6Kit.fS n : ℝ)) := Real.log_le_log hb0 hbub
      _ = Real.log 2 + 2 * Real.log (i : ℝ) + Real.log (BB6Kit.fR n : ℝ) + Real.log (BB6Kit.fS n : ℝ) := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
            Real.log_mul (by positivity) (by positivity), Real.log_pow]; push_cast; ring
      _ ≤ _ := by
          have h1 : Real.log (BB6Kit.fR n : ℝ) ≤ 21 * Real.log 2 + 2 * Real.log n := by
            have := Real.log_le_log (by linarith) hRn
            rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at this
            push_cast at this; linarith
          have h2 : Real.log (BB6Kit.fS n : ℝ) ≤ 17 * Real.log 2 + Real.log n := by
            have := Real.log_le_log (by linarith) hSn
            rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at this
            push_cast at this; linarith
          linarith
  -- G bounds
  set Nr : ℝ := (BB6Kit.fN n : ℝ) with hNrdef
  have hNpos : 0 < Nr := by rw [hNr]; positivity
  have hgK : BB6Kit.gK (BB6Kit.fN n) (BB6Kit.fR n) (BB6Kit.fS n) (BB6Kit.fR n) ≤ 1 / 4 := by
    unfold BB6Kit.gK
    have : (0:ℝ) ≤ (BB6Kit.fN n : ℝ) / (12 * (BB6Kit.fR n : ℝ) * (BB6Kit.fS n : ℝ) * (BB6Kit.fR n : ℝ)) := by positivity
    linarith
  have hG : ∀ X : ℕ, BB6Kit.GK (BB6Kit.fN n) (BB6Kit.fL n) (BB6Kit.fR n) (BB6Kit.fS n) (BB6Kit.fR n) X ≤
      Nr * (BB6Kit.fL n : ℝ) * (X : ℝ) / 8 := by
    intro X
    unfold BB6Kit.GK
    have h0 : (0:ℝ) ≤ Nr * (BB6Kit.fL n : ℝ) * (X : ℝ) := by positivity
    have := mul_le_mul_of_nonneg_left hgK h0
    rw [← hNrdef]
    linarith
  have hl20 : 0 ≤ Real.log 2 := by linarith
  have hT1 := mul_le_mul_of_nonneg_right (hG (BB6Kit.fR n)) hl20
  have hT2a := mul_le_mul_of_nonneg_right (hG (BB6Kit.fS n)) hlogc0
  have hT2b := mul_le_mul_of_nonneg_left hlogc (by positivity : (0:ℝ) ≤ Nr * (BB6Kit.fL n : ℝ) * (BB6Kit.fS n : ℝ) / 8)
  have hT3a := mul_le_mul_of_nonneg_right (hG (BB6Kit.fR n)) l30
  have hT3b := mul_le_mul_of_nonneg_left l3 (by positivity : (0:ℝ) ≤ Nr * (BB6Kit.fL n : ℝ) * (BB6Kit.fR n : ℝ) / 8)
  -- factorial
  have hfact : Real.log ((BB6Kit.fN n).factorial : ℝ) ≤ Nr * Real.log Nr := by
    have h1 : ((BB6Kit.fN n).factorial : ℝ) ≤ ((BB6Kit.fN n : ℝ)) ^ (BB6Kit.fN n) := by
      exact_mod_cast Nat.factorial_le_pow (BB6Kit.fN n)
    have h0 : (0:ℝ) < ((BB6Kit.fN n).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have := Real.log_le_log h0 h1
    rw [Real.log_pow] at this
    exact this
  have hlogN : Real.log Nr ≤ 49 * Real.log 2 + 5 * Real.log (n : ℝ) := by
    have hn0 : (0:ℝ) < n := by linarith
    have hNle : Nr ≤ 2 ^ 49 * (n : ℝ) ^ 5 := by
      rw [hNr]; nlinarith only [hx53, pow_pos hn0 3]
    have := Real.log_le_log hNpos hNle
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at this
    push_cast at this
    linarith
  -- C bound
  have hC : (599:ℝ) / 600 ≤ 1 - 2 / (3 * (BB6Kit.fL n : ℝ)) - 2 / (3 * (BB6Kit.fK n : ℝ) * (BB6Kit.fL n : ℝ)) -
      1 / (3 * (BB6Kit.fL n : ℝ) ^ 2) - 16 / (3 * (BB6Kit.fK n : ℝ) ^ 2 * (BB6Kit.fL n : ℝ)) := by
    rw [hLr, hKr]
    have a1 : 2 / (3 * (8 * (n:ℝ))) ≤ 1 / 720 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith only [hx]
    have a2 : 2 / (3 * (2 ^ 23 * (n:ℝ) ^ 2) * (8 * (n:ℝ))) ≤ 1 / 100000 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith only [hx3, hxsq]
    have a3 : 1 / (3 * (8 * (n:ℝ)) ^ 2) ≤ 1 / 100000 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith only [hxsq]
    have a4 : 16 / (3 * (2 ^ 23 * (n:ℝ) ^ 2) ^ 2 * (8 * (n:ℝ))) ≤ 1 / 100000 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith only [h5]
    linarith
  -- RHS lower bound
  have hNK : Nr ^ 2 / (2 * (BB6Kit.fK n : ℝ)) = Nr * (2 * (n : ℝ) * ((BB6Kit.fK n : ℝ) + 1)) := by
    have hK0 : (BB6Kit.fK n : ℝ) ≠ 0 := by rw [hKr]; positivity
    rw [hNr, hKr] at *
    field_simp
    ring
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hRHS : Nr * (2 * (n : ℝ) * ((BB6Kit.fK n : ℝ) + 1) * ((599:ℝ) / 600) * (2 * 0.6931471803)) ≤
      Nr ^ 2 / (2 * (BB6Kit.fK n : ℝ)) * (1 - 2 / (3 * (BB6Kit.fL n : ℝ)) - 2 / (3 * (BB6Kit.fK n : ℝ) * (BB6Kit.fL n : ℝ)) -
        1 / (3 * (BB6Kit.fL n : ℝ) ^ 2) - 16 / (3 * (BB6Kit.fK n : ℝ) ^ 2 * (BB6Kit.fL n : ℝ))) * Real.log 4 := by
    rw [hNK, hlog4]
    have hP : (0:ℝ) ≤ Nr * (2 * (n : ℝ) * ((BB6Kit.fK n : ℝ) + 1)) := by positivity
    have h1 := mul_le_mul_of_nonneg_left hC hP
    have h2 : (0:ℝ) ≤ Nr * (2 * (n : ℝ) * ((BB6Kit.fK n : ℝ) + 1)) * ((599:ℝ) / 600) := by positivity
    have h3 := mul_le_mul_of_nonneg_left (by linarith : 2 * 0.6931471803 ≤ 2 * Real.log 2) h2
    have h4 : (0:ℝ) ≤ 2 * Real.log 2 := by linarith
    have h6 := mul_le_mul_of_nonneg_right h1 h4
    linarith only [h3, h6]
  -- b-term upper bound
  have hKm1 : (0:ℝ) ≤ Nr * ((BB6Kit.fK n : ℝ) - 1) / 3 := by
    have : (1:ℝ) ≤ (BB6Kit.fK n : ℝ) := by rw [hKr]; linarith only [hxsq]
    have : (0:ℝ) ≤ (BB6Kit.fK n : ℝ) - 1 := by linarith
    positivity
  have hB := mul_le_mul_of_nonneg_left hlogb hKm1
  -- polynomial comparison
  have hpoly : 5 * ((8 * (n:ℝ)) * (1441792 * (n:ℝ) ^ 2 + 1) / 8 * 0.6931471808 +
        (8 * (n:ℝ)) * (65536 * (n:ℝ) + 81) / 8 * (((n:ℝ) + 3) * 0.6931471808) +
        (8 * (n:ℝ)) * (1441792 * (n:ℝ) ^ 2 + 1) / 8 * 1.14) +
      (49 * 0.6931471808 + 5 * ((n:ℝ) / 32 + 5 / 2)) + 0.6931471808 +
      ((2 ^ 23 * (n:ℝ) ^ 2) - 1) / 3 * (0.6931471808 + 2 * (((n:ℝ) + 1) * 0.6931471808) +
        (21 * 0.6931471808 + 2 * ((n:ℝ) / 32 + 5 / 2)) + (17 * 0.6931471808 + ((n:ℝ) / 32 + 5 / 2))) + 0.001 <
      2 * (n : ℝ) * ((2 ^ 23 * (n:ℝ) ^ 2) + 1) * ((599:ℝ) / 600) * (2 * 0.6931471803) := by
    nlinarith only [hx, hx2, hx3]
  have hkey := mul_lt_mul_of_pos_left hpoly hNpos
  -- assemble: replace logs by numeric bounds (all with nonnegative coefficients)
  have hLRS0 : (0:ℝ) ≤ Nr * (BB6Kit.fL n : ℝ) * (BB6Kit.fR n : ℝ) / 8 := by positivity
  have hLSS0 : (0:ℝ) ≤ Nr * (BB6Kit.fL n : ℝ) * (BB6Kit.fS n : ℝ) / 8 := by positivity
  have e1 := mul_le_mul_of_nonneg_left l2hi.le hLRS0
  have e2 := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left l2hi.le (by linarith : (0:ℝ) ≤ (n:ℝ) + 3)) hLSS0
  have e3 := mul_le_mul_of_nonneg_left (by linarith only [l2hi, hlogx] : 49 * Real.log 2 + 5 * Real.log (n:ℝ) ≤
    49 * 0.6931471808 + 5 * ((n:ℝ) / 32 + 5 / 2)) hNpos.le
  have e4 := mul_le_mul_of_nonneg_left l2hi.le hNpos.le
  have hnl : ((n:ℝ) + 1) * Real.log 2 ≤ ((n:ℝ) + 1) * 0.6931471808 :=
    mul_le_mul_of_nonneg_left l2hi.le (by linarith only [hx])
  have e5 := mul_le_mul_of_nonneg_left (by linarith only [l2hi, hlogx, hnl] : Real.log 2 + 2 * (((n : ℝ) + 1) * Real.log 2) +
      (21 * Real.log 2 + 2 * Real.log n) + (17 * Real.log 2 + Real.log n) ≤
      0.6931471808 + 2 * (((n:ℝ) + 1) * 0.6931471808) + (21 * 0.6931471808 + 2 * ((n:ℝ) / 32 + 5 / 2)) +
        (17 * 0.6931471808 + ((n:ℝ) / 32 + 5 / 2))) hKm1
  have e6 := mul_le_mul_of_nonneg_left hlogN hNpos.le
  have hN1 : (1:ℝ) ≤ Nr := by rw [hNr]; nlinarith only [h5, pow_pos hn0 3]
  rw [hLr, hRr] at hT1 hT3a hT3b e1
  rw [hLr, hSr] at hT2a hT2b e2
  rw [hKr] at hB e5
  rw [hKr, hLr] at hRHS ⊢
  linarith only [hT1, hT2a, hT2b, hT3a, hT3b, hfact, e1, e2, e3, e4, e5, e6, hB, hRHS, hkey, hN1]
