-- Prove2me | solution 1 for BB6Kit.nondegenerate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @alon yuval
-- created : 2026-11-23T22:14:09.549794+00:00
-- url     : https://prove2.me/submissions/d47bdeb7-cbeb-4b1a-9da1-50d290c86742
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BB6Delta
import Definitions.Def_BB6Kit
import Theorems.Thm_BB6Kit_prop37
import Theorems.Thm_BB6Kit_prop39_int
import Theorems.Thm_BB6Kit_zero_lemma
import Theorems.Thm_BB6Kit_params_cond
import Theorems.Thm_BB6Kit_params_synth
import Theorems.Thm_BB6Kit_excl_215
import Theorems.Thm_BB6Kit_card_box

theorem solution (i k c : ℕ) (hi : 2 ^ 60 ≤ i) (hc : 0 < c) (hc4 : c ≤ 4 * i)
    (hk2 : 2 ≤ k) (hk : k ≤ 2 * i + 2)
    (hne : ((k : ℝ) - 1) * Real.log 2 - (i : ℝ) * Real.log 3 + Real.log (c : ℝ) ≠ 0) (hind : BB6Kit.MultIndep 2 c 3) :
    -(2 ^ 30 * Real.log (4 * (i : ℝ)) ^ 3) ≤ Real.log |((k : ℝ) - 1) * Real.log 2 - (i : ℝ) * Real.log 3 + Real.log (c : ℝ)| := by
  by_contra hcon
  push_neg at hcon
  set Λ : ℝ := ((k : ℝ) - 1) * Real.log 2 - (i : ℝ) * Real.log 3 + Real.log (c : ℝ) with hΛdef
  have hΛpos : 0 < |Λ| := abs_pos.mpr hne
  have hi0 : i ≠ 0 := by
    have : 0 < i := lt_of_lt_of_le (by norm_num) hi
    omega
  -- n = ⌊log₂ i⌋
  set n := Nat.log 2 i with hndef
  have h2n : 2 ^ n ≤ i := Nat.pow_log_le_self 2 hi0
  have h2n' : i < 2 ^ (n + 1) := Nat.lt_pow_succ_log_self (by norm_num) i
  have hn : 60 ≤ n := by
    by_contra hlt
    push_neg at hlt
    have : 2 ^ (n + 1) ≤ 2 ^ 60 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨hK3, hL5, hRST, hpos, h27, hχ, h29, h210', h211', h212, h213, hT, hLT, hKL⟩ :=
    BB6Kit.params_cond n hn
  -- 1 < c from independence
  have hc1 : 1 < c := by
    by_contra h
    have hc' : c = 1 := by omega
    have := hind 0 1 0 (by subst hc'; simp)
    simp at this
  -- the kit's form of Λ
  have hkitΛ : ((k - 1 : ℕ) : ℝ) * Real.log ((2 : ℕ) : ℝ) + ((1 : ℕ) : ℝ) * Real.log (c : ℝ) -
      (i : ℝ) * Real.log ((3 : ℕ) : ℝ) = Λ := by
    rw [hΛdef, Nat.cast_sub (by omega : 1 ≤ k)]
    push_cast
    ring
  have hΛne : ((k - 1 : ℕ) : ℝ) * Real.log ((2 : ℕ) : ℝ) + ((1 : ℕ) : ℝ) * Real.log (c : ℝ) -
      (i : ℝ) * Real.log ((3 : ℕ) : ℝ) ≠ 0 := by rw [hkitΛ]; exact hne
  -- smallness of |Λ|
  have hiR : (2:ℝ) ^ n ≤ (i : ℝ) := by exact_mod_cast h2n
  have h4i : (n + 2) * Real.log 2 ≤ Real.log (4 * (i : ℝ)) := by
    have h1 : (2:ℝ) ^ (n + 2) ≤ 4 * (i : ℝ) := by
      rw [pow_add]; norm_num; linarith
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_pow] at h2
    push_cast at h2
    exact h2
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcube : (((n : ℝ) + 2) * Real.log 2) ^ 3 ≤ Real.log (4 * (i : ℝ)) ^ 3 :=
    pow_le_pow_left₀ (by positivity) (by exact_mod_cast h4i) 3
  have hlogΛ : Real.log |Λ| < -((BB6Kit.fK n : ℝ) * (BB6Kit.fL n : ℝ) * Real.log 4) := by
    have : (2:ℝ) ^ 30 * (((n : ℝ) + 2) * Real.log 2) ^ 3 ≤ 2 ^ 30 * Real.log (4 * (i : ℝ)) ^ 3 := by
      have := mul_le_mul_of_nonneg_left hcube (by positivity : (0:ℝ) ≤ 2 ^ 30)
      linarith
    linarith
  have hΛsmall : |Λ| < Real.exp (-((BB6Kit.fK n : ℝ) * (BB6Kit.fL n : ℝ) * Real.log 4)) := by
    have := Real.exp_lt_exp.mpr hlogΛ
    rwa [Real.exp_log hΛpos] at this
  have hKLpos : 0 ≤ (BB6Kit.fK n : ℝ) * (BB6Kit.fL n : ℝ) * Real.log 4 := by positivity
  have hΛ1 : |Λ| < 1 := by
    have : Real.exp (-((BB6Kit.fK n : ℝ) * (BB6Kit.fL n : ℝ) * Real.log 4)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; linarith
    linarith
  -- Λ' < 4^(-KL)
  have hLam' : BB6Kit.lamPrime (BB6Kit.fL n) (BB6Kit.fR n) i
      (((k - 1 : ℕ) : ℝ) * Real.log ((2 : ℕ) : ℝ) + ((1 : ℕ) : ℝ) * Real.log (c : ℝ) -
        (i : ℝ) * Real.log ((3 : ℕ) : ℝ)) < (4:ℝ) ^ (-((BB6Kit.fK n : ℝ) * (BB6Kit.fL n : ℝ))) := by
    rw [hkitΛ]
    unfold BB6Kit.lamPrime
    have hA : ((BB6Kit.fL n : ℝ) * (BB6Kit.fR n : ℝ)) ≤ (i : ℝ) := by
      have : BB6Kit.fL n * BB6Kit.fR n ≤ i := le_trans hLT h2n
      exact_mod_cast this
    have hA0 : 0 ≤ ((BB6Kit.fL n : ℝ) * (BB6Kit.fR n : ℝ)) := by positivity
    have hipos : (0:ℝ) < i := by positivity
    have hexp : Real.exp ((BB6Kit.fL n : ℝ) * (BB6Kit.fR n : ℝ) * |Λ| / (2 * (i : ℝ))) ≤ 2 := by
      have h1 : (BB6Kit.fL n : ℝ) * (BB6Kit.fR n : ℝ) * |Λ| / (2 * (i : ℝ)) ≤ Real.log 2 := by
        rw [div_le_iff₀ (by positivity)]
        have := Real.log_two_gt_d9
        nlinarith [abs_nonneg Λ]
      calc _ ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr h1
        _ = 2 := Real.exp_log (by norm_num)
    have hmain : |Λ| * ((BB6Kit.fL n : ℝ) * (BB6Kit.fR n : ℝ) *
        Real.exp ((BB6Kit.fL n : ℝ) * (BB6Kit.fR n : ℝ) * |Λ| / (2 * (i : ℝ)))) / (2 * (i : ℝ)) ≤ |Λ| := by
      rw [div_le_iff₀ (by positivity)]
      have h1 : (BB6Kit.fL n : ℝ) * (BB6Kit.fR n : ℝ) *
          Real.exp ((BB6Kit.fL n : ℝ) * (BB6Kit.fR n : ℝ) * |Λ| / (2 * (i : ℝ))) ≤ (i : ℝ) * 2 :=
        mul_le_mul hA hexp (Real.exp_pos _).le hipos.le
      have := mul_le_mul_of_nonneg_left h1 (abs_nonneg Λ)
      nlinarith
    have hrp : (4:ℝ) ^ (-((BB6Kit.fK n : ℝ) * (BB6Kit.fL n : ℝ))) =
        Real.exp (-((BB6Kit.fK n : ℝ) * (BB6Kit.fL n : ℝ) * Real.log 4)) := by
      rw [Real.rpow_def_of_pos (by norm_num)]
      ring_nf
    rw [hrp]
    linarith
  have hgcd : Nat.gcd (Nat.gcd (k - 1) 1) i = 1 := by simp
  have h214 : ¬ (k - 1 ≤ max (BB6Kit.fR1 n) (BB6Kit.fR2 n) ∧ 1 ≤ max (BB6Kit.fS1 n) (BB6Kit.fS2 n) ∧
      i ≤ max (BB6Kit.fR1 n) (BB6Kit.fR2 n)) := by
    rintro ⟨_, _, h⟩
    exact absurd (lt_of_lt_of_le hT h2n) (not_lt.mpr h)
  have h210 := h210'
  rw [← BB6Kit.card_box 2 c 3 (BB6Kit.fR1 n) (BB6Kit.fS1 n) (BB6Kit.fR1 n) (by norm_num) hc (by norm_num) hind]
    at h210
  have h211 := h211'
  rw [← BB6Kit.card_box 2 c 3 (BB6Kit.fR2 n) (BB6Kit.fS2 n) (BB6Kit.fR2 n) (by norm_num) hc (by norm_num) hind]
    at h211
  have hexcl := BB6Kit.excl_215 n i k c hn h2n h2n' hc hc4 hk2 hk hΛ1
  obtain ⟨kml, rst, hrows, hcols, hΔ⟩ :=
    BB6Kit.zero_lemma (BB6Kit.fK n) (BB6Kit.fL n) (BB6Kit.fR n) (BB6Kit.fS n) (BB6Kit.fR n) (BB6Kit.fN n)
      (k - 1) 1 i 2 c 3 (BB6Kit.fR1 n) (BB6Kit.fS1 n) (BB6Kit.fR1 n) (BB6Kit.fR2 n) (BB6Kit.fS2 n) (BB6Kit.fR2 n)
      (BB6Kit.fR3 n) (BB6Kit.fS3 n) (BB6Kit.fR3 n) (BB6Kit.fChi n)
      hK3 hL5 rfl hRST (by norm_num) hc1 (by norm_num) hind (by omega) one_pos (by omega) hgcd hΛne
      hpos h27 hχ h29 h210 h211 h212 h213 h214 hexcl
  have hup := BB6Kit.prop37 (BB6Kit.fK n) (BB6Kit.fL n) (BB6Kit.fR n) (BB6Kit.fS n) (BB6Kit.fR n) (BB6Kit.fN n)
      (k - 1) 1 i 2 c 3 4 hK3 hL5 rfl hRST (by norm_num) hc1 (by norm_num) hind (by omega) one_pos (by omega)
      hgcd hΛne (by norm_num) kml rst hrows hcols hLam'
  have hlow := BB6Kit.prop39_int (BB6Kit.fK n) (BB6Kit.fL n) (BB6Kit.fR n) (BB6Kit.fS n) (BB6Kit.fR n) (BB6Kit.fN n)
      (k - 1) 1 i 2 c 3 hK3 hL5 rfl hRST (by norm_num) (by omega) (by norm_num) kml rst hrows hcols hΔ
  have hsyn := BB6Kit.params_synth n i k c hn h2n h2n' hc hc4 hk2 hk
  have hup' := (Real.log_lt_iff_lt_exp (abs_pos.mpr hΔ)).mpr hup
  linarith
