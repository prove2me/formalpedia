-- Prove2me | solution 1 for DetDLP.stage1_complexity_dominance
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T11:52:53.412989+00:00
-- url     : https://prove2.me/submissions/9d3e4dc7-f934-4f65-aae0-76989707f838

import Mathlib
import Definitions.Def_DetDLP_FactorBase

set_option autoImplicit false

open DetDLP

private lemma bitLen_ge_one {p : ℕ} (hp : 2 ≤ p) : 1 ≤ bitLen p := by
  have h := Nat.le_pow_clog (by decide : 1 < 2) p
  by_contra hlt
  have h0 : bitLen p = 0 := by omega
  unfold bitLen at h0
  rw [h0, pow_zero] at h
  omega

private lemma one_le_logSafe (x : ℝ) : 1 ≤ logSafe x := le_max_left _ _

private lemma logSafe_pos (x : ℝ) : 0 < logSafe x :=
  lt_of_lt_of_le zero_lt_one (one_le_logSafe x)

private lemma logSafe_mono {x y : ℝ} (hxy : x ≤ y) : logSafe x ≤ logSafe y := by
  unfold logSafe
  refine max_le_max (le_refl 1) ?_
  exact Real.logb_le_logb_of_le (by norm_num) (by positivity) (max_le_max (le_refl 2) hxy)

private lemma mainSpaceBound_mono {C₁ C₂ b : ℕ} (hC : C₁ ≤ C₂) :
    mainSpaceBound C₁ b ≤ mainSpaceBound C₂ b := by
  unfold mainSpaceBound
  have hden : 0 < (logSafe (b : ℝ)) ^ ((1 : ℝ) / 4) :=
    Real.rpow_pos_of_pos (logSafe_pos _) _
  have hexp : (C₁ : ℝ) * (b : ℝ) / (logSafe (b : ℝ)) ^ ((1 : ℝ) / 4) ≤
      (C₂ : ℝ) * (b : ℝ) / (logSafe (b : ℝ)) ^ ((1 : ℝ) / 4) := by
    refine div_le_div_of_nonneg_right ?_ (le_of_lt hden)
    refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg b)
    exact_mod_cast hC
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp

private lemma mainSpaceBound_mul (C₁ C₂ b : ℕ) :
    mainSpaceBound C₁ b * mainSpaceBound C₂ b = mainSpaceBound (C₁ + C₂) b := by
  unfold mainSpaceBound
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 1
  push_cast
  ring

private lemma mainSpaceBound_pow (C K b : ℕ) :
    (mainSpaceBound C b) ^ K = mainSpaceBound (C * K) b := by
  unfold mainSpaceBound
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  push_cast
  ring

private lemma one_le_b_div_logSafe_rpow {b : ℕ} (hb : 1 ≤ b) :
    1 ≤ (b : ℝ) / (logSafe (b : ℝ)) ^ ((1 : ℝ) / 4) := by
  have hb_pos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : 0 < b)
  have hb1 : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hb4_ge1 : 1 ≤ b ^ 4 := Nat.one_le_pow 4 b (by omega)
  have hb_le_b4 : b ≤ b ^ 4 := Nat.le_self_pow (by decide : 4 ≠ 0) b
  have hmax_le : max (2 : ℝ) (b : ℝ) ≤ (2 : ℝ) ^ (b ^ 4 : ℕ) := by
    refine max_le ?_ ?_
    · have h2 : (2 : ℕ) ≤ 2 ^ (b ^ 4) := by
        simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hb4_ge1
      exact_mod_cast h2
    · have hlt : b < 2 ^ (b ^ 4) := lt_of_le_of_lt hb_le_b4 (Nat.lt_two_pow_self)
      exact_mod_cast le_of_lt hlt
  have hlogb_le : Real.logb 2 (max 2 (b : ℝ)) ≤ (b : ℝ) ^ (4 : ℝ) := by
    calc Real.logb 2 (max 2 (b : ℝ))
        ≤ Real.logb 2 ((2 : ℝ) ^ (b ^ 4 : ℕ)) :=
          Real.logb_le_logb_of_le (by norm_num) (by positivity) hmax_le
      _ = ((b ^ 4 : ℕ) : ℝ) := by
          rw [← Real.rpow_natCast, Real.logb_rpow (by norm_num) (by norm_num)]
      _ = (b : ℝ) ^ (4 : ℝ) := by rw [Nat.cast_pow, ← Real.rpow_natCast]; rfl
  have hL_le : logSafe (b : ℝ) ≤ (b : ℝ) ^ (4 : ℝ) := by
    unfold logSafe
    exact max_le (by simpa using Real.one_le_rpow hb1 (by norm_num : (0 : ℝ) ≤ 4)) hlogb_le
  have hLr_le : (logSafe (b : ℝ)) ^ ((1 : ℝ) / 4) ≤ (b : ℝ) := by
    calc (logSafe (b : ℝ)) ^ ((1 : ℝ) / 4)
        ≤ ((b : ℝ) ^ (4 : ℝ)) ^ ((1 : ℝ) / 4) :=
          Real.rpow_le_rpow (le_of_lt (logSafe_pos _)) hL_le (by norm_num)
      _ = (b : ℝ) ^ ((4 : ℝ) * ((1 : ℝ) / 4)) := by rw [← Real.rpow_mul (le_of_lt hb_pos)]
      _ = (b : ℝ) := by norm_num
  have hLr_pos : 0 < (logSafe (b : ℝ)) ^ ((1 : ℝ) / 4) :=
    Real.rpow_pos_of_pos (logSafe_pos _) _
  exact (one_le_div hLr_pos).mpr hLr_le

private lemma pow2_le_mainSpaceBound (k : ℕ) {b : ℕ} (hb : 1 ≤ b) :
    (2 : ℝ) ^ (k : ℝ) ≤ mainSpaceBound k b := by
  unfold mainSpaceBound
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ?_
  have h1 := one_le_b_div_logSafe_rpow hb
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  calc (k : ℝ) = (k : ℝ) * 1 := (mul_one _).symm
    _ ≤ (k : ℝ) * ((b : ℝ) / (logSafe (b : ℝ)) ^ ((1 : ℝ) / 4)) :=
        mul_le_mul_of_nonneg_left h1 hk
    _ = (k : ℝ) * (b : ℝ) / (logSafe (b : ℝ)) ^ ((1 : ℝ) / 4) := (mul_div_assoc _ _ _).symm

private lemma nat_le_mainSpaceBound (k : ℕ) {b : ℕ} (hb : 1 ≤ b) :
    (k : ℝ) ≤ mainSpaceBound k b := by
  have h1 : k ≤ 2 ^ k := le_of_lt Nat.lt_two_pow_self
  have h1R : (k : ℝ) ≤ (2 : ℝ) ^ (k : ℝ) := by
    have h2 : ((k : ℕ) : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := by exact_mod_cast h1
    simpa [Real.rpow_natCast] using h2
  exact le_trans h1R (pow2_le_mainSpaceBound k hb)

private lemma b_plus_one_le_mainSpaceBound {b : ℕ} (hb : 1 ≤ b) :
    (b : ℝ) + 1 ≤ mainSpaceBound 64 b := by
  have hb_pos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : 0 < b)
  have hb1 : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  set L : ℝ := logSafe (b : ℝ)
  have hL1 : 1 ≤ L := one_le_logSafe _
  have hL_pos : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  -- Step 1: b + 1 ≤ 2^(L + 1)
  have hbp1_le_pow : (b : ℝ) + 1 ≤ (2 : ℝ) ^ (L + 1) := by
    have hle1 : (b : ℝ) + 1 ≤ 2 * max 2 (b : ℝ) := by
      have hm1 : 2 ≤ max (2 : ℝ) (b : ℝ) := le_max_left _ _
      have hm2 : (b : ℝ) ≤ max (2 : ℝ) (b : ℝ) := le_max_right _ _
      linarith
    have hmax_eq : max (2 : ℝ) (b : ℝ) = (2 : ℝ) ^ Real.logb 2 (max 2 (b : ℝ)) :=
      (Real.rpow_logb (by norm_num) (by norm_num) (by positivity)).symm
    have hmax_le : max (2 : ℝ) (b : ℝ) ≤ (2 : ℝ) ^ L := by
      rw [hmax_eq]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (le_max_right _ _)
    calc (b : ℝ) + 1 ≤ 2 * max 2 (b : ℝ) := hle1
      _ ≤ 2 * (2 : ℝ) ^ L := by linarith
      _ = (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ L := by rw [Real.rpow_one]
      _ = (2 : ℝ) ^ (1 + L) := (Real.rpow_add (by norm_num) 1 L).symm
      _ = (2 : ℝ) ^ (L + 1) := by ring_nf
  -- Step 2: L ≤ 16 * b^(1/8)
  have hL_le_b18 : L ≤ 16 * (b : ℝ) ^ ((1 : ℝ) / 8) := by
    by_cases hb2 : (b : ℝ) ≤ 2
    · have hmax2 : max (2 : ℝ) (b : ℝ) = 2 := max_eq_left hb2
      have hL_eq : L = 1 := by
        dsimp only [L]
        unfold logSafe
        rw [hmax2, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), max_self]
      have hb18_ge1 : 1 ≤ (b : ℝ) ^ ((1 : ℝ) / 8) := Real.one_le_rpow hb1 (by norm_num)
      linarith
    · push Not at hb2
      have hmaxb : max (2 : ℝ) (b : ℝ) = (b : ℝ) := max_eq_right (le_of_lt hb2)
      have h1_le_logb : 1 ≤ Real.logb 2 (b : ℝ) := by
        rw [← Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
        exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) (le_of_lt hb2)
      have hL_eq : L = Real.log (b : ℝ) / Real.log 2 := by
        dsimp only [L]
        unfold logSafe
        rw [hmaxb, max_eq_right h1_le_logb, Real.logb]
      have hlog_b : Real.log ((b : ℝ) ^ ((1 : ℝ) / 8)) ≤ (b : ℝ) ^ ((1 : ℝ) / 8) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      rw [Real.log_rpow hb_pos] at hlog_b
      have hlog_le : Real.log (b : ℝ) ≤ 8 * (b : ℝ) ^ ((1 : ℝ) / 8) := by linarith
      have hlog2_gt : (1 : ℝ) / 2 < Real.log 2 := by
        linarith [Real.log_two_gt_d9]
      rw [hL_eq, div_le_iff₀ (by linarith)]
      have hmul : (16 * (b : ℝ) ^ ((1 : ℝ) / 8)) * (1 / 2) ≤
          (16 * (b : ℝ) ^ ((1 : ℝ) / 8)) * Real.log 2 :=
        mul_le_mul_of_nonneg_left (le_of_lt hlog2_gt) (by positivity)
      linarith
  -- Step 3: L^(5/4) ≤ 32 * b
  have hL54_le : L ^ ((5 : ℝ) / 4) ≤ 32 * (b : ℝ) := by
    have hpow : L ^ ((5 : ℝ) / 4) ≤ (16 * (b : ℝ) ^ ((1 : ℝ) / 8)) ^ ((5 : ℝ) / 4) :=
      Real.rpow_le_rpow (le_of_lt hL_pos) hL_le_b18 (by norm_num)
    rw [Real.mul_rpow (by norm_num) (by positivity)] at hpow
    have h16 : (16 : ℝ) ^ ((5 : ℝ) / 4) = 32 := by
      have h16_eq : (16 : ℝ) = (2 : ℝ) ^ (4 : ℝ) := by norm_num
      rw [h16_eq, ← Real.rpow_mul (by norm_num)]
      norm_num
    have hb532 : ((b : ℝ) ^ ((1 : ℝ) / 8)) ^ ((5 : ℝ) / 4) ≤ (b : ℝ) := by
      rw [← Real.rpow_mul (le_of_lt hb_pos)]
      calc (b : ℝ) ^ (((1 : ℝ) / 8) * ((5 : ℝ) / 4))
          ≤ (b : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hb1 (by norm_num)
        _ = (b : ℝ) := Real.rpow_one _
    rw [h16] at hpow
    linarith
  -- Step 4: L + 1 ≤ 64 * b / L^(1/4)
  have hLr_pos : 0 < L ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hL_pos _
  have hL_split : L ^ ((5 : ℝ) / 4) = L * L ^ ((1 : ℝ) / 4) := by
    have h54 : ((5 : ℝ) / 4) = 1 + (1 : ℝ) / 4 := by norm_num
    rw [h54, Real.rpow_add hL_pos, Real.rpow_one]
  have hexp_le : L + 1 ≤ 64 * (b : ℝ) / L ^ ((1 : ℝ) / 4) := by
    rw [le_div_iff₀ hLr_pos]
    calc (L + 1) * L ^ ((1 : ℝ) / 4)
        ≤ (2 * L) * L ^ ((1 : ℝ) / 4) :=
          mul_le_mul_of_nonneg_right (by linarith) (le_of_lt hLr_pos)
      _ = 2 * (L * L ^ ((1 : ℝ) / 4)) := by ring
      _ = 2 * L ^ ((5 : ℝ) / 4) := by rw [← hL_split]
      _ ≤ 2 * (32 * (b : ℝ)) := by linarith
      _ = 64 * (b : ℝ) := by ring
  unfold mainSpaceBound
  calc (b : ℝ) + 1 ≤ (2 : ℝ) ^ (L + 1) := hbp1_le_pow
    _ ≤ (2 : ℝ) ^ (64 * (b : ℝ) / L ^ ((1 : ℝ) / 4)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp_le
    _ = (2 : ℝ) ^ ((64 : ℕ) * (b : ℝ) / (logSafe (b : ℝ)) ^ ((1 : ℝ) / 4)) := by
        norm_num [L]

private lemma blockCount_bounds {b : ℕ} (hb : 1 ≤ b) :
    (logSafe (b : ℝ)) ^ ((1 : ℝ) / 4) ≤ (blockCount b : ℝ) ∧
    (blockCount b : ℝ) ≤ 4 * (logSafe (b : ℝ)) ^ ((1 : ℝ) / 4) := by
  have hL1 : 1 ≤ logSafe (b : ℝ) := one_le_logSafe _
  have hL_pos : 0 < logSafe (b : ℝ) := logSafe_pos _
  -- First, logSafe b ≤ Nat.clog 2 (b + 2)
  have hclog_ge1 : 1 ≤ Nat.clog 2 (b + 2) := Nat.clog_pos (by decide) (by omega)
  have hclog_ge1R : (1 : ℝ) ≤ (Nat.clog 2 (b + 2) : ℝ) := by exact_mod_cast hclog_ge1
  have hL_le_clog : logSafe (b : ℝ) ≤ (Nat.clog 2 (b + 2) : ℝ) := by
    have hmax_le : max (2 : ℝ) (b : ℝ) ≤ (2 : ℝ) ^ (Nat.clog 2 (b + 2)) := by
      have hpow : b + 2 ≤ 2 ^ Nat.clog 2 (b + 2) := Nat.le_pow_clog (by decide) (b + 2)
      refine max_le ?_ ?_
      · have : 2 ≤ 2 ^ Nat.clog 2 (b + 2) := by omega
        exact_mod_cast this
      · have : b ≤ 2 ^ Nat.clog 2 (b + 2) := by omega
        exact_mod_cast this
    unfold logSafe
    refine max_le hclog_ge1R ?_
    calc Real.logb 2 (max 2 (b : ℝ))
        ≤ Real.logb 2 ((2 : ℝ) ^ (Nat.clog 2 (b + 2))) :=
          Real.logb_le_logb_of_le (by norm_num) (by positivity) hmax_le
      _ = (Nat.clog 2 (b + 2) : ℝ) := by
          rw [← Real.rpow_natCast, Real.logb_rpow (by norm_num) (by norm_num)]
  have hlower : (logSafe (b : ℝ)) ^ ((1 : ℝ) / 4) ≤ (blockCount b : ℝ) := by
    have hrpow : (logSafe (b : ℝ)) ^ ((1 : ℝ) / 4) ≤
        ((Nat.clog 2 (b + 2) : ℝ)) ^ ((1 : ℝ) / 4) :=
      Real.rpow_le_rpow (le_of_lt hL_pos) hL_le_clog (by norm_num)
    have hceil : ((Nat.clog 2 (b + 2) : ℝ)) ^ ((1 : ℝ) / 4) ≤
        (Nat.ceil ((Nat.clog 2 (b + 2) : ℝ) ^ ((1 : ℝ) / 4)) : ℝ) :=
      Nat.le_ceil _
    have hmax : Nat.ceil ((Nat.clog 2 (b + 2) : ℝ) ^ ((1 : ℝ) / 4)) ≤ blockCount b :=
      le_max_right _ _
    have hmaxR : (Nat.ceil ((Nat.clog 2 (b + 2) : ℝ) ^ ((1 : ℝ) / 4)) : ℝ) ≤
        (blockCount b : ℝ) := by exact_mod_cast hmax
    exact le_trans hrpow (le_trans hceil hmaxR)
  -- Second, Nat.clog 2 (b + 2) ≤ 3 * logSafe b
  have hclog_le_3L : (Nat.clog 2 (b + 2) : ℝ) ≤ 3 * logSafe (b : ℝ) := by
    by_cases hb1 : b = 1
    · subst hb1
      have hc : Nat.clog 2 (1 + 2) = 2 := by decide
      rw [hc]
      norm_num at hL1 ⊢
      linarith
    · have hb2 : 2 ≤ b := by omega
      have hbp2 : Nat.clog 2 (b + 2) ≤ Nat.clog 2 b + 1 := by
        have h1 : b + 2 ≤ 2 * b := by omega
        have h2 : 2 * b ≤ 2 ^ (Nat.clog 2 b + 1) := by
          rw [pow_succ']
          exact Nat.mul_le_mul_left 2 (Nat.le_pow_clog (by decide : 1 < 2) b)
        exact Nat.clog_le_of_le_pow (le_trans h1 h2)
      -- 2^(Nat.clog 2 b - 1) < b
      have hpow_lt : 2 ^ (Nat.clog 2 b - 1) < b :=
        Nat.pow_pred_clog_lt_self (by decide : 1 < 2) (by omega)
      have hclog_b_le : (Nat.clog 2 b : ℝ) - 1 ≤ Real.logb 2 (b : ℝ) := by
        have hk1 : 1 ≤ Nat.clog 2 b := Nat.clog_pos (by decide) (by omega)
        have hpow_ltR : (2 : ℝ) ^ ((Nat.clog 2 b - 1 : ℕ) : ℝ) < (b : ℝ) := by
          have h : ((2 ^ (Nat.clog 2 b - 1) : ℕ) : ℝ) < (b : ℝ) := by exact_mod_cast hpow_lt
          simpa [Real.rpow_natCast] using h
        have hle := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity)
          (le_of_lt hpow_ltR)
        rw [Real.logb_rpow (by norm_num) (by norm_num)] at hle
        have hcast : ((Nat.clog 2 b - 1 : ℕ) : ℝ) = (Nat.clog 2 b : ℝ) - 1 := by
          rw [Nat.cast_sub hk1]; norm_num
        linarith
      have hlogb_le_L : Real.logb 2 (b : ℝ) ≤ logSafe (b : ℝ) := by
        unfold logSafe
        have hbm : max (2 : ℝ) (b : ℝ) = (b : ℝ) := max_eq_right (by exact_mod_cast hb2)
        rw [hbm]
        exact le_max_right _ _
      have hclog_bp2R : (Nat.clog 2 (b + 2) : ℝ) ≤ (Nat.clog 2 b : ℝ) + 1 := by
        exact_mod_cast hbp2
      linarith
  have hupper : (blockCount b : ℝ) ≤ 4 * (logSafe (b : ℝ)) ^ ((1 : ℝ) / 4) := by
    unfold blockCount
    rcases le_total (Nat.ceil ((Nat.clog 2 (b + 2) : ℝ) ^ ((1 : ℝ) / 4))) 2 with hle | hge
    · rw [max_eq_left hle]
      have h1 : (1 : ℝ) ≤ (logSafe (b : ℝ)) ^ ((1 : ℝ) / 4) :=
        Real.one_le_rpow hL1 (by norm_num)
      linarith
    · rw [max_eq_right hge]
      set x : ℝ := (Nat.clog 2 (b + 2) : ℝ) ^ ((1 : ℝ) / 4)
      have hx1 : 1 ≤ x := Real.one_le_rpow hclog_ge1R (by norm_num)
      have hceil_lt : (Nat.ceil x : ℝ) < x + 1 := Nat.ceil_lt_add_one (by linarith)
      have hx_le : x ≤ (3 * logSafe (b : ℝ)) ^ ((1 : ℝ) / 4) :=
        Real.rpow_le_rpow (by positivity) hclog_le_3L (by norm_num)
      rw [Real.mul_rpow (by norm_num) (le_of_lt hL_pos)] at hx_le
      have h3r : (3 : ℝ) ^ ((1 : ℝ) / 4) ≤ 2 := by
        rw [← Real.rpow_le_rpow_iff (by positivity) (by norm_num) (by norm_num : (0 : ℝ) < 4)]
        rw [← Real.rpow_mul (by norm_num)]
        norm_num
      have hx_le2 : x ≤ 2 * (logSafe (b : ℝ)) ^ ((1 : ℝ) / 4) := by
        have hnn : 0 ≤ (logSafe (b : ℝ)) ^ ((1 : ℝ) / 4) := by positivity
        calc x ≤ (3 : ℝ) ^ ((1 : ℝ) / 4) * (logSafe (b : ℝ)) ^ ((1 : ℝ) / 4) := hx_le
          _ ≤ 2 * (logSafe (b : ℝ)) ^ ((1 : ℝ) / 4) := mul_le_mul_of_nonneg_right h3r hnn
      linarith
  exact ⟨hlower, hupper⟩

theorem solution :
    (∀ (C₁ C₂ b : ℕ), C₁ ≤ C₂ →
      mainSpaceBound C₁ b ≤ mainSpaceBound C₂ b ∧ polyBound C₁ b ≤ polyBound C₂ b) ∧
    (∀ (K b : ℕ),
      (2 : ℝ) ^ ((K : ℝ) * (b : ℝ) / Real.sqrt (logSafe (b : ℝ))) ≤ mainSpaceBound K b) ∧
    (∀ (K C_fb : ℕ), ∃ C : ℕ,
      ∀ (p gord : ℕ), 2 ≤ p → gord ≤ 3 * p →
        let b := bitLen p
        let m := blockCount b
        polyBound K b ≤ mainSpaceBound C b ∧
        polyBound K b *
          ((C_fb : ℝ) * ((m : ℝ) ^ 2 + (m : ℝ) * (gord : ℝ) ^ ((1 : ℝ) / (m : ℝ)))) ≤
          mainSpaceBound C b) ∧
    (∀ (K K_u K_s : ℕ), ∃ C : ℕ,
      ∀ (p u s : ℕ), 2 ≤ p →
        let b := bitLen p
        let m := blockCount b
        u ≤ K_u * m * b → b ≤ s → s ≤ K_s * m * b →
        btnTimeBound K u s ≤ mainSpaceBound C b) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Conjunct 1: monotonicity in C
    intro C₁ C₂ b hC
    refine ⟨mainSpaceBound_mono hC, ?_⟩
    unfold polyBound
    have hbase : (1 : ℝ) ≤ (b : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) b]
    have hpow : ((b : ℝ) + 1) ^ C₁ ≤ ((b : ℝ) + 1) ^ C₂ := pow_le_pow_right₀ hbase hC
    have hCr : (C₁ : ℝ) ≤ (C₂ : ℝ) := by exact_mod_cast hC
    exact mul_le_mul hCr hpow (by positivity) (by positivity)
  · -- Conjunct 2: factoring runtime fits inside mainSpaceBound
    intro K b
    unfold mainSpaceBound
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ?_
    have hL1 : 1 ≤ logSafe (b : ℝ) := one_le_logSafe _
    have hpow_le : (logSafe (b : ℝ)) ^ ((1 : ℝ) / 4) ≤ Real.sqrt (logSafe (b : ℝ)) := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    have hden_pos : 0 < (logSafe (b : ℝ)) ^ ((1 : ℝ) / 4) :=
      Real.rpow_pos_of_pos (logSafe_pos _) _
    have hnum_nn : 0 ≤ (K : ℝ) * (b : ℝ) := by positivity
    exact div_le_div_of_nonneg_left hnum_nn hden_pos hpow_le
  · -- Conjunct 3: polyBound K b and polyBound K b * (C_fb * (m^2 + m * gord^(1/m))) ≤ mainSpaceBound C b
    intro K C_fb
    refine ⟨65 * K + C_fb + 133, fun p gord hp hgord => ?_⟩
    dsimp only
    set b := bitLen p
    set m := blockCount b
    have hb : 1 ≤ b := bitLen_ge_one hp
    have hpoly : polyBound K b ≤ mainSpaceBound (65 * K) b := by
      unfold polyBound
      have hK : (K : ℝ) ≤ mainSpaceBound K b := nat_le_mainSpaceBound K hb
      have hb1 : ((b : ℝ) + 1) ^ K ≤ mainSpaceBound (64 * K) b := by
        rw [← mainSpaceBound_pow 64 K b]
        exact pow_le_pow_left₀ (by positivity) (b_plus_one_le_mainSpaceBound hb) K
      calc (K : ℝ) * ((b : ℝ) + 1) ^ K
          ≤ mainSpaceBound K b * mainSpaceBound (64 * K) b :=
            mul_le_mul hK hb1 (by positivity) (by unfold mainSpaceBound; positivity)
        _ = mainSpaceBound (K + 64 * K) b := mainSpaceBound_mul K (64 * K) b
        _ = mainSpaceBound (65 * K) b := by ring_nf
    have hpolyC : polyBound K b ≤ mainSpaceBound (65 * K + C_fb + 133) b :=
      le_trans hpoly (mainSpaceBound_mono (by omega))
    refine ⟨hpolyC, ?_⟩
    have ⟨hm_lo, hm_hi⟩ := blockCount_bounds hb
    have hm_le_msb : (m : ℝ) ≤ mainSpaceBound 66 b := by
      have hLr_le_b : (logSafe (b : ℝ)) ^ ((1 : ℝ) / 4) ≤ (b : ℝ) := by
        have h1 := one_le_b_div_logSafe_rpow hb
        have hden : 0 < (logSafe (b : ℝ)) ^ ((1 : ℝ) / 4) :=
          Real.rpow_pos_of_pos (logSafe_pos _) _
        exact (one_le_div hden).mp h1
      have hbp1 := b_plus_one_le_mainSpaceBound hb
      have h4 : (4 : ℝ) ≤ mainSpaceBound 2 b := by
        have h2 : (4 : ℝ) = (2 : ℝ) ^ ((2 : ℕ) : ℝ) := by norm_num
        rw [h2]; exact pow2_le_mainSpaceBound 2 hb
      calc (m : ℝ) ≤ 4 * (logSafe (b : ℝ)) ^ ((1 : ℝ) / 4) := hm_hi
        _ ≤ 4 * ((b : ℝ) + 1) := by linarith
        _ ≤ mainSpaceBound 2 b * mainSpaceBound 64 b :=
            mul_le_mul h4 hbp1 (by positivity) (by unfold mainSpaceBound; positivity)
        _ = mainSpaceBound 66 b := mainSpaceBound_mul 2 64 b
    have hgord_le_msb : (gord : ℝ) ^ ((1 : ℝ) / (m : ℝ)) ≤ mainSpaceBound 3 b := by
      have hp_pow : p ≤ 2 ^ b := Nat.le_pow_clog (by decide) p
      have hg_pow : gord ≤ 2 ^ (b + 2) := by
        have : 3 * p ≤ 4 * 2 ^ b := by omega
        have h4eq : 4 * 2 ^ b = 2 ^ (b + 2) := by rw [pow_add]; norm_num; ring
        omega
      have hg_powR : (gord : ℝ) ≤ (2 : ℝ) ^ ((b + 2 : ℕ) : ℝ) := by
        rw [Real.rpow_natCast]
        have h : ((gord : ℕ) : ℝ) ≤ ((2 ^ (b + 2) : ℕ) : ℝ) := by exact_mod_cast hg_pow
        simpa using h
      have hm_pos : (0 : ℝ) < (m : ℝ) := by
        have : 2 ≤ m := le_max_left _ _
        exact_mod_cast (by omega : 0 < m)
      have hrpow : (gord : ℝ) ^ ((1 : ℝ) / (m : ℝ)) ≤
          ((2 : ℝ) ^ ((b + 2 : ℕ) : ℝ)) ^ ((1 : ℝ) / (m : ℝ)) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hg_powR (by positivity)
      rw [← Real.rpow_mul (by norm_num)] at hrpow
      have hexp : ((b + 2 : ℕ) : ℝ) * ((1 : ℝ) / (m : ℝ)) ≤
          (3 : ℕ) * (b : ℝ) / (logSafe (b : ℝ)) ^ ((1 : ℝ) / 4) := by
        have hb2 : ((b + 2 : ℕ) : ℝ) ≤ (3 : ℕ) * (b : ℝ) := by
          have : b + 2 ≤ 3 * b := by omega
          exact_mod_cast this
        have hden : 0 < (logSafe (b : ℝ)) ^ ((1 : ℝ) / 4) :=
          Real.rpow_pos_of_pos (logSafe_pos _) _
        calc ((b + 2 : ℕ) : ℝ) * ((1 : ℝ) / (m : ℝ))
            = ((b + 2 : ℕ) : ℝ) / (m : ℝ) := mul_one_div _ _
          _ ≤ ((3 : ℕ) * (b : ℝ)) / (logSafe (b : ℝ)) ^ ((1 : ℝ) / 4) :=
              div_le_div₀ (by positivity) hb2 hden hm_lo
      have h2exp : (2 : ℝ) ^ (((b + 2 : ℕ) : ℝ) * ((1 : ℝ) / (m : ℝ))) ≤ mainSpaceBound 3 b := by
        unfold mainSpaceBound
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp
      exact le_trans hrpow h2exp
    have hm2 : (m : ℝ) ^ 2 ≤ mainSpaceBound 132 b := by
      have : mainSpaceBound 66 b ^ 2 = mainSpaceBound 132 b := by
        rw [mainSpaceBound_pow]
      rw [← this]
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) hm_le_msb 2
    have hmg : (m : ℝ) * (gord : ℝ) ^ ((1 : ℝ) / (m : ℝ)) ≤ mainSpaceBound 132 b := by
      calc (m : ℝ) * (gord : ℝ) ^ ((1 : ℝ) / (m : ℝ))
          ≤ mainSpaceBound 66 b * mainSpaceBound 3 b :=
            mul_le_mul hm_le_msb hgord_le_msb (by positivity) (by unfold mainSpaceBound; positivity)
        _ = mainSpaceBound 69 b := mainSpaceBound_mul 66 3 b
        _ ≤ mainSpaceBound 132 b := mainSpaceBound_mono (by omega)
    have hsum : (m : ℝ) ^ 2 + (m : ℝ) * (gord : ℝ) ^ ((1 : ℝ) / (m : ℝ)) ≤
        mainSpaceBound 133 b := by
      have h2 : (2 : ℝ) ≤ mainSpaceBound 1 b := by
        simpa using pow2_le_mainSpaceBound 1 hb
      calc (m : ℝ) ^ 2 + (m : ℝ) * (gord : ℝ) ^ ((1 : ℝ) / (m : ℝ))
          ≤ 2 * mainSpaceBound 132 b := by linarith
        _ ≤ mainSpaceBound 1 b * mainSpaceBound 132 b :=
            mul_le_mul_of_nonneg_right h2 (by unfold mainSpaceBound; positivity)
        _ = mainSpaceBound 133 b := mainSpaceBound_mul 1 132 b
    have hCfb : (C_fb : ℝ) ≤ mainSpaceBound C_fb b := nat_le_mainSpaceBound C_fb hb
    calc polyBound K b *
          ((C_fb : ℝ) * ((m : ℝ) ^ 2 + (m : ℝ) * (gord : ℝ) ^ ((1 : ℝ) / (m : ℝ))))
        ≤ mainSpaceBound (65 * K) b * (mainSpaceBound C_fb b * mainSpaceBound 133 b) := by
          refine mul_le_mul hpoly ?_ (by positivity) (by unfold mainSpaceBound; positivity)
          exact mul_le_mul hCfb hsum (by positivity) (by unfold mainSpaceBound; positivity)
      _ = mainSpaceBound (65 * K + (C_fb + 133)) b := by
          rw [mainSpaceBound_mul, mainSpaceBound_mul]
      _ = mainSpaceBound (65 * K + C_fb + 133) b := by ring_nf
  · -- Conjunct 4: Stage I BTN runtime fits inside mainSpaceBound
    intro K K_u K_s
    refine ⟨K + K * (4 * K_u + 129) + 4 * K * K_s, fun p u s hp hu hbu hsu => ?_⟩
    set b := bitLen p
    set m := blockCount b
    have hb : 1 ≤ b := bitLen_ge_one hp
    have ⟨hm_lo, hm_hi⟩ := blockCount_bounds hb
    have hLr_pos : 0 < (logSafe (b : ℝ)) ^ ((1 : ℝ) / 4) :=
      Real.rpow_pos_of_pos (logSafe_pos _) _
    have hLr_le_b : (logSafe (b : ℝ)) ^ ((1 : ℝ) / 4) ≤ (b : ℝ) := by
      exact (one_le_div hLr_pos).mp (one_le_b_div_logSafe_rpow hb)
    have hm_le_4b : (m : ℝ) ≤ 4 * (b : ℝ) := by linarith
    have hu1_le : (u : ℝ) + 1 ≤ mainSpaceBound (4 * K_u + 129) b := by
      have huR : (u : ℝ) ≤ (K_u : ℝ) * (m : ℝ) * (b : ℝ) := by exact_mod_cast hu
      have hb1 : (b : ℝ) ≤ (b : ℝ) + 1 := by linarith
      have hu_poly : (u : ℝ) + 1 ≤ ((4 * K_u + 1 : ℕ) : ℝ) * ((b : ℝ) + 1) ^ 2 := by
        have hstep : (u : ℝ) ≤ (4 * K_u : ℝ) * ((b : ℝ) + 1) ^ 2 := by
          calc (u : ℝ) ≤ (K_u : ℝ) * (m : ℝ) * (b : ℝ) := huR
            _ ≤ (K_u : ℝ) * (4 * (b : ℝ)) * (b : ℝ) := by
                refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg b)
                exact mul_le_mul_of_nonneg_left hm_le_4b (Nat.cast_nonneg K_u)
            _ = (4 * (K_u : ℝ)) * (b : ℝ) ^ 2 := by ring
            _ ≤ (4 * (K_u : ℝ)) * ((b : ℝ) + 1) ^ 2 := by
                refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                exact pow_le_pow_left₀ (Nat.cast_nonneg b) hb1 2
        have hsq1 : (1 : ℝ) ≤ ((b : ℝ) + 1) ^ 2 := by
          have : (1 : ℝ) ≤ (b : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) b]
          nlinarith
        push_cast
        linarith
      have hK4 : ((4 * K_u + 1 : ℕ) : ℝ) ≤ mainSpaceBound (4 * K_u + 1) b :=
        nat_le_mainSpaceBound (4 * K_u + 1) hb
      have hb1_sq : ((b : ℝ) + 1) ^ 2 ≤ mainSpaceBound 128 b := by
        have h128 : mainSpaceBound 64 b ^ 2 = mainSpaceBound 128 b := by
          rw [mainSpaceBound_pow]
        rw [← h128]
        exact pow_le_pow_left₀ (by positivity) (b_plus_one_le_mainSpaceBound hb) 2
      calc (u : ℝ) + 1 ≤ ((4 * K_u + 1 : ℕ) : ℝ) * ((b : ℝ) + 1) ^ 2 := hu_poly
        _ ≤ mainSpaceBound (4 * K_u + 1) b * mainSpaceBound 128 b :=
            mul_le_mul hK4 hb1_sq (by positivity) (by unfold mainSpaceBound; positivity)
        _ = mainSpaceBound (4 * K_u + 129) b := mainSpaceBound_mul _ _ _
    have hpoly_u : polyBound K u ≤ mainSpaceBound (K + K * (4 * K_u + 129)) b := by
      unfold polyBound
      have hK : (K : ℝ) ≤ mainSpaceBound K b := nat_le_mainSpaceBound K hb
      have hpow : ((u : ℝ) + 1) ^ K ≤ mainSpaceBound (K * (4 * K_u + 129)) b := by
        rw [mul_comm K _, ← mainSpaceBound_pow (4 * K_u + 129) K b]
        exact pow_le_pow_left₀ (by positivity) hu1_le K
      calc (K : ℝ) * ((u : ℝ) + 1) ^ K
          ≤ mainSpaceBound K b * mainSpaceBound (K * (4 * K_u + 129)) b :=
            mul_le_mul hK hpow (by positivity) (by unfold mainSpaceBound; positivity)
        _ = mainSpaceBound (K + K * (4 * K_u + 129)) b := mainSpaceBound_mul _ _ _
    have hexp_s : (2 : ℝ) ^ ((K : ℝ) * (s : ℝ) / Real.sqrt (logSafe (s : ℝ))) ≤
        mainSpaceBound (4 * K * K_s) b := by
      unfold mainSpaceBound
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ?_
      have hbsR : (b : ℝ) ≤ (s : ℝ) := by exact_mod_cast hbu
      have hLb_le_Ls : logSafe (b : ℝ) ≤ logSafe (s : ℝ) := logSafe_mono hbsR
      have hsqrt_le : Real.sqrt (logSafe (b : ℝ)) ≤ Real.sqrt (logSafe (s : ℝ)) :=
        Real.sqrt_le_sqrt hLb_le_Ls
      have hsqrt_split : Real.sqrt (logSafe (b : ℝ)) =
          (logSafe (b : ℝ)) ^ ((1 : ℝ) / 4) * (logSafe (b : ℝ)) ^ ((1 : ℝ) / 4) := by
        rw [Real.sqrt_eq_rpow]
        have h12 : ((1 : ℝ) / 2) = (1 : ℝ) / 4 + (1 : ℝ) / 4 := by norm_num
        rw [h12, Real.rpow_add (logSafe_pos _)]
      have hsR : (s : ℝ) ≤ (K_s : ℝ) * (m : ℝ) * (b : ℝ) := by exact_mod_cast hsu
      have hKs : (K : ℝ) * (s : ℝ) ≤
          (4 * K * K_s : ℕ) * (b : ℝ) * (logSafe (b : ℝ)) ^ ((1 : ℝ) / 4) := by
        have h1 : (s : ℝ) ≤ (K_s : ℝ) * (4 * (logSafe (b : ℝ)) ^ ((1 : ℝ) / 4)) * (b : ℝ) := by
          calc (s : ℝ) ≤ (K_s : ℝ) * (m : ℝ) * (b : ℝ) := hsR
            _ ≤ (K_s : ℝ) * (4 * (logSafe (b : ℝ)) ^ ((1 : ℝ) / 4)) * (b : ℝ) := by
                refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg b)
                exact mul_le_mul_of_nonneg_left hm_hi (Nat.cast_nonneg K_s)
        have h2 : (K : ℝ) * (s : ℝ) ≤
            (K : ℝ) * ((K_s : ℝ) * (4 * (logSafe (b : ℝ)) ^ ((1 : ℝ) / 4)) * (b : ℝ)) :=
          mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg K)
        push_cast
        linarith
      have hsqrt_b_pos : 0 < Real.sqrt (logSafe (b : ℝ)) := by
        rw [hsqrt_split]
        exact mul_pos hLr_pos hLr_pos
      calc (K : ℝ) * (s : ℝ) / Real.sqrt (logSafe (s : ℝ))
          ≤ (K : ℝ) * (s : ℝ) / Real.sqrt (logSafe (b : ℝ)) :=
            div_le_div_of_nonneg_left (by positivity) hsqrt_b_pos hsqrt_le
        _ ≤ ((4 * K * K_s : ℕ) * (b : ℝ) * (logSafe (b : ℝ)) ^ ((1 : ℝ) / 4)) /
              ((logSafe (b : ℝ)) ^ ((1 : ℝ) / 4) * (logSafe (b : ℝ)) ^ ((1 : ℝ) / 4)) := by
            rw [← hsqrt_split]
            exact div_le_div_of_nonneg_right hKs (le_of_lt hsqrt_b_pos)
        _ = ((4 * K * K_s : ℕ) : ℝ) * (b : ℝ) / (logSafe (b : ℝ)) ^ ((1 : ℝ) / 4) := by
            have hne : (logSafe (b : ℝ)) ^ ((1 : ℝ) / 4) ≠ 0 := ne_of_gt hLr_pos
            field_simp [hne]
    unfold btnTimeBound
    calc polyBound K u * (2 : ℝ) ^ ((K : ℝ) * (s : ℝ) / Real.sqrt (logSafe (s : ℝ)))
        ≤ mainSpaceBound (K + K * (4 * K_u + 129)) b * mainSpaceBound (4 * K * K_s) b :=
          mul_le_mul hpoly_u hexp_s (by positivity) (by unfold mainSpaceBound; positivity)
      _ = mainSpaceBound (K + K * (4 * K_u + 129) + 4 * K * K_s) b :=
          mainSpaceBound_mul _ _ _
