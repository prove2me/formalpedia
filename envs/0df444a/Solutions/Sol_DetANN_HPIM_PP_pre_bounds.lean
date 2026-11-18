-- Prove2me | solution 1 for DetANN.HPIM.PP.pre_bounds
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-17T09:27:32.011891+00:00
-- url     : https://prove2.me/submissions/8b80fc18-da44-4657-80e7-5036cc5e932c

import Mathlib
import Definitions.Def_DetANN_HPIMPreProg
import Definitions.Def_PNormReg_Machine
import Definitions.Def_PNormRegLib_Exec
import Definitions.Def_DetANN_DataStructure
import Definitions.Def_DetANN_HPIMLayout
import Definitions.Def_DetANN_HPIMWF
import Definitions.Def_PNormRegLib_Reloc
import Definitions.Def_DetANN_HPIMPreBlocks

-- ===== PP_Init =====
namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth DetANN DetANN.HPIM Classical

section Input

variable {m N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ)

end Input

lemma gCond_ex (δ : ℝ) (N : ℕ) (hδ : 0 < δ) : ∃ k, gCond N δ k := by
  have he : 1 < 1 + δ / 4 := by linarith
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (8 * (N : ℝ) * lamOf N δ * (1 + δ / 4)) he
  refine ⟨k, ?_⟩
  unfold gCond
  rw [one_div_mul_eq_div, le_div_iff₀ (by linarith)]
  linarith

variable {m N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ)

end DetANN.HPIM.PP

-- ===== PP_Budget =====
namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth DetANN DetANN.HPIM Classical

lemma bspFuel_le (n m : ℕ) {δ : ℝ} (hδ : 0 < δ) : bspFuel n m δ ≤ n * Gn m δ + 1 := by
  unfold bspFuel Gn
  have : ⌈(n : ℝ) * ((2 : ℝ) ^ 12 / (δ / 4)) ^ (2 * m)⌉₊ ≤ n * ⌈((2 : ℝ) ^ 12 / (δ / 4)) ^ (2 * m)⌉₊ :=
    Nat.ceil_le.2 (by push_cast; exact mul_le_mul_of_nonneg_left (Nat.le_ceil _) (Nat.cast_nonneg _))
  omega

lemma bspB_le {m n : ℕ} {δ : ℝ} (hδ : 0 < δ) (hn : 1 ≤ n) : bspB n m δ ≤ n * (2 * Gn m δ + 3) := by
  unfold bspB
  have := bspFuel_le n m hδ
  have e : n * (2 * Gn m δ + 3) = 2 * (n * Gn m δ) + 3 * n := by ring
  omega

section

variable {B : Blocks} (ch : ChildOK B)

end

variable {m N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ)

end DetANN.HPIM.PP

-- ===== PP_Asym =====
namespace DetANN.HPIM.PP

open DetANN DetANN.HPIM Classical

lemma clog_le_logb (K : ℕ) (hK : 1 ≤ K) : (Nat.clog 2 K : ℝ) ≤ Real.logb 2 K + 1 := by
  rcases Nat.eq_or_lt_of_le hK with h | hK'
  · subst h; simp
  · have h := Nat.pow_pred_clog_lt_self (by norm_num : 1 < 2) hK'
    have h' : ((2 : ℝ) ^ (Nat.clog 2 K).pred) < K := by exact_mod_cast h
    have h2 := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2) (by positivity) h'
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at h2
    have hc : (Nat.clog 2 K : ℝ) ≤ ((Nat.clog 2 K).pred : ℝ) + 1 := by
      have : Nat.clog 2 K ≤ (Nat.clog 2 K).pred + 1 := by rw [Nat.pred_eq_sub_one]; omega
      exact_mod_cast this
    linarith

lemma logb_le_two_mul (y : ℝ) (hy : 0 < y) : Real.logb 2 y ≤ 2 * y := by
  have h1 := Real.log_le_sub_one_of_pos hy
  have h2 : (1 : ℝ) / 2 < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  rw [Real.logb, div_le_iff₀ (by linarith)]
  nlinarith

section

variable (N : ℕ) (δ : ℝ)

/-- `L₁ = log₂ (N/δ)`. -/
noncomputable def L1 : ℝ := Real.logb 2 (N / δ)

lemma logb_inv_ge (hδ : 0 < δ) (hδ' : δ < 1 / 2) : 1 ≤ Real.logb 2 (1 / δ) := by
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity), Real.rpow_one]
  rw [le_div_iff₀ hδ]; linarith

lemma L1_eq (hN : 1 ≤ N) (hδ : 0 < δ) : L1 N δ = Real.logb 2 N + Real.logb 2 (1 / δ) := by
  unfold L1
  rw [div_eq_mul_one_div, Real.logb_mul (by positivity) (by positivity)]

lemma logb_N_nonneg (hN : 1 ≤ N) : 0 ≤ Real.logb 2 N :=
  Real.logb_nonneg (by norm_num) (by exact_mod_cast hN)

lemma L1_ge (hN : 1 ≤ N) (hδ : 0 < δ) (hδ' : δ < 1 / 2) : 1 ≤ L1 N δ := by
  rw [L1_eq N δ hN hδ]
  have := logb_inv_ge δ hδ hδ'; have := logb_N_nonneg N hN; linarith

lemma clogN_le (hN : 1 ≤ N) (hδ : 0 < δ) (hδ' : δ < 1 / 2) : (Nat.clog 2 N : ℝ) + 1 ≤ 2 * L1 N δ := by
  have h1 := clog_le_logb N hN
  rw [L1_eq N δ hN hδ]
  have := logb_inv_ge δ hδ hδ'
  have := logb_N_nonneg N hN
  linarith

/-- Bernoulli: `(1 + δ/4)^⌈4/δ⌉ ≥ 2`. -/
lemma pow_j_ge (hδ : 0 < δ) : (2 : ℝ) ≤ (1 + δ / 4) ^ ⌈4 / δ⌉₊ := by
  have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ δ / 4 by linarith) ⌈4 / δ⌉₊
  have hj : (4 / δ : ℝ) ≤ ⌈4 / δ⌉₊ := Nat.le_ceil _
  have : (1 : ℝ) ≤ ⌈4 / δ⌉₊ * (δ / 4) := by
    rw [div_le_iff₀ hδ] at hj
    nlinarith
  linarith

/-- The global ladder is short: `KG ≤ ⌈4/δ⌉ · clog₂ ⌈16 N λ⌉`. -/
lemma KG_le (hN : 1 ≤ N) (hδ : 0 < δ) (hδ' : δ < 1 / 2) :
    KG N δ ≤ ⌈4 / δ⌉₊ * Nat.clog 2 ⌈16 * (N : ℝ) * lamOf N δ⌉₊ := by
  have hg := gCond_ex δ N hδ
  unfold KG; rw [dif_pos hg]
  apply Nat.find_min'
  set j := ⌈4 / δ⌉₊
  set t := Nat.clog 2 ⌈16 * (N : ℝ) * lamOf N δ⌉₊
  have hlam : 0 ≤ lamOf N δ := by unfold lamOf; positivity
  have h2t : 16 * (N : ℝ) * lamOf N δ ≤ (2 : ℝ) ^ t := by
    have h1 := Nat.le_ceil (16 * (N : ℝ) * lamOf N δ)
    have h3 := Nat.le_pow_clog (by norm_num : 1 < 2) ⌈16 * (N : ℝ) * lamOf N δ⌉₊
    have h2 : ((⌈16 * (N : ℝ) * lamOf N δ⌉₊ : ℕ) : ℝ) ≤ ((2 ^ t : ℕ) : ℝ) := Nat.cast_le.2 h3
    rw [Nat.cast_pow, Nat.cast_ofNat] at h2
    linarith
  have hjt : (2 : ℝ) ^ t ≤ (1 + δ / 4) ^ (j * t) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by norm_num) (pow_j_ge δ hδ) t
  unfold gCond
  have he : (1 : ℝ) / (1 + δ / 4) ≥ 1 / 2 := by
    rw [ge_iff_le, div_le_div_iff₀ (by norm_num) (by linarith)]; linarith
  have hpos : (0 : ℝ) ≤ (1 + δ / 4) ^ (j * t) := by positivity
  nlinarith

end

section

variable (N m : ℕ) (δ : ℝ)

/-- `E = (2^14/δ)^m`. -/
noncomputable def EE : ℝ := ((2 : ℝ) ^ 14 / δ) ^ m

lemma base_ge (hδ : 0 < δ) (hδ' : δ < 1 / 2) : (2 : ℝ) ≤ (2 : ℝ) ^ 14 / δ := by
  rw [le_div_iff₀ hδ]; norm_num; linarith

lemma EE_ge_base (hm : 1 ≤ m) (hδ : 0 < δ) (hδ' : δ < 1 / 2) : (2 : ℝ) ^ 14 / δ ≤ EE m δ := by
  unfold EE
  exact le_self_pow₀ (by have := base_ge δ hδ hδ'; linarith) (by omega)

lemma EE_ge (hm : 1 ≤ m) (hδ : 0 < δ) (hδ' : δ < 1 / 2) : 2 ≤ EE m δ :=
  (base_ge δ hδ hδ').trans (EE_ge_base m δ hm hδ hδ')

lemma inv_le_EE (hm : 1 ≤ m) (hδ : 0 < δ) (hδ' : δ < 1 / 2) : 1 / δ ≤ EE m δ := by
  refine le_trans ?_ (EE_ge_base m δ hm hδ hδ')
  rw [div_le_div_iff_of_pos_right hδ]; norm_num

lemma m_le_EE (hδ : 0 < δ) (hδ' : δ < 1 / 2) : (m : ℝ) ≤ EE m δ := by
  have h1 : (m : ℝ) ≤ 2 ^ m := by exact_mod_cast (Nat.lt_two_pow_self).le
  exact h1.trans (by unfold EE; exact pow_le_pow_left₀ (by norm_num) (base_ge δ hδ hδ') m)

lemma Gn_le (hm : 1 ≤ m) (hδ : 0 < δ) (hδ' : δ < 1 / 2) : (Gn m δ : ℝ) ≤ 2 * EE m δ ^ 2 := by
  unfold Gn
  have e : ((2 : ℝ) ^ 12 / (δ / 4)) ^ (2 * m) = EE m δ ^ 2 := by
    unfold EE; rw [← pow_mul, mul_comm m 2]; congr 1; field_simp; norm_num
  rw [e]
  have h1 := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ EE m δ ^ 2 by positivity)
  have h2 : (1 : ℝ) ≤ EE m δ ^ 2 := by have := EE_ge m δ hm hδ hδ'; nlinarith
  linarith

lemma MGG_le (hN : 1 ≤ N) (hδ : 0 < δ) (hδ' : δ < 1 / 2) : (MGG N δ : ℝ) ≤ 61 * L1 N δ / δ := by
  have hK := KG_le N δ hN hδ hδ'
  set j := ⌈4 / δ⌉₊
  set K' := ⌈16 * (N : ℝ) * lamOf N δ⌉₊
  have hL := L1_ge N δ hN hδ hδ'
  have hinv : (2 : ℝ) < 1 / δ := by rw [lt_div_iff₀ hδ]; linarith
  -- j ≤ 5/δ
  have hj : (j : ℝ) ≤ 5 / δ := by
    have := (Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 4 / δ by positivity)).le
    have e : (5 : ℝ) / δ = 4 / δ + 1 / δ := by ring
    rw [e]; linarith
  -- λ ≤ 16 N / δ²
  have hlam : lamOf N δ ≤ 16 * (N / δ) / δ := by
    unfold lamOf
    have h1 := clogN_le N δ hN hδ hδ'
    have h2 := logb_le_two_mul (N / δ) (by have : (0 : ℝ) < N := (by exact_mod_cast hN); positivity)
    unfold L1 at h1
    rw [div_le_div_iff_of_pos_right hδ]; linarith
  have hlam0 : 0 < lamOf N δ := by unfold lamOf; positivity
  have hN0 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hK1 : 1 ≤ K' := Nat.one_le_iff_ne_zero.2 (by
    intro h; rw [Nat.ceil_eq_zero] at h; nlinarith)
  -- t ≤ 12 L1
  have ht : (Nat.clog 2 K' : ℝ) ≤ 12 * L1 N δ := by
    have h1 := clog_le_logb K' hK1
    have hK'le : (K' : ℝ) ≤ 512 * (N / δ) ^ 2 := by
      have := (Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 16 * N * lamOf N δ by positivity)).le
      have h16 : 16 * (N : ℝ) * lamOf N δ ≤ 256 * (N / δ) ^ 2 := by
        calc 16 * (N : ℝ) * lamOf N δ ≤ 16 * N * (16 * (N / δ) / δ) := by gcongr
          _ = 256 * (N / δ) ^ 2 := by ring
      have hone : (1 : ℝ) ≤ 256 * (N / δ) ^ 2 := by
        have : (1 : ℝ) ≤ N / δ := by rw [le_div_iff₀ hδ]; linarith
        nlinarith
      linarith
    have h2 : Real.logb 2 K' ≤ Real.logb 2 (512 * (N / δ) ^ 2) :=
      Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hK1) hK'le
    have h3 : Real.logb 2 (512 * (N / δ) ^ 2) = 9 + 2 * L1 N δ := by
      unfold L1
      rw [Real.logb_mul (by norm_num) (by have : (0 : ℝ) < N := (by exact_mod_cast hN); positivity),
        Real.logb_pow, show (512 : ℝ) = 2 ^ (9 : ℕ) by norm_num, Real.logb_pow,
        Real.logb_self_eq_one (by norm_num)]
      push_cast; ring
    linarith
  have hKG : (KG N δ : ℝ) ≤ (j : ℝ) * (Nat.clog 2 K' : ℝ) := by exact_mod_cast hK
  have hpos : (0 : ℝ) ≤ Nat.clog 2 K' := by positivity
  have : (KG N δ : ℝ) ≤ 5 / δ * (12 * L1 N δ) :=
    hKG.trans (mul_le_mul hj ht hpos (by positivity))
  unfold MGG; push_cast
  have e : 61 * L1 N δ / δ = 5 / δ * (12 * L1 N δ) + L1 N δ / δ := by ring
  have h1 : (1 : ℝ) ≤ L1 N δ / δ := by
    rw [le_div_iff₀ hδ]; linarith
  linarith

end

section Final

variable {B : Blocks} (ch : ChildOK B) (N m : ℕ) (δ : ℝ)

lemma T0G_le_MGG : T0G N δ ≤ MGG N δ := by
  unfold T0G MGG
  have : Nat.clog 2 (KG N δ) ≤ KG N δ := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le
  omega

/-- The basic real facts, with `Y = L₁ E`. -/
abbrev Facts (N m : ℕ) (δ : ℝ) : Prop :=
  ((1 : ℝ) ≤ N) ∧
  (1 ≤ L1 N δ) ∧
  (2 ≤ L1 N δ * EE m δ) ∧
  ((m : ℝ) ≤ L1 N δ * EE m δ) ∧
  (EE m δ ≤ L1 N δ * EE m δ) ∧
  (L1 N δ ≤ L1 N δ * EE m δ) ∧
  ((MGG N δ : ℝ) ≤ 61 * (L1 N δ * EE m δ)) ∧
  ((T0G N δ : ℝ) ≤ 61 * (L1 N δ * EE m δ)) ∧
  (2 * (Gn m δ : ℝ) + 3 ≤ 5 * (L1 N δ * EE m δ) ^ 2) ∧
  ((Nat.clog 2 N : ℝ) + 1 ≤ 2 * (L1 N δ * EE m δ)) ∧
  ((bspB N m δ : ℝ) ≤ N * (5 * (L1 N δ * EE m δ) ^ 2))

section

theorem Facts.n1 {N m : ℕ} {δ : ℝ} (bu : Facts N m δ) :
    (1 : ℝ) ≤ N := bu.1

theorem Facts.l1 {N m : ℕ} {δ : ℝ} (bu : Facts N m δ) :
    1 ≤ L1 N δ := bu.2.1

theorem Facts.Y2 {N m : ℕ} {δ : ℝ} (bu : Facts N m δ) :
    2 ≤ L1 N δ * EE m δ := bu.2.2.1

theorem Facts.mY {N m : ℕ} {δ : ℝ} (bu : Facts N m δ) :
    (m : ℝ) ≤ L1 N δ * EE m δ := bu.2.2.2.1

theorem Facts.MG {N m : ℕ} {δ : ℝ} (bu : Facts N m δ) :
    (MGG N δ : ℝ) ≤ 61 * (L1 N δ * EE m δ) := bu.2.2.2.2.2.2.1

theorem Facts.T0 {N m : ℕ} {δ : ℝ} (bu : Facts N m δ) :
    (T0G N δ : ℝ) ≤ 61 * (L1 N δ * EE m δ) := bu.2.2.2.2.2.2.2.1

theorem Facts.G5 {N m : ℕ} {δ : ℝ} (bu : Facts N m δ) :
    2 * (Gn m δ : ℝ) + 3 ≤ 5 * (L1 N δ * EE m δ) ^ 2 := bu.2.2.2.2.2.2.2.2.1

theorem Facts.cl {N m : ℕ} {δ : ℝ} (bu : Facts N m δ) :
    (Nat.clog 2 N : ℝ) + 1 ≤ 2 * (L1 N δ * EE m δ) := bu.2.2.2.2.2.2.2.2.2.1

theorem Facts.bs {N m : ℕ} {δ : ℝ} (bu : Facts N m δ) :
    (bspB N m δ : ℝ) ≤ N * (5 * (L1 N δ * EE m δ) ^ 2) := bu.2.2.2.2.2.2.2.2.2.2

end

lemma facts (hN : 1 ≤ N) (hm : 1 ≤ m) (hδ : 0 < δ) (hδ' : δ < 1 / 2) : Facts N m δ := by
  have hL := L1_ge N δ hN hδ hδ'
  have hE := EE_ge m δ hm hδ hδ'
  have hEY : EE m δ ≤ L1 N δ * EE m δ := by nlinarith
  have hLY : L1 N δ ≤ L1 N δ * EE m δ := by nlinarith
  have hMG : (MGG N δ : ℝ) ≤ 61 * (L1 N δ * EE m δ) := by
    have h1 := MGG_le N δ hN hδ hδ'
    have h2 := inv_le_EE m δ hm hδ hδ'
    have e : 61 * L1 N δ / δ = 61 * L1 N δ * (1 / δ) := by ring
    rw [e] at h1
    nlinarith
  have hG : 2 * (Gn m δ : ℝ) + 3 ≤ 5 * (L1 N δ * EE m δ) ^ 2 := by
    have h1 := Gn_le m δ hm hδ hδ'
    have h2 : EE m δ ^ 2 ≤ (L1 N δ * EE m δ) ^ 2 := by gcongr
    nlinarith
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  refine ⟨hn1, hL, by nlinarith, (m_le_EE m δ hδ hδ').trans hEY, hEY, hLY, hMG, ?_, hG, ?_, ?_⟩
  · exact (by exact_mod_cast T0G_le_MGG N δ : (T0G N δ : ℝ) ≤ MGG N δ).trans hMG
  · have := clogN_le N δ hN hδ hδ'; linarith
  · have hb : (bspB N m δ : ℝ) ≤ N * (2 * Gn m δ + 3) := by exact_mod_cast bspB_le hδ hN
    exact hb.trans (by gcongr)

variable {N m δ}

lemma lkD_real (F : Facts N m δ) :
    (lkD ch N m δ : ℝ) ≤ 10 * Acon ch * N * (L1 N δ * EE m δ) ^ 3 := by
  set Y := L1 N δ * EE m δ
  have hA : ((ch.Cb : ℝ) * (m + 1) + ch.Cbal) ≤ 2 * Acon ch * Y := by
    unfold Acon; push_cast
    have := F.mY; have := F.Y2
    have h0 : (0 : ℝ) ≤ ch.Cb := by positivity
    have h1 : (0 : ℝ) ≤ ch.Cbal := by positivity
    have h2 : (0 : ℝ) ≤ ch.Cm := by positivity
    have h3 : (0 : ℝ) ≤ ch.Cc := by positivity
    nlinarith
  unfold lkD; push_cast
  calc ((ch.Cb : ℝ) * (m + 1) + ch.Cbal) * (bspB N m δ : ℝ)
      ≤ (2 * Acon ch * Y) * (N * (5 * Y ^ 2)) := by
        have := F.bs
        gcongr
        exact mul_nonneg (by positivity) (by linarith [F.Y2])
    _ = 10 * Acon ch * N * Y ^ 3 := by ring

end Final

section Final2

variable {B : Blocks} (ch : ChildOK B) {N m : ℕ} {δ : ℝ}

lemma Acon_ge : (1 : ℝ) ≤ Acon ch := by unfold Acon; push_cast; linarith [(Nat.cast_nonneg ch.Cm : (0:ℝ) ≤ _), (Nat.cast_nonneg ch.Cc : (0:ℝ) ≤ _), (Nat.cast_nonneg ch.Cb : (0:ℝ) ≤ _), (Nat.cast_nonneg ch.Cbal : (0:ℝ) ≤ _)]

lemma consts_le : (ch.Cm : ℝ) ≤ Acon ch ∧ (ch.Cc : ℝ) ≤ Acon ch ∧ (ch.Cb : ℝ) ≤ Acon ch ∧
    (ch.Cbal : ℝ) ≤ Acon ch ∧ (ch.Cm : ℝ) + ch.Cc ≤ Acon ch := by
  unfold Acon; push_cast
  have h1 : (0 : ℝ) ≤ ch.Cm := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ ch.Cc := Nat.cast_nonneg _
  have h3 : (0 : ℝ) ≤ ch.Cb := Nat.cast_nonneg _
  have h4 : (0 : ℝ) ≤ ch.Cbal := Nat.cast_nonneg _
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

lemma KHc_real (F : Facts N m δ) :
    (KHc ch N m δ : ℝ) ≤ 751 * Acon ch * (L1 N δ * EE m δ) ^ 3 := by
  set Y := L1 N δ * EE m δ
  have hA := Acon_ge ch
  have hY := F.Y2
  have hb : (ch.Cbal : ℝ) ≤ Acon ch := (consts_le ch).2.2.2.1
  unfold KHc; push_cast
  have h1 : (MGG N δ : ℝ) * (ch.Cbal * (2 * Gn m δ + 3)) ≤ (61 * Y) * (Acon ch * (5 * Y ^ 2)) := by
    have := F.MG; have := F.G5; gcongr
  have hY3 : Y ≤ Y ^ 3 := by nlinarith
  have hAY : Y ^ 3 ≤ Acon ch * Y ^ 3 := by nlinarith
  have hAY1 : (1 : ℝ) ≤ Acon ch * Y ^ 3 := by nlinarith
  have := F.MG
  nlinarith

lemma KRc_real (F : Facts N m δ) :
    (KRc ch N m δ : ℝ) ≤ 427 * Acon ch * (L1 N δ * EE m δ) ^ 4 := by
  set Y := L1 N δ * EE m δ
  have hA := Acon_ge ch
  have hY := F.Y2
  have hb : (ch.Cbal : ℝ) ≤ Acon ch := (consts_le ch).2.2.2.1
  have hm0 : (0 : ℝ) ≤ m := by positivity
  unfold KRc; push_cast
  have h1 : (2 * (m : ℝ) + ch.Cbal * (2 * Gn m δ + 3) * m) ≤ 2 * Y + Acon ch * (5 * Y ^ 2) * Y := by
    have := F.mY; have := F.G5; gcongr
  have h2 : 2 * Y + Acon ch * (5 * Y ^ 2) * Y ≤ 7 * Acon ch * Y ^ 3 := by
    have hY3 : Y ≤ Y ^ 3 := by nlinarith
    have hAY : Y ^ 3 ≤ Acon ch * Y ^ 3 := by nlinarith
    have e : Acon ch * (5 * Y ^ 2) * Y = 5 * (Acon ch * Y ^ 3) := by ring
    linarith
  have h3 : (MGG N δ : ℝ) * (2 * (m : ℝ) + ch.Cbal * (2 * Gn m δ + 3) * m) ≤ (61 * Y) * (7 * Acon ch * Y ^ 3) := by
    have := F.MG
    have h0 : (0 : ℝ) ≤ 2 * (m : ℝ) + ch.Cbal * (2 * Gn m δ + 3) * m := by positivity
    calc _ ≤ (61 * Y) * (2 * (m : ℝ) + ch.Cbal * (2 * Gn m δ + 3) * m) := by gcongr
      _ ≤ _ := by gcongr; linarith
  nlinarith

/-- **Cells.** The cell bound of `pre_run` for the concrete budgets. -/
lemma cells_real (F : Facts N m δ) (tp : ℕ) (htp : (tp : ℝ) ≤ 8 * N * (L1 N δ * EE m δ)) :
    (((v0G N δ + 18 + Dn (WbIc ch N m δ) N + (tp : ℤ) * KHc ch N m δ + (tp : ℤ) * KRc ch N m δ +
      WbRc ch N m δ : ℤ)) : ℝ) ≤ 10000 * Acon ch * N * (L1 N δ * EE m δ) ^ 5 := by
  set Y := L1 N δ * EE m δ
  have hA := Acon_ge ch
  have hY := F.Y2
  have hn := F.n1
  have hD := lkD_real ch F
  have hH := KHc_real ch F
  have hR := KRc_real ch F
  have hcm : (ch.Cm : ℝ) + ch.Cc ≤ Acon ch := (consts_le ch).2.2.2.2
  have hcm0 : (0 : ℝ) ≤ ch.Cm := by positivity
  have hcc0 : (0 : ℝ) ≤ ch.Cc := by positivity
  have hv : ((v0G N δ : ℤ) : ℝ) = 5 + 2 * N + T0G N δ := by
    unfold v0G Hbase; push_cast; ring
  have hT := F.T0
  have hcl := F.cl
  set W := Acon ch * N * Y ^ 5 with hW
  have hY1 : (1 : ℝ) ≤ Y := by linarith
  have p3 : (1 : ℝ) ≤ Y ^ 3 := one_le_pow₀ hY1
  have p34 : Y ^ 3 ≤ Y ^ 4 := pow_le_pow_right₀ hY1 (by norm_num)
  have p45 : Y ^ 4 ≤ Y ^ 5 := pow_le_pow_right₀ hY1 (by norm_num)
  have pY5 : Y ≤ Y ^ 5 := le_self_pow₀ hY1 (by norm_num)
  have hAn : (1 : ℝ) ≤ Acon ch * N := by nlinarith
  have w1 : Acon ch * N * Y ^ 3 ≤ W := by rw [hW]; gcongr; linarith
  have w2 : Acon ch * N * Y ^ 4 ≤ W := by rw [hW]; gcongr
  have w0 : Acon ch * N ≤ W := by
    rw [hW]; nlinarith [one_le_pow₀ hY1 (n := 5)]
  have wY : Y ≤ W := by
    rw [hW]; nlinarith [mul_le_mul_of_nonneg_right hAn (show (0:ℝ) ≤ Y ^ 5 by positivity)]
  have wn : (N : ℝ) ≤ W := by nlinarith
  have w1' : (1 : ℝ) ≤ W := by linarith
  have hDn : ((Dn (WbIc ch N m δ) N : ℕ) : ℝ) ≤ 2 * N + 20 * Y + 2 * Acon ch * N + lkD ch N m δ + 20 := by
    unfold Dn WbIc; push_cast
    have : (ch.Cm : ℝ) * (N + 1) + ch.Cc * (N + 1) ≤ 2 * Acon ch * N := by nlinarith
    linarith
  have hTH : (tp : ℝ) * KHc ch N m δ ≤ (8 * N * Y) * (751 * Acon ch * Y ^ 3) := by
    gcongr
  have hTR : (tp : ℝ) * KRc ch N m δ ≤ (8 * N * Y) * (427 * Acon ch * Y ^ 4) := by
    gcongr
  have e1 : (8 * N * Y) * (751 * Acon ch * Y ^ 3) = 6008 * (Acon ch * N * Y ^ 4) := by ring
  have e2 : (8 * N * Y) * (427 * Acon ch * Y ^ 4) = 3416 * W := by rw [hW]; ring
  push_cast
  rw [hv]
  unfold WbRc
  nlinarith

end Final2

section Final3

variable {B : Blocks} (ch : ChildOK B) {N m : ℕ} {δ : ℝ}

lemma headW_le (n M : ℕ) : headW ch n m M ≤ 51 + ch.Cm * (n + 1) ^ 5 * (m + 1) + 9 * M := by
  unfold headW
  have : Nat.clog 2 (M - 1) ≤ M - 1 := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le
  omega

lemma dom (P Y : ℝ) (hP : 1 ≤ P) (hY : 1 ≤ Y) (a b k : ℕ) (ha : a ≤ k) (hb : b ≤ k) :
    P ^ a * Y ^ b ≤ (P * Y) ^ k := by
  rw [mul_pow]
  exact mul_le_mul (pow_le_pow_right₀ hP ha) (pow_le_pow_right₀ hY hb) (by positivity) (by positivity)

set_option maxHeartbeats 1000000 in
/-- **Work.** The work bound of `pre_run` for the concrete budgets. -/
lemma work_real (F : Facts N m δ) (hm : 1 ≤ m) (tp : ℕ) (htp : (tp : ℝ) ≤ 8 * N * (L1 N δ * EE m δ)) :
    ((79 + 4 * Nat.clog 2 N + 11 * N + 5 * KG N δ + 10 * T0G N δ + tp * KWc ch N m δ : ℕ) : ℝ) ≤
      100000 * Acon ch * (((N : ℝ) + m) * (L1 N δ * EE m δ)) ^ 7 := by
  set Y := L1 N δ * EE m δ
  set P : ℝ := (N : ℝ) + m with hPdef
  set Q := P * Y with hQ
  have hA := Acon_ge ch
  have hA0 : (0 : ℝ) ≤ Acon ch := by linarith
  have hY := F.Y2
  have hn := F.n1
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hY1 : (1 : ℝ) ≤ Y := by linarith
  have hP1 : (1 : ℝ) ≤ P := by linarith
  have hP2 : (2 : ℝ) ≤ P := by linarith
  have hQ1 : (1 : ℝ) ≤ Q := one_le_mul_of_one_le_of_one_le hP1 hY1
  obtain ⟨cm, cc, cb, cbal, _⟩ := consts_le ch
  have d := dom P Y hP1 hY1
  have AQ : ∀ k, (1 : ℝ) ≤ Q ^ k ∧ Q ^ k ≤ Acon ch * Q ^ k := fun k =>
    ⟨one_le_pow₀ hQ1, le_mul_of_one_le_left (by positivity) hA⟩
  have hMG := F.MG
  have hKG : (KG N δ : ℝ) ≤ 61 * Y := by
    have : (KG N δ : ℝ) ≤ MGG N δ := by unfold MGG; push_cast; linarith
    linarith
  have hYQ : Y ≤ Q := le_mul_of_one_le_left (by linarith) hP1
  have hNQ : (N : ℝ) ≤ Q := by
    have : (N : ℝ) ≤ P := by linarith
    exact this.trans (le_mul_of_one_le_right (by linarith) hY1)
  -- head
  have hhead : (headW ch N m (MGG N δ) : ℝ) ≤ 601 * Acon ch * Q ^ 6 := by
    have h' : (headW ch N m (MGG N δ) : ℝ) ≤ 51 + ch.Cm * ((N : ℝ) + 1) ^ 5 * (m + 1) + 9 * MGG N δ := by
      exact_mod_cast headW_le ch N (MGG N δ) (m := m)
    have h1 : (ch.Cm : ℝ) * ((N : ℝ) + 1) ^ 5 * (m + 1) ≤ Acon ch * P ^ 5 * P := by
      gcongr <;> linarith
    have h2 : Acon ch * P ^ 5 * P ≤ Acon ch * Q ^ 6 := by
      have := d 6 0 6 le_rfl (by norm_num); simp only [pow_zero, mul_one] at this
      rw [mul_assoc, ← pow_succ]; exact mul_le_mul_of_nonneg_left this hA0
    have h3 : Y ≤ Q ^ 6 := by have := d 0 1 6 (by norm_num) (by norm_num); simpa using this
    obtain ⟨h4, h5⟩ := AQ 6
    linarith
  -- lookup iteration
  have hbs : (bspB N m δ : ℝ) ≤ 5 * P * Y ^ 2 := by
    have := F.bs
    have : (N : ℝ) * (5 * Y ^ 2) ≤ P * (5 * Y ^ 2) := by gcongr; linarith
    linarith
  have hbs2 : (bspB N m δ : ℝ) ^ 2 ≤ 25 * (P ^ 2 * Y ^ 4) := by
    have h0 : (0 : ℝ) ≤ bspB N m δ := by positivity
    calc (bspB N m δ : ℝ) ^ 2 ≤ (5 * P * Y ^ 2) ^ 2 := by gcongr
      _ = 25 * (P ^ 2 * Y ^ 4) := by ring
  have hlk : (lkW ch N m δ : ℝ) ≤ 144 * Acon ch * Q ^ 5 := by
    unfold lkW; push_cast
    obtain ⟨q5, qa⟩ := AQ 5
    have pq2 : P ^ 2 ≤ Q ^ 5 := by have := d 2 0 5 (by norm_num) (by norm_num); simpa using this
    have pq1 : P ≤ Q ^ 5 := by have := d 1 0 5 (by norm_num) (by norm_num); simpa using this
    have t1 : ((15 : ℝ) * N + 30) * m ≤ 45 * Q ^ 5 := by
      calc ((15 : ℝ) * N + 30) * m ≤ (30 * P) * P := by gcongr <;> linarith
        _ = 30 * P ^ 2 := by ring
        _ ≤ 45 * Q ^ 5 := by linarith
    have t2 : (11 : ℝ) * m ≤ 11 * Q ^ 5 := by linarith
    have t3 : (ch.Cb : ℝ) * (bspB N m δ : ℝ) ^ 2 * ((N : ℝ) + 1) * ((m : ℝ) + 1) ^ 2 ≤
        Acon ch * (25 * (P ^ 2 * Y ^ 4)) * P * P ^ 2 := by gcongr <;> linarith
    have t3' : Acon ch * (25 * (P ^ 2 * Y ^ 4)) * P * P ^ 2 ≤ 25 * (Acon ch * Q ^ 5) := by
      have := d 5 4 5 (by norm_num) (by norm_num)
      have e : Acon ch * (25 * (P ^ 2 * Y ^ 4)) * P * P ^ 2 = 25 * (Acon ch * (P ^ 5 * Y ^ 4)) := by ring
      rw [e]; gcongr
    have t4 : (ch.Cbal : ℝ) * (bspB N m δ : ℝ) ^ 2 * ((m : ℝ) + 1) ≤ Acon ch * (25 * (P ^ 2 * Y ^ 4)) * P := by
      gcongr; linarith
    have t4' : Acon ch * (25 * (P ^ 2 * Y ^ 4)) * P ≤ 25 * (Acon ch * Q ^ 5) := by
      have := d 3 4 5 (by norm_num) (by norm_num)
      have e : Acon ch * (25 * (P ^ 2 * Y ^ 4)) * P = 25 * (Acon ch * (P ^ 3 * Y ^ 4)) := by ring
      rw [e]; gcongr
    linarith
  have hMlk : (MGG N δ : ℝ) * lkW ch N m δ ≤ 8784 * Acon ch * Q ^ 6 := by
    have h0 : (0 : ℝ) ≤ lkW ch N m δ := by positivity
    have h1 : (MGG N δ : ℝ) * lkW ch N m δ ≤ (61 * Y) * (144 * Acon ch * Q ^ 5) := by gcongr
    have h2 : Y * Q ^ 5 ≤ Q ^ 6 := by
      calc Y * Q ^ 5 ≤ Q * Q ^ 5 := by gcongr
        _ = Q ^ 6 := by ring
    have h3 := mul_le_mul_of_nonneg_left h2 hA0
    have e : (61 * Y) * (144 * Acon ch * Q ^ 5) = 8784 * (Acon ch * (Y * Q ^ 5)) := by ring
    linarith
  have hmid : (midW ch N m : ℝ) ≤ 32 * Acon ch * Q ^ 6 := by
    unfold midW; push_cast
    have h1 : (ch.Cc : ℝ) * ((N : ℝ) + 1) ^ 3 * ((m : ℝ) + 1) ≤ Acon ch * P ^ 3 * P := by
      gcongr <;> linarith
    have h2 : P ^ 3 * P ≤ Q ^ 6 := by
      have := d 4 0 6 (by norm_num) (by norm_num); rw [← pow_succ]; simpa using this
    have h3 : P ≤ Q ^ 6 := by have := d 1 0 6 (by norm_num) (by norm_num); simpa using this
    obtain ⟨h4, h5⟩ := AQ 6
    have h6 : Acon ch * P ^ 3 * P ≤ Acon ch * Q ^ 6 := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h2 hA0
    have hN : (N : ℝ) ≤ P := by linarith
    linarith
  have hkid : ((N * kidW N : ℕ) : ℝ) ≤ 103 * Acon ch * Q ^ 6 := by
    unfold kidW; push_cast
    have h1 : P ^ 2 ≤ Q ^ 6 := by have := d 2 0 6 (by norm_num) (by norm_num); simpa using this
    have h3 : P ≤ Q ^ 6 := by have := d 1 0 6 (by norm_num) (by norm_num); simpa using this
    obtain ⟨h4, h5⟩ := AQ 6
    have hN : (N : ℝ) ≤ P := by linarith
    have hN0 : (0 : ℝ) ≤ N := by positivity
    have e : (N : ℝ) * (23 * N + 80) ≤ 23 * P ^ 2 + 80 * P := by
      have : (N : ℝ) * N ≤ P * P := by gcongr
      nlinarith only [this, hN, hN0]
    linarith
  have hKW : (KWc ch N m δ : ℝ) ≤ 9600 * Acon ch * Q ^ 6 := by
    unfold KWc; push_cast
    obtain ⟨h4, h5⟩ := AQ 6
    push_cast at hkid
    linarith
  have hTK : (tp : ℝ) * KWc ch N m δ ≤ (8 * Q) * (9600 * Acon ch * Q ^ 6) := by
    have : (tp : ℝ) ≤ 8 * Q := by
      have : (N : ℝ) * Y ≤ P * Y := by gcongr; linarith
      linarith
    gcongr
  have hT := F.T0
  have hcl := F.cl
  have q7 : Q ≤ Q ^ 7 := le_self_pow₀ hQ1 (by norm_num)
  obtain ⟨q71, q7a⟩ := AQ 7
  have e : (8 * Q) * (9600 * Acon ch * Q ^ 6) = 76800 * (Acon ch * Q ^ 7) := by ring
  push_cast
  linarith

end Final3

end DetANN.HPIM.PP

-- ===== PP_Bounds =====
namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth DetANN DetANN.HPIM Classical

lemma log_eq_L1 (N : ℕ) (δ : ℝ) : Real.log (N / δ) = L1 N δ * Real.log 2 := by
  unfold L1 Real.logb
  rw [div_mul_cancel₀ _ (by positivity)]

lemma rpow_eq_EE (m : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ((2 : ℝ) ^ 14 / δ) ^ (((8 : ℕ) : ℝ) * m) = EE m δ ^ 8 := by
  unfold EE
  rw [show (((8 : ℕ) : ℝ) * m) = ((8 * m : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast, ← pow_mul,
    mul_comm 8 m]

lemma L1_pow_le (N : ℕ) (δ : ℝ) (hL : 1 ≤ L1 N δ) :
    L1 N δ ^ 8 ≤ 256 * Real.log (N / δ) ^ 8 := by
  rw [log_eq_L1, mul_pow]
  have h2 : (1 : ℝ) / 2 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have h3 : (1 : ℝ) / 256 ≤ Real.log 2 ^ 8 := by
    calc (1 : ℝ) / 256 = (1 / 2) ^ 8 := by norm_num
      _ ≤ Real.log 2 ^ 8 := by gcongr
  have h4 : (0 : ℝ) ≤ L1 N δ ^ 8 := by positivity
  nlinarith

set_option maxHeartbeats 1000000 in
/-- **The arithmetic of the preprocessing bounds.** With `tp` points over the tree, the work and
cell budgets of the driver are within the bounds of `hpim_preprocessing`. -/
theorem pre_bounds {B : Blocks} (ch : ChildOK B) {m N : ℕ} (hm : 1 ≤ m) (hN : 1 ≤ N) (δ : ℝ)
    (hδ : 0 < δ) (hδ' : δ < 1 / 2) (tp : ℕ) (htp0 : tp ≤ 4 * N * (Nat.clog 2 N + 1)) :
    ((79 + 4 * Nat.clog 2 N + 11 * N + 5 * KG N δ + 10 * T0G N δ + tp * KWc ch N m δ : ℕ) : ℝ) ≤
        ((256 * 100000 * Acon ch : ℕ) : ℝ) * ((N : ℝ) + m) ^ 8 *
          ((2 : ℝ) ^ 14 / δ) ^ (((8 : ℕ) : ℝ) * m) * Real.log (N / δ) ^ 8 ∧
      (((v0G N δ + 18 + Dn (WbIc ch N m δ) N + (tp : ℤ) * KHc ch N m δ + (tp : ℤ) * KRc ch N m δ +
          WbRc ch N m δ : ℤ)) : ℝ) ≤
        ((256 * 100000 * Acon ch : ℕ) : ℝ) * N *
          ((2 : ℝ) ^ 14 / δ) ^ (((8 : ℕ) : ℝ) * m) * Real.log (N / δ) ^ 8 := by
  have F := facts N m δ hN hm hδ hδ'
  have htp : (tp : ℝ) ≤ 8 * N * (L1 N δ * EE m δ) := by
    have h' : (tp : ℝ) ≤ 4 * N * ((Nat.clog 2 N : ℝ) + 1) := by exact_mod_cast htp0
    have := F.cl
    have : (4 : ℝ) * N * ((Nat.clog 2 N : ℝ) + 1) ≤ 4 * N * (2 * (L1 N δ * EE m δ)) := by
      gcongr
    linarith
  rw [rpow_eq_EE m δ hδ]
  have hL8 := L1_pow_le N δ F.l1
  have hA := Acon_ge ch
  have hE : (2 : ℝ) ≤ EE m δ := EE_ge m δ hm hδ hδ'
  have hL := F.l1
  have hY1 : (1 : ℝ) ≤ L1 N δ * EE m δ := by linarith [F.Y2]
  constructor
  · -- work
    have hw' := work_real ch F hm tp htp
    set P : ℝ := (N : ℝ) + m
    have hP1 : (1 : ℝ) ≤ P := by
      have := F.n1
      have : (0 : ℝ) ≤ m := by positivity
      linarith
    have hQ1 : (1 : ℝ) ≤ P * (L1 N δ * EE m δ) := one_le_mul_of_one_le_of_one_le hP1 hY1
    have h78 : (P * (L1 N δ * EE m δ)) ^ 7 ≤ (P * (L1 N δ * EE m δ)) ^ 8 :=
      pow_le_pow_right₀ hQ1 (by norm_num)
    have e : (P * (L1 N δ * EE m δ)) ^ 8 = P ^ 8 * EE m δ ^ 8 * L1 N δ ^ 8 := by ring
    have hPE : (0 : ℝ) ≤ P ^ 8 * EE m δ ^ 8 := by positivity
    have h9 : P ^ 8 * EE m δ ^ 8 * L1 N δ ^ 8 ≤ P ^ 8 * EE m δ ^ 8 * (256 * Real.log (N / δ) ^ 8) :=
      mul_le_mul_of_nonneg_left hL8 hPE
    have hA0 : (0 : ℝ) ≤ Acon ch := by linarith
    have h10 := mul_le_mul_of_nonneg_left (h78.trans (e ▸ h9)) (show (0 : ℝ) ≤ 100000 * Acon ch by positivity)
    refine hw'.trans ?_
    push_cast
    calc 100000 * Acon ch * (P * (L1 N δ * EE m δ)) ^ 7
        ≤ 100000 * Acon ch * (P ^ 8 * EE m δ ^ 8 * (256 * Real.log (N / δ) ^ 8)) := h10
      _ = 25600000 * (Acon ch : ℝ) * P ^ 8 * EE m δ ^ 8 * Real.log (N / δ) ^ 8 := by ring
  · -- cells
    have hc' := cells_real ch F tp htp
    have h58 : (L1 N δ * EE m δ) ^ 5 ≤ (L1 N δ * EE m δ) ^ 8 := pow_le_pow_right₀ hY1 (by norm_num)
    have e : (L1 N δ * EE m δ) ^ 8 = EE m δ ^ 8 * L1 N δ ^ 8 := by ring
    have hE0 : (0 : ℝ) ≤ EE m δ ^ 8 := by positivity
    have h9 : EE m δ ^ 8 * L1 N δ ^ 8 ≤ EE m δ ^ 8 * (256 * Real.log (N / δ) ^ 8) :=
      mul_le_mul_of_nonneg_left hL8 hE0
    have hA0 : (0 : ℝ) ≤ Acon ch := by linarith
    have hN0 : (0 : ℝ) ≤ N := by positivity
    have h10 := mul_le_mul_of_nonneg_left (h58.trans (e ▸ h9))
      (show (0 : ℝ) ≤ 10000 * Acon ch * N by positivity)
    refine hc'.trans ?_
    push_cast
    calc 10000 * Acon ch * N * (L1 N δ * EE m δ) ^ 5
        ≤ 10000 * Acon ch * N * (EE m δ ^ 8 * (256 * Real.log (N / δ) ^ 8)) := h10
      _ ≤ 25600000 * (Acon ch : ℝ) * N * EE m δ ^ 8 * Real.log (N / δ) ^ 8 := by
        have : (0 : ℝ) ≤ (Acon ch : ℝ) * N * EE m δ ^ 8 * Real.log (N / δ) ^ 8 := by positivity
        nlinarith

end DetANN.HPIM.PP

theorem solution : type_of% @DetANN.HPIM.PP.pre_bounds := @DetANN.HPIM.PP.pre_bounds
