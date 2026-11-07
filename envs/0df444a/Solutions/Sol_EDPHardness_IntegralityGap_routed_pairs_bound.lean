-- Prove2me | solution 1 for EDPHardness.IntegralityGap.routed_pairs_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T10:22:42.665889+00:00
-- url     : https://prove2.me/submissions/355c7819-abfc-4b09-891c-b8b3b049728b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_EDPHardness_IntegralityGap_FlowRelaxation
import Definitions.Def_EDPHardness_IntegralityGap_GapInstance
import Theorems.Thm_EDPHardness_IntegralityGap_canonical_paths_bound
import Theorems.Thm_EDPHardness_IntegralityGap_long_paths_bound
import Theorems.Thm_EDPHardness_IntegralityGap_short_paths_bound

namespace EDPParamsAux

open EDPHardness.IntegralityGap Real

lemma logb_le_quarter (x : ℝ) (hx : 0 ≤ x) : logb 2 x ≤ 6 * x ^ ((1 : ℝ) / 4) := by
  have h1 := Real.log_le_rpow_div hx (ε := 1 / 4) (by norm_num)
  have h2 := Real.log_two_gt_d9
  have hp : 0 ≤ x ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hx _
  unfold logb
  rw [div_le_iff₀ (by linarith)]
  have : x ^ ((1 : ℝ) / 4) / (1 / 4) = 4 * x ^ ((1 : ℝ) / 4) := by ring
  rw [this] at h1
  nlinarith

lemma quarter_pow (x : ℝ) (hx : 0 ≤ x) : (x ^ ((1 : ℝ) / 4)) ^ 4 = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num

lemma quarter_ge (x : ℝ) (hx : 256 ≤ x) : 4 ≤ x ^ ((1 : ℝ) / 4) := by
  have h := quarter_pow x (by linarith)
  have hp : 0 ≤ x ^ ((1 : ℝ) / 4) := Real.rpow_nonneg (by linarith) _
  by_contra hlt
  push_neg at hlt
  have : (x ^ ((1 : ℝ) / 4)) ^ 4 < 4 ^ 4 := by
    apply pow_lt_pow_left₀ hlt hp (by norm_num)
  rw [h] at this
  norm_num at this
  linarith

lemma two_mul_le_two_pow (c : ℕ) : 2 * c ≤ 2 ^ c := by
  induction c with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp
    · omega

lemma aux64 (s : ℝ) (h : 4 ≤ s) : 64 * s ≤ s ^ 4 := by nlinarith [sq_nonneg s, sq_nonneg (s - 4)]

lemma aux42 (s : ℝ) (h : 4 ≤ s) : 1 + 42 * s ≤ 0.9 * s ^ 4 := by
  have := aux64 s h; linarith

lemma auxsq (x : ℝ) (h : 256 ≤ x) : 1 ≤ 150 * x ^ 2 := by nlinarith

lemma aux_mul2 (a b : ℝ) (ha : 2 ≤ a) (hb : 2 ≤ b) : 4 ≤ a * b := by nlinarith

set_option maxHeartbeats 1000000 in
/-- Parameter estimates of §2.4 for large `n`. -/
theorem params :
    ∃ α : ℝ, 0 < α ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ c : ℕ, 2 ≤ c →
      (c : ℝ) ≤ α * Real.logb 2 (Real.logb 2 n) / Real.logb 2 (Real.logb 2 (Real.logb 2 n)) →
      2 ≤ beta1 n c ∧ 1 ≤ beta2 n c ∧ 10 * beta2 n c * c ≤ (gParam n c : ℝ) ∧
      2 * (gParam n c : ℝ) * c * (6 * beta2 n c * (c : ℝ) ^ 2) ^ (2 * gParam n c + 2)
        ≤ (n : ℝ) / beta1 n c := by
  refine ⟨1 / 6, by norm_num, ⌈(2 : ℝ) ^ ((2 : ℝ) ^ (256 : ℝ))⌉₊, ?_⟩
  intro n hn c hc hcα
  -- basic logarithms
  set L1 := logb 2 (n : ℝ) with hL1
  set L2 := logb 2 L1 with hL2
  set L3 := logb 2 L2 with hL3
  have hnR : (2 : ℝ) ^ ((2 : ℝ) ^ (256 : ℝ)) ≤ n := Nat.ceil_le.1 hn
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) hnR
  have hL1big : (2 : ℝ) ^ (256 : ℝ) ≤ L1 := by
    have : logb 2 ((2 : ℝ) ^ ((2 : ℝ) ^ (256 : ℝ))) ≤ L1 :=
      (Real.logb_le_logb (by norm_num) (by positivity) hnpos).2 hnR
    rwa [Real.logb_rpow (by norm_num) (by norm_num)] at this
  have hL1pos : 0 < L1 := lt_of_lt_of_le (by positivity) hL1big
  have hL2big : 256 ≤ L2 := by
    have : logb 2 ((2 : ℝ) ^ (256 : ℝ)) ≤ L2 :=
      (Real.logb_le_logb (by norm_num) (by positivity) hL1pos).2 hL1big
    rwa [Real.logb_rpow (by norm_num) (by norm_num)] at this
  have hL1_256 : 256 ≤ L1 := by
    refine le_trans ?_ hL1big
    have : (2 : ℝ) ^ (8 : ℝ) ≤ (2 : ℝ) ^ (256 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    refine le_trans (le_of_eq ?_) this
    rw [show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have hL2pos : 0 < L2 := by linarith
  have hL3one : 1 ≤ L3 := by
    rw [hL3, Real.le_logb_iff_rpow_le (by norm_num) hL2pos]; norm_num; linarith
  have hL1eq : (2 : ℝ) ^ L2 = L1 := Real.rpow_logb (by norm_num) (by norm_num) hL1pos
  have hneq : (2 : ℝ) ^ L1 = n := Real.rpow_logb (by norm_num) (by norm_num) hnpos
  have hlogL1 : Real.log L1 = L2 * Real.log 2 := by
    rw [hL2, Real.logb, div_mul_cancel₀ _ (Real.log_pos (by norm_num : (1:ℝ) < 2)).ne']
  have hL3le := logb_le_quarter L2 hL2pos.le
  have hL2le := logb_le_quarter L1 hL1pos.le
  set t := L2 ^ ((1 : ℝ) / 4) with ht
  set s := L1 ^ ((1 : ℝ) / 4) with hs
  have ht4 : t ^ 4 = L2 := quarter_pow L2 hL2pos.le
  have hs4 : s ^ 4 = L1 := quarter_pow L1 hL1pos.le
  have ht_ge : 4 ≤ t := quarter_ge L2 hL2big
  have hs_ge : 4 ≤ s := quarter_ge L1 hL1_256
  -- c ≤ L2 / 6
  have hcR : (2 : ℝ) ≤ c := by exact_mod_cast hc
  have hcpos : (0 : ℝ) < c := by linarith
  have hcL2 : (c : ℝ) ≤ L2 / 6 := by
    refine hcα.trans ?_
    rw [div_le_iff₀ (by linarith)]
    have := mul_le_mul_of_nonneg_left hL3one (by positivity : (0:ℝ) ≤ L2 / 6)
    linarith
  -- X
  set X := L1 / (150 * L2 ^ 2) with hX
  have hXpos : 0 < X := by positivity
  have hlog150 : logb 2 (150 : ℝ) ≤ 8 := by
    have : logb 2 (150 : ℝ) ≤ logb 2 ((2 : ℝ) ^ (8 : ℕ)) :=
      (Real.logb_le_logb (by norm_num) (by norm_num) (by norm_num)).2 (by norm_num)
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at this
    simpa using this
  have hlogX : logb 2 X = L2 - logb 2 150 - 2 * L3 := by
    rw [hX, Real.logb_div hL1pos.ne' (by positivity), Real.logb_mul (by norm_num) (by positivity),
      Real.logb_pow]
    push_cast; ring
  have hlogX_ge : L2 / 2 ≤ logb 2 X := by
    rw [hlogX]
    have ht3 : (4 : ℝ) ^ 3 ≤ t ^ 3 := pow_le_pow_left₀ (by norm_num) ht_ge 3
    have ht4' : t ^ 4 = t ^ 3 * t := by ring
    have h64 : 64 * t ≤ t ^ 3 * t := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    linarith
  -- β₁
  have hb1def : beta1 n c = (1 / 4) * X ^ ((1 : ℝ) / c) := rfl
  set Z := X ^ ((1 : ℝ) / c) with hZ
  have hZpos : 0 < Z := Real.rpow_pos_of_pos hXpos _
  have hZ8 : 8 ≤ Z := by
    have h3 : (3 : ℝ) ≤ logb 2 Z := by
      rw [hZ, Real.logb_rpow_eq_mul_logb_of_pos hXpos]
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hcpos]
      linarith
    rw [Real.le_logb_iff_rpow_le (by norm_num) hZpos] at h3
    norm_num at h3
    exact h3
  have hXge1 : 1 ≤ X := by
    by_contra h
    push_neg at h
    have : Z ≤ 1 := Real.rpow_le_one hXpos.le h.le (by positivity)
    linarith
  have hb1 : 2 ≤ beta1 n c := by rw [hb1def]; linarith
  have hb1pos : 0 < beta1 n c := by linarith
  have hZc : Z ^ c = X := by
    rw [hZ, ← Real.rpow_natCast, ← Real.rpow_mul hXpos.le]
    rw [one_div, inv_mul_cancel₀ hcpos.ne', Real.rpow_one]
  have hXL1 : X ≤ L1 := by
    rw [hX, div_le_iff₀ (by positivity)]
    have h1 : (1 : ℝ) ≤ 150 * L2 ^ 2 := auxsq L2 hL2big
    exact le_mul_of_one_le_right hL1pos.le h1
  have hZX : Z ≤ X := by
    have : X ^ ((1 : ℝ) / c) ≤ X ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hXge1 (by rw [div_le_one hcpos]; linarith)
    rw [Real.rpow_one] at this; exact this
  -- logs
  have hlogb1 : Real.log (beta1 n c) ≤ Real.log X / c := by
    have h1 : Real.log (beta1 n c) ≤ Real.log Z :=
      Real.log_le_log hb1pos (by rw [hb1def]; linarith)
    rw [hZ, Real.log_rpow hXpos] at h1
    rw [div_eq_mul_one_div, mul_comm]; exact h1
  have hlog2 := Real.log_two_lt_d9
  have hlog2' := Real.log_two_gt_d9
  have hlogXnn : 0 ≤ Real.log X := Real.log_nonneg hXge1
  have hlogXle : Real.log X ≤ L2 * 0.7 := by
    have := Real.log_le_log hXpos hXL1
    rw [hlogL1] at this
    have h7 := mul_le_mul_of_nonneg_left hlog2.le hL2pos.le
    linarith
  set Q := X * Real.log X with hQ
  have hQnn : 0 ≤ Q := mul_nonneg hXpos.le hlogXnn
  have hXL2 : X * L2 = L1 / (150 * L2) := by
    rw [hX]; field_simp
  have hQle : Q * L2 ≤ L1 / 200 := by
    have h1 : Q ≤ X * (L2 * 0.7) := mul_le_mul_of_nonneg_left hlogXle hXpos.le
    have h3 : X * L2 * L2 = L1 / 150 := by
      rw [hXL2]; field_simp
    have h4 : Q * L2 ≤ X * (L2 * 0.7) * L2 := mul_le_mul_of_nonneg_right h1 hL2pos.le
    have h5 : X * (L2 * 0.7) * L2 = 0.7 * (X * L2 * L2) := by ring
    rw [h5, h3] at h4
    linarith
  -- β₂
  have hb2def : beta2 n c = 6 * (2 * beta1 n c) ^ (c - 1) * Real.log (beta1 n c) := rfl
  have hpow : (2 * beta1 n c) ^ (c - 1) * (2 * beta1 n c) = X / 2 ^ c := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ c)]
    rw [← hZc, hb1def]
    field_simp
    rw [← mul_pow]
    congr 1
    ring
  have hlogb1pos : 0.69 ≤ Real.log (beta1 n c) := by
    have := Real.log_le_log (by norm_num) hb1
    linarith
  have hpowge : 1 ≤ (2 * beta1 n c) ^ (c - 1) := one_le_pow₀ (by linarith)
  have hb2 : 1 ≤ beta2 n c := by
    rw [hb2def]
    have := mul_le_mul hpowge hlogb1pos (by norm_num) (by positivity)
    linarith
  have hb2pos : 0 < beta2 n c := by linarith
  have h2c : (2 : ℝ) * c ≤ 2 ^ c := by exact_mod_cast two_mul_le_two_pow c
  have h2cpos : (0 : ℝ) < 2 ^ c := by positivity
  -- β₂ · 2β₁ · c · 2^c ≤ 6 X log X
  have hb2b1 : beta2 n c * (2 * beta1 n c) * (c * 2 ^ c) ≤ 6 * Q := by
    have e : beta2 n c * (2 * beta1 n c) =
        6 * ((2 * beta1 n c) ^ (c - 1) * (2 * beta1 n c)) * Real.log (beta1 n c) := by
      rw [hb2def]; ring
    rw [e, hpow]
    have : X / 2 ^ c * Real.log (beta1 n c) * (c * 2 ^ c) = X * (c * Real.log (beta1 n c)) := by
      field_simp
    have hcl : c * Real.log (beta1 n c) ≤ Real.log X := by
      rw [le_div_iff₀ hcpos] at hlogb1; linarith
    calc 6 * (X / 2 ^ c) * Real.log (beta1 n c) * (c * 2 ^ c)
        = 6 * (X / 2 ^ c * Real.log (beta1 n c) * (c * 2 ^ c)) := by ring
      _ = 6 * (X * (c * Real.log (beta1 n c))) := by rw [this]
      _ ≤ 6 * Q := by
          have := mul_le_mul_of_nonneg_left hcl hXpos.le
          rw [hQ]; linarith
  have hcc : (c : ℝ) ^ 2 * 2 ≤ c * 2 ^ c := by
    have e : (c : ℝ) ^ 2 * 2 = c * (2 * c) := by ring
    rw [e]; exact mul_le_mul_of_nonneg_left h2c hcpos.le
  -- β₁ β₂ c² ≤ 1.5 Q
  have hb1b2c : beta1 n c * beta2 n c * (c : ℝ) ^ 2 ≤ 1.5 * Q := by
    have hA : 0 ≤ beta1 n c * beta2 n c := by positivity
    have : beta1 n c * beta2 n c * ((c : ℝ) ^ 2 * 2) ≤ beta1 n c * beta2 n c * (c * 2 ^ c) :=
      mul_le_mul_of_nonneg_left hcc hA
    linear_combination (1 / 4 : ℝ) * hb2b1 + (1 / 2 : ℝ) * this
  -- β₂ c² ≤ 0.75 Q
  have hb2c : beta2 n c * (c : ℝ) ^ 2 ≤ 0.75 * Q := by
    have hA : 0 ≤ beta2 n c * (c : ℝ) ^ 2 := by positivity
    have : beta2 n c * (c : ℝ) ^ 2 * 4 ≤ beta2 n c * (c : ℝ) ^ 2 * (2 * beta1 n c) :=
      mul_le_mul_of_nonneg_left (by linarith) hA
    linear_combination (1 / 4 : ℝ) * this + (1 / 2 : ℝ) * hb1b2c
  -- g
  set g := gParam n c with hg
  have hg_ge : 3 * beta1 n c * beta2 n c * (c : ℝ) ^ 2 ≤ g := by
    rw [hg]; unfold gParam; exact Nat.le_ceil _
  have hg_le : (g : ℝ) ≤ 4.5 * Q + 1 := by
    have : (g : ℝ) < 3 * beta1 n c * beta2 n c * (c : ℝ) ^ 2 + 1 := by
      rw [hg]; unfold gParam; exact Nat.ceil_lt_add_one (by positivity)
    linarith
  have hgnn : (0 : ℝ) ≤ g := Nat.cast_nonneg _
  refine ⟨hb1, hb2, ?_, ?_⟩
  · -- 10 β₂ c ≤ g
    have : 10 * beta2 n c * c ≤ 3 * beta1 n c * beta2 n c * (c : ℝ) ^ 2 := by
      have h1 : 0 ≤ beta2 n c * c := by positivity
      have h2 : beta2 n c * c * 12 ≤ beta2 n c * c * (3 * beta1 n c * c) :=
        mul_le_mul_of_nonneg_left (by have := aux_mul2 _ _ hb1 hcR; linarith) h1
      linear_combination h2 + 2 * h1
    linarith
  · -- the final estimate
    set Y := 6 * beta2 n c * (c : ℝ) ^ 2 with hY
    have hYnn : 0 ≤ Y := by positivity
    have hQL1 : Q ≤ L1 / 200 / 256 := by
      rw [le_div_iff₀ (by norm_num)]
      have : Q * 256 ≤ Q * L2 := mul_le_mul_of_nonneg_left hL2big hQnn
      linarith
    have hYL1 : Y ≤ L1 := by linarith
    have hgL1 : (g : ℝ) ≤ L1 := by linarith
    have hcL1 : (c : ℝ) ≤ L1 := by
      have := aux64 s hs_ge
      linarith
    have hb1L1 : beta1 n c ≤ L1 := by rw [hb1def]; linarith
    have hYpow : Y ^ (2 * g + 2) ≤ L1 ^ (2 * g + 2) := pow_le_pow_left₀ hYnn hYL1 _
    have hstep : 2 * (g : ℝ) * c * Y ^ (2 * g + 2) * beta1 n c ≤ 2 * L1 ^ (2 * g + 5) := by
      have e : (2 : ℝ) * L1 ^ (2 * g + 5) = 2 * L1 * L1 * L1 ^ (2 * g + 2) * L1 := by ring
      rw [e]
      have h1 : 2 * (g : ℝ) * c ≤ 2 * L1 * L1 := by
        have := mul_le_mul hgL1 hcL1 (by positivity) hL1pos.le
        linear_combination 2 * this
      have h2 : 2 * (g : ℝ) * c * Y ^ (2 * g + 2) ≤ 2 * L1 * L1 * L1 ^ (2 * g + 2) :=
        mul_le_mul h1 hYpow (by positivity) (by positivity)
      exact mul_le_mul h2 hb1L1 hb1pos.le (by positivity)
    have hexp : 1 + L2 * (2 * (g : ℝ) + 5) ≤ L1 := by
      have h1 : L2 * g ≤ L2 * (4.5 * Q + 1) := mul_le_mul_of_nonneg_left hg_le hL2pos.le
      have h2 : 1 + 42 * s ≤ 0.9 * s ^ 4 := aux42 s hs_ge
      linarith
    have hfin : 2 * L1 ^ (2 * g + 5) ≤ (n : ℝ) := by
      rw [← hneq]
      have e1 : L1 ^ (2 * g + 5) = (2 : ℝ) ^ (L2 * ((2 * g + 5 : ℕ) : ℝ)) := by
        rw [← hL1eq, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      rw [e1]
      calc (2 : ℝ) * (2 : ℝ) ^ (L2 * ((2 * g + 5 : ℕ) : ℝ))
          = (2 : ℝ) ^ (1 + L2 * ((2 * g + 5 : ℕ) : ℝ)) := by
            rw [Real.rpow_add (by norm_num), Real.rpow_one]
        _ ≤ (2 : ℝ) ^ L1 := by
            apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
            push_cast; linarith
    rw [le_div_iff₀ hb1pos]
    linarith

end EDPParamsAux

open EDPHardness.IntegralityGap in
theorem solution :
    ∃ α : ℝ, 0 < α ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ c : ℕ, 2 ≤ c →
      (c : ℝ) ≤ α * Real.logb 2 (Real.logb 2 n) / Real.logb 2 (Real.logb 2 (Real.logb 2 n)) →
      ∀ H : Hyp n (numEdges n c) c, ¬ E1 n c H → ¬ E2 n c H → ¬ E3 n c (2 * gParam n c) H →
      ∀ R : IntRouting (gapGraph H) (src n (numEdges n c)) (snk n (numEdges n c)) (c - 1),
        (R.routed.card : ℝ) ≤ 4 * (n : ℝ) / beta1 n c := by
  classical
  obtain ⟨α, hα, N₀, hN⟩ := EDPParamsAux.params
  refine ⟨α, hα, N₀, ?_⟩
  intro n hn c hc hcα H hE1 hE2 hE3 R
  obtain ⟨hb1, hb2, hg, hT⟩ := hN n hn c hc hcα
  have hb1pos : 0 < beta1 n c := by linarith
  have hA := canonical_paths_bound n c hc hb1pos H hE1 R
  have hB := long_paths_bound n c hc hb1pos hb2 H R
  have hC := short_paths_bound n c hc hb1pos (by linarith) hg H hE2 hE3 R
  set A := Finset.univ.filter
    (fun v : R.routed => (R.path v).support = canonicalSupport H v)
  set B := Finset.univ.filter
    (fun v : R.routed => (R.path v).support ≠ canonicalSupport H v ∧
      gParam n c ≤ (R.path v).length)
  set C := Finset.univ.filter
    (fun v : R.routed => (R.path v).support ≠ canonicalSupport H v ∧
      (R.path v).length < gParam n c)
  have h1 : (Finset.univ : Finset R.routed) ⊆ A ∪ B ∪ C := by
    intro v _
    simp only [A, B, C, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hp : (R.path v).support = canonicalSupport H v
    · exact Or.inl (Or.inl hp)
    · by_cases hq : gParam n c ≤ (R.path v).length
      · exact Or.inl (Or.inr ⟨hp, hq⟩)
      · exact Or.inr ⟨hp, lt_of_not_ge hq⟩
  have h2 := (Finset.card_le_card h1).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  rw [Finset.card_univ, Fintype.card_coe] at h2
  have h3 : (R.routed.card : ℝ) ≤ A.card + B.card + C.card := by exact_mod_cast h2
  rw [mul_div_assoc]
  linarith
