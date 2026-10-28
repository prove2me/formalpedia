-- Prove2me | solution 1 for DusartFinite.pi_le_div_log_sub_one_point_one
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T19:14:26.287482+00:00
-- url     : https://prove2.me/submissions/7c2e268b-c344-419f-90eb-99eefc9fe418

import Mathlib
import Definitions.Def_DusartCertData_0
import Definitions.Def_DusartCertData_1
import Definitions.Def_DusartCertData_2
import Definitions.Def_DusartCertData_3
import Definitions.Def_DusartCertData_4
import Definitions.Def_DusartCertData_5
import Definitions.Def_DusartCertData_6
import Definitions.Def_DusartCertData_7
import Definitions.Def_DusartCertData_8
import Definitions.Def_DusartCertData_9
import Definitions.Def_DusartCertData_10
import Definitions.Def_DusartCertData_11
import Definitions.Def_DusartCertData_12
import Definitions.Def_DusartCertData_13

section

open Finset

set_option autoImplicit false

namespace S68PiCert
open DusartCert

abbrev St := Nat × List Nat × Nat × Nat × Nat

/-- Walk wheel candidates `n` (remaining gap list `gs`), counting kept candidates in `k`; `U` is a
`Q`-scaled upper bound for `log L`. At each kept candidate `n ≥ L` check `k (U/Q - 1.1) ≤ L`, then move
`L := n`, `U := U + ⌈Q (n - L) / L⌉`. -/
noncomputable def pstep (Q : Nat) (cs : List Nat) : List Nat → Nat → Nat → Nat → Nat → Option St :=
  cs.rec (fun gs n k U L => some (n, gs, k, U, L)) (fun c _ ih gs n k U L =>
    gs.casesOn none (fun g t =>
    cond (Nat.beq c 0)
      (cond (Nat.blt n L) (ih (cond t.isEmpty gaps t) (n + g) (k + 1) U L)
        (cond (Nat.ble (10 * k * U) (10 * L * Q + 11 * k * Q))
          (ih (cond t.isEmpty gaps t) (n + g) (k + 1) (U + (Q * (n - L) + L - 1) / L) n) none))
      (cond (Nat.blt 1 c && Nat.blt c n && Nat.beq (n % c) 0) (ih (cond t.isEmpty gaps t) (n + g) k U L) none)))

noncomputable def prun (Q : Nat) (l : List (List Nat × Option (Nat × Nat × Nat))) : St → Option St :=
  l.rec (fun s => some s) (fun x _ ih s =>
    (pstep Q x.1 s.2.1 s.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2).casesOn none ih)

def QQ : Nat := 18446744073709551616

/-- Final check on the end state. -/
def finOK (s : St) : Bool :=
  Nat.blt 2000000 s.1 && Nat.ble (10 * s.2.2.1 * s.2.2.2.1) (10 * s.2.2.2.2 * QQ + 11 * s.2.2.1 * QQ)

lemma gaps_pos : ∀ i < 48, 0 < gaps.getD i 0 := by decide +kernel

lemma res_next : ∀ i < 48, (res.getD i 0 + gaps.getD i 0) % 210 = res.getD ((i + 1) % 48) 0 := by decide +kernel

lemma gap_between : ∀ i < 48, ∀ t < 11, 0 < t → t < gaps.getD i 0 → Nat.gcd ((res.getD i 0 + t) % 210) 210 ≠ 1 := by
  decide +kernel

lemma gaps_le : ∀ i < 48, gaps.getD i 0 ≤ 10 := by decide +kernel

lemma prime_dvd_210 : ∀ k ≤ 210, k ∣ 210 → k.Prime → k ≤ 7 := by decide +kernel

/-- Integers strictly between consecutive wheel candidates are not primes above 7. -/
lemma not_prime_between {i n k : ℕ} (hi : i < 48) (hn : n % 210 = res.getD i 0) (hk1 : n < k)
    (hk2 : k < n + gaps.getD i 0) : ¬ (k.Prime ∧ 7 < k) := by
  rintro ⟨hp, h7⟩
  have hgl := gaps_le i hi
  have hg := gap_between i hi (k - n) (by omega) (by omega) (by omega)
  have hmod : (res.getD i 0 + (k - n)) % 210 = k % 210 := by
    rw [← hn]; omega
  rw [hmod, ← Nat.gcd_rec] at hg
  have hdvd : k ∣ 210 := by
    by_contra h
    exact hg (by rw [Nat.gcd_comm]; exact (hp.coprime_iff_not_dvd.2 h))
  have := prime_dvd_210 k (Nat.le_of_dvd (by norm_num) hdvd) hdvd hp
  omega

lemma hasSum_log_atanh {y : ℝ} (hy : 1 ≤ y) :
    HasSum (fun j : ℕ => 2 * (1 / (2 * (j : ℝ) + 1)) * ((y - 1) / (y + 1)) ^ (2 * j + 1)) (Real.log y) := by
  have hz0 : 0 ≤ (y - 1) / (y + 1) := div_nonneg (by linarith) (by linarith)
  have hz1 : (y - 1) / (y + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have h := Real.hasSum_log_sub_log_of_abs_lt_one (x := (y - 1) / (y + 1)) (by rw [abs_of_nonneg hz0]; exact hz1)
  convert h using 1
  rw [← Real.log_div (by positivity) (by linarith)]
  congr 1
  field_simp; ring

lemma atanh_lower {y : ℝ} (hy : 1 ≤ y) (K : ℕ) :
    ∑ j ∈ range K, 2 * (1 / (2 * (j : ℝ) + 1)) * ((y - 1) / (y + 1)) ^ (2 * j + 1) ≤ Real.log y := by
  have hz0 : 0 ≤ (y - 1) / (y + 1) := div_nonneg (by linarith) (by linarith)
  exact sum_le_hasSum _ (fun j _ => by positivity) (hasSum_log_atanh hy)

lemma atanh_upper {y : ℝ} (hy : 1 ≤ y) (K : ℕ) :
    Real.log y ≤ ∑ j ∈ range K, 2 * (1 / (2 * (j : ℝ) + 1)) * ((y - 1) / (y + 1)) ^ (2 * j + 1) +
      2 * ((y - 1) / (y + 1)) ^ (2 * K + 1) / ((2 * K + 1) * (1 - ((y - 1) / (y + 1)) ^ 2)) := by
  set z := (y - 1) / (y + 1) with hz
  have hz0 : 0 ≤ z := div_nonneg (by linarith) (by linarith)
  have hz1 : z < 1 := by rw [hz, div_lt_one (by linarith)]; linarith
  have hS := hasSum_log_atanh hy
  rw [← hz] at hS
  have hsplit := hS.summable.sum_add_tsum_nat_add K
  rw [hS.tsum_eq] at hsplit
  rw [← hsplit]
  gcongr
  have hz2 : z ^ 2 < 1 := by nlinarith
  have hgeo : Summable fun j : ℕ => 2 * z ^ (2 * K + 1) / (2 * K + 1) * (z ^ 2) ^ j :=
    (summable_geometric_of_lt_one (by positivity) hz2).mul_left _
  have hle : ∀ j : ℕ, 2 * (1 / (2 * ((j + K : ℕ) : ℝ) + 1)) * z ^ (2 * (j + K) + 1) ≤
      2 * z ^ (2 * K + 1) / (2 * K + 1) * (z ^ 2) ^ j := by
    intro j
    rw [← pow_mul, show 2 * (j + K) + 1 = (2 * K + 1) + 2 * j by ring, pow_add]
    have h1 : 1 / (2 * ((j + K : ℕ) : ℝ) + 1) ≤ 1 / (2 * (K : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity); push_cast; linarith [show (0 : ℝ) ≤ j from Nat.cast_nonneg j]
    have h2 : 0 ≤ z ^ (2 * K + 1) * z ^ (2 * j) := by positivity
    calc 2 * (1 / (2 * ((j + K : ℕ) : ℝ) + 1)) * (z ^ (2 * K + 1) * z ^ (2 * j))
        ≤ 2 * (1 / (2 * (K : ℝ) + 1)) * (z ^ (2 * K + 1) * z ^ (2 * j)) := by gcongr
      _ = 2 * z ^ (2 * K + 1) / (2 * K + 1) * z ^ (2 * j) := by ring
  calc ∑' j : ℕ, 2 * (1 / (2 * ((j + K : ℕ) : ℝ) + 1)) * z ^ (2 * (j + K) + 1)
      ≤ ∑' j : ℕ, 2 * z ^ (2 * K + 1) / (2 * K + 1) * (z ^ 2) ^ j :=
        Summable.tsum_le_tsum hle (hgeo.of_nonneg_of_le (fun j => by positivity) hle) hgeo
    _ = 2 * z ^ (2 * K + 1) / ((2 * K + 1) * (1 - z ^ 2)) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) hz2]
        have : (1 - z ^ 2) ≠ 0 := by linarith
        field_simp

lemma floor_div_le (N D : ℕ) (hD : 0 < D) : ((N / D : ℕ) : ℝ) ≤ (N : ℝ) / D := by
  rw [le_div_iff₀ (by exact_mod_cast hD)]; exact_mod_cast Nat.div_mul_le_self N D

lemma le_cdiv (N D : ℕ) (hD : 0 < D) : (N : ℝ) / D ≤ (cdiv N D : ℝ) := by
  rw [div_le_iff₀ (by exact_mod_cast hD)]
  have h2 := Nat.div_add_mod (N + D - 1) D
  have h3 := Nat.mod_lt (N + D - 1) hD
  have : N ≤ cdiv N D * D := by
    unfold cdiv; rw [Nat.mul_comm] at h2
    generalize (N + D - 1) / D * D = X at *; omega
  exact_mod_cast this

/-- The real term `Q · 2 (a/b)^(2j+1)/(2j+1)`. -/
lemma lterm_real (Q a b j : ℕ) (hb : 0 < b) :
    (Q : ℝ) * (2 * (1 / (2 * (j : ℝ) + 1)) * ((a : ℝ) / b) ^ (2 * j + 1)) =
      ((2 * Q * a ^ (2 * j + 1) : ℕ) : ℝ) / (((2 * j + 1) * b ^ (2 * j + 1) : ℕ) : ℝ) := by
  have : (b : ℝ) ≠ 0 := by positivity
  push_cast; rw [div_pow]; field_simp

lemma lsumLo_le (Q a b : ℕ) (hb : 0 < b) : ∀ K, (lsumLo Q a b K : ℝ) ≤
    (Q : ℝ) * ∑ j ∈ range K, 2 * (1 / (2 * (j : ℝ) + 1)) * ((a : ℝ) / b) ^ (2 * j + 1) := by
  intro K; induction K with
  | zero => simp [lsumLo]
  | succ K ih =>
    rw [lsumLo, Nat.cast_add, sum_range_succ, mul_add, lterm_real Q a b K hb]
    have := floor_div_le (2 * Q * a ^ (2 * K + 1)) ((2 * K + 1) * b ^ (2 * K + 1)) (by positivity)
    unfold ltermLo; linarith

lemma lsumHi_ge (Q a b : ℕ) (hb : 0 < b) : ∀ K,
    (Q : ℝ) * ∑ j ∈ range K, 2 * (1 / (2 * (j : ℝ) + 1)) * ((a : ℝ) / b) ^ (2 * j + 1) ≤ (lsumHi Q a b K : ℝ) := by
  intro K; induction K with
  | zero => simp [lsumHi]
  | succ K ih =>
    rw [lsumHi, Nat.cast_add, sum_range_succ, mul_add, lterm_real Q a b K hb]
    have := le_cdiv (2 * Q * a ^ (2 * K + 1)) ((2 * K + 1) * b ^ (2 * K + 1)) (by positivity)
    unfold ltermHi; linarith

/-- **Reduced log bounds.** For `0 < den ≤ num`: `logRedLo ≤ Q log(num/den) ≤ logRedHi`. -/
theorem logRed_bounds (Q num den : ℕ) (hd : 0 < den) (hle : den ≤ num) :
    (logRedLo Q num den : ℝ) ≤ Q * Real.log ((num : ℝ) / den) ∧
      Q * Real.log ((num : ℝ) / den) ≤ (logRedHi Q num den : ℝ) := by
  have hden : (0 : ℝ) < den := by exact_mod_cast hd
  have hy : (1 : ℝ) ≤ (num : ℝ) / den := by rw [le_div_iff₀ hden]; simp; exact_mod_cast hle
  have hb : 0 < num + den := by omega
  have hz : ((num : ℝ) / den - 1) / ((num : ℝ) / den + 1) = (((num - den : ℕ) : ℝ)) / ((num + den : ℕ) : ℝ) := by
    rw [Nat.cast_sub hle]; push_cast; field_simp
  have hQ : (0 : ℝ) ≤ Q := Nat.cast_nonneg Q
  constructor
  · have := atanh_lower hy nterms
    rw [hz] at this
    exact (lsumLo_le Q (num - den) (num + den) hb nterms).trans (mul_le_mul_of_nonneg_left this hQ)
  · have hu := atanh_upper hy nterms
    rw [hz] at hu
    have h1 := lsumHi_ge Q (num - den) (num + den) hb nterms
    -- remainder
    set a := num - den; set b := num + den
    have hab : a < b := by omega
    have hb2 : 0 < b ^ 2 - a ^ 2 := by
      have : a ^ 2 < b ^ 2 := Nat.pow_lt_pow_left hab (by norm_num)
      omega
    have hrem := le_cdiv (2 * Q * a ^ (2 * nterms + 1) * b ^ 2) ((2 * nterms + 1) * b ^ (2 * nterms + 1) * (b ^ 2 - a ^ 2))
      (by positivity)
    have hremeq : (Q : ℝ) * (2 * ((a : ℝ) / b) ^ (2 * nterms + 1) / ((2 * nterms + 1) * (1 - ((a : ℝ) / b) ^ 2))) =
        ((2 * Q * a ^ (2 * nterms + 1) * b ^ 2 : ℕ) : ℝ) /
          (((2 * nterms + 1) * b ^ (2 * nterms + 1) * (b ^ 2 - a ^ 2) : ℕ) : ℝ) := by
      have hb0 : (b : ℝ) ≠ 0 := by positivity
      have hsub : ((b ^ 2 - a ^ 2 : ℕ) : ℝ) = (b : ℝ) ^ 2 - (a : ℝ) ^ 2 := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      have hne : (b : ℝ) ^ 2 - (a : ℝ) ^ 2 ≠ 0 := by
        rw [← hsub]; exact_mod_cast hb2.ne'
      push_cast [hsub]
      simp only [div_pow]
      field_simp
    unfold logRedHi lrem
    rw [Nat.cast_add]
    calc (Q : ℝ) * Real.log ((num : ℝ) / den) ≤ (Q : ℝ) * (∑ j ∈ range nterms,
          2 * (1 / (2 * (j : ℝ) + 1)) * ((a : ℝ) / b) ^ (2 * j + 1) +
          2 * ((a : ℝ) / b) ^ (2 * nterms + 1) / ((2 * nterms + 1) * (1 - ((a : ℝ) / b) ^ 2))) :=
          mul_le_mul_of_nonneg_left hu hQ
      _ ≤ _ := by rw [mul_add, hremeq]; linarith

/-- **Log bounds with range reduction.** -/
theorem log_bounds (Q num den k : ℕ) (h : redOK num den k = true) :
    (logLo Q num den k : ℝ) ≤ Q * Real.log ((num : ℝ) / den) ∧
      Q * Real.log ((num : ℝ) / den) ≤ (logHi Q num den k : ℝ) := by
  simp only [redOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, _⟩, hd⟩ := h
  have h2 := logRed_bounds Q 2 1 one_pos (by norm_num)
  have hk := logRed_bounds Q num (den * 2 ^ k) (by positivity) h1
  have hden : (0 : ℝ) < den := by exact_mod_cast hd
  have hsplit : Real.log ((num : ℝ) / den) = k * Real.log 2 + Real.log ((num : ℝ) / ((den * 2 ^ k : ℕ) : ℝ)) := by
    have hnum : (0 : ℝ) < num := by
      have : 0 < den * 2 ^ k := by positivity
      exact_mod_cast lt_of_lt_of_le this h1
    push_cast
    rw [Real.log_div hnum.ne' hden.ne', Real.log_div hnum.ne' (by positivity : (den : ℝ) * 2 ^ k ≠ 0),
      Real.log_mul hden.ne' (by positivity), Real.log_pow]; ring
  have hl2 : Real.log ((2 : ℕ) / ((1 : ℕ) : ℝ)) = Real.log 2 := by norm_num
  rw [hl2] at h2
  unfold logLo logHi
  push_cast
  rw [hsplit]
  constructor
  · nlinarith [h2.1, hk.1, show (0 : ℝ) ≤ k from Nat.cast_nonneg k]
  · nlinarith [h2.2, hk.2, show (0 : ℝ) ≤ k from Nat.cast_nonneg k]

lemma gs_step : ∀ i < 48, gaps.drop i = gaps.getD i 0 :: gaps.drop (i + 1) ∧
    cond (gaps.drop (i + 1)).isEmpty gaps (gaps.drop (i + 1)) = gaps.drop ((i + 1) % 48) := by
  decide +kernel

lemma count_gap {n g : ℕ} (h : ∀ j, n < j → j < n + g → ¬ j.Prime) :
    ∀ t, 0 < t → t ≤ g → Nat.count Nat.Prime (n + t) = Nat.count Nat.Prime n + if n.Prime then 1 else 0 := by
  intro t
  induction t with
  | zero => intro h0; omega
  | succ t ih =>
    intro _ ht
    rw [← add_assoc, Nat.count_succ]
    rcases Nat.eq_zero_or_pos t with rfl | ht0
    · simp
    · rw [ih ht0 (by omega), if_neg (h (n + t) (by omega) (by omega))]; simp

noncomputable def good (m : ℕ) : Prop := (Nat.primeCounting m : ℝ) * (Real.log m - 11 / 10) ≤ m

lemma three_le_log {L : ℕ} (hL : 60184 ≤ L) : 3 ≤ Real.log L := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  have h1 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  have h2 := Real.exp_one_lt_d9
  have h3 : (60184 : ℝ) ≤ L := by exact_mod_cast hL
  have h0 := Real.exp_pos 1
  rw [h1]
  nlinarith [pow_lt_pow_left₀ h2 h0.le (by norm_num : (3 : ℕ) ≠ 0)]

lemma log_le_lin {L m : ℕ} (hL : 0 < L) (hm : L ≤ m) :
    Real.log m ≤ Real.log L + ((m : ℝ) - L) / L := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hm' : (0 : ℝ) < m := lt_of_lt_of_le hL' (by exact_mod_cast hm)
  have := Real.log_le_sub_one_of_pos (div_pos hm' hL')
  rw [Real.log_div hm'.ne' hL'.ne'] at this
  have e : (m : ℝ) / L - 1 = ((m : ℝ) - L) / L := by field_simp
  linarith

lemma good_of_check {Q k U L m : ℕ} (hQ : 0 < Q) (hc : 10 * k * U ≤ 10 * L * Q + 11 * k * Q)
    (hlog : Real.log L ≤ (U : ℝ) / Q) (hL : 60184 ≤ L) (hm : L ≤ m) (hk : Nat.primeCounting m ≤ k) :
    good m := by
  unfold good
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hL0 : (0 : ℝ) < L := lt_of_lt_of_le (by norm_num) (show (60184 : ℝ) ≤ L by exact_mod_cast hL)
  have hc' : (k : ℝ) * ((U : ℝ) / Q - 11 / 10) ≤ L := by
    have : ((10 * k * U : ℕ) : ℝ) ≤ ((10 * L * Q + 11 * k * Q : ℕ) : ℝ) := by exact_mod_cast hc
    push_cast at this
    have e : (k : ℝ) * ((U : ℝ) / Q - 11 / 10) = ((10 * k * U : ℝ) - 11 * k * Q) / (10 * Q) := by
      field_simp
    rw [e, div_le_iff₀ (by positivity)]; linarith
  have h3 := three_le_log hL
  have hlm := log_le_lin (by omega) hm
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hkL : (k : ℝ) ≤ L := by nlinarith
  have hpk : (Nat.primeCounting m : ℝ) ≤ k := by exact_mod_cast hk
  have hmL : (L : ℝ) ≤ m := by exact_mod_cast hm
  have hlogm : 3 ≤ Real.log m := le_trans h3 (Real.log_le_log hL0 hmL)
  have hfrac : (k : ℝ) * (((m : ℝ) - L) / L) ≤ (m : ℝ) - L := by
    rw [mul_div_assoc']; rw [div_le_iff₀ hL0]; nlinarith
  calc (Nat.primeCounting m : ℝ) * (Real.log m - 11 / 10) ≤ k * (Real.log m - 11 / 10) :=
        mul_le_mul_of_nonneg_right hpk (by linarith)
    _ ≤ k * (Real.log L + ((m : ℝ) - L) / L - 11 / 10) := mul_le_mul_of_nonneg_left (by linarith) hk0
    _ = k * (Real.log L - 11 / 10) + k * (((m : ℝ) - L) / L) := by ring
    _ ≤ L + ((m : ℝ) - L) := by
        have : (k : ℝ) * (Real.log L - 11 / 10) ≤ k * ((U : ℝ) / Q - 11 / 10) :=
          mul_le_mul_of_nonneg_left (by linarith) hk0
        linarith
    _ = m := by ring

def InvV (Q n : ℕ) (gs : List ℕ) (k U L : ℕ) : Prop :=
  ∃ i < 48, gs = gaps.drop i ∧ n % 210 = res.getD i 0 ∧ 11 ≤ n ∧ Nat.count Nat.Prime n ≤ k ∧
    60184 ≤ L ∧ Real.log L ≤ (U : ℝ) / Q ∧ (L = 60184 ∨ L < n) ∧
    ∀ m, 60184 ≤ m → m < n → m < L → good m

lemma pc_le {m n k : ℕ} (hmn : m < n) (h : Nat.count Nat.Prime n ≤ k) : Nat.primeCounting m ≤ k := by
  have : Nat.primeCounting m = Nat.count Nat.Prime (m + 1) := rfl
  rw [this]; exact le_trans (Nat.count_monotone _ (by omega)) h

lemma cdiv_real (Q n L : ℕ) (hL : 0 < L) :
    ((n : ℝ) - L) / L ≤ (((Q * (n - L) + L - 1) / L : ℕ) : ℝ) / Q ∨ Q = 0 := by
  rcases Nat.eq_zero_or_pos Q with h | hQ
  · right; exact h
  left
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  have := le_cdiv (Q * (n - L)) L hL
  unfold cdiv at this
  rw [le_div_iff₀ hQ']
  calc ((n : ℝ) - L) / L * Q ≤ ((n - L : ℕ) : ℝ) / L * Q := by
        gcongr
        rcases le_total L n with h | h
        · rw [Nat.cast_sub h]
        · have : (n : ℝ) ≤ L := by exact_mod_cast h
          linarith [(Nat.cast_nonneg (n - L) : (0 : ℝ) ≤ _)]
    _ = ((Q * (n - L) : ℕ) : ℝ) / L := by push_cast; ring
    _ ≤ _ := this

theorem pstep_sound (Q : ℕ) (hQ : 0 < Q) : ∀ (cs gs : List ℕ) (n k U L : ℕ) (s : St),
    InvV Q n gs k U L → pstep Q cs gs n k U L = some s → InvV Q s.1 s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2 := by
  intro cs
  induction cs with
  | nil =>
    intro gs n k U L s hI h
    simp only [pstep, Option.some.injEq] at h
    subst h; exact hI
  | cons c cs ih =>
    intro gs n k U L s hI h
    obtain ⟨i, hi, hgs, hn, hn11, hk, hL, hlog, hLn, hgood⟩ := hI
    obtain ⟨hd, hrot⟩ := gs_step i hi
    rw [hgs, hd] at h
    have hg := gaps_pos i hi
    have hi' : (i + 1) % 48 < 48 := Nat.mod_lt _ (by norm_num)
    have hn' : (n + gaps.getD i 0) % 210 = res.getD ((i + 1) % 48) 0 := by
      rw [← res_next i hi, Nat.add_mod, hn, Nat.add_mod (res.getD i 0)]; simp
    have hnp : ∀ j, n < j → j < n + gaps.getD i 0 → ¬ j.Prime := fun j h1 h2 hp =>
      not_prime_between hi hn h1 h2 ⟨hp, by omega⟩
    have hcnt := count_gap hnp _ hg le_rfl
    change cond (Nat.beq c 0)
      (cond (Nat.blt n L) (pstep Q cs (cond (gaps.drop (i+1)).isEmpty gaps (gaps.drop (i+1))) (n + gaps.getD i 0) (k + 1) U L)
        (cond (Nat.ble (10 * k * U) (10 * L * Q + 11 * k * Q))
          (pstep Q cs (cond (gaps.drop (i+1)).isEmpty gaps (gaps.drop (i+1))) (n + gaps.getD i 0) (k + 1)
            (U + (Q * (n - L) + L - 1) / L) n) none))
      (cond (Nat.blt 1 c && Nat.blt c n && Nat.beq (n % c) 0)
        (pstep Q cs (cond (gaps.drop (i+1)).isEmpty gaps (gaps.drop (i+1))) (n + gaps.getD i 0) k U L) none) = some s at h
    rw [hrot] at h
    cases hc0 : Nat.beq c 0
    · -- composite code
      rw [hc0] at h
      cases hv : (Nat.blt 1 c && Nat.blt c n && Nat.beq (n % c) 0)
      · rw [hv] at h; simp at h
      rw [hv] at h
      simp only [cond_true] at h
      simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hv
      have hnot : ¬ n.Prime := fun hp =>
        Nat.not_prime_of_dvd_of_lt (Nat.dvd_of_mod_eq_zero hv.2) hv.1.1 hv.1.2 hp
      refine ih _ _ _ _ _ s ⟨_, hi', rfl, hn', by omega, ?_, hL, hlog, ?_, ?_⟩ h
      · rw [hcnt, if_neg hnot]; simpa using hk
      · rcases hLn with h1 | h1 <;> [left; right] <;> omega
      · intro m hm1 hm2 hm3
        by_cases hmn : m < n
        · exact hgood m hm1 hmn hm3
        · exfalso; rcases hLn with h1 | h1 <;> omega
    · rw [hc0] at h
      simp only [cond_true] at h
      have hk1 : Nat.count Nat.Prime (n + gaps.getD i 0) ≤ k + 1 := by
        rw [hcnt]; split_ifs <;> omega
      cases hb : Nat.blt n L
      · rw [hb] at h
        simp only [cond_false] at h
        have hb : L ≤ n := Nat.not_lt.mp (fun h' => by rw [Nat.blt_eq.mpr h'] at hb; exact Bool.noConfusion hb)
        cases hch : Nat.ble (10 * k * U) (10 * L * Q + 11 * k * Q)
        · rw [hch] at h; simp at h
        rw [hch] at h
        simp only [cond_true] at h
        simp only [Nat.ble_eq] at hch
        refine ih _ _ _ _ _ s ⟨_, hi', rfl, hn', by omega, hk1, by omega, ?_, Or.inr (by omega), ?_⟩ h
        · have h1 := log_le_lin (by omega) hb
          rcases cdiv_real Q n L (by omega) with h2 | h2
          · push_cast; rw [add_div]; linarith
          · omega
        · intro m hm1 hm2 hm3
          by_cases hmL : m < L
          · exact hgood m hm1 hm3 hmL
          · exact good_of_check hQ hch hlog hL (by omega) (pc_le hm3 hk)
      · rw [hb] at h
        simp only [cond_true] at h
        simp only [Nat.blt_eq] at hb
        have hLS : L = 60184 := by rcases hLn with h1 | h1 <;> omega
        refine ih _ _ _ _ _ s ⟨_, hi', rfl, hn', by omega, hk1, hL, hlog, Or.inl hLS, ?_⟩ h
        intro m hm1 hm2 hm3; omega

theorem prun_sound (Q : ℕ) (hQ : 0 < Q) : ∀ (l : List (List ℕ × Option (ℕ × ℕ × ℕ))) (s s' : St),
    InvV Q s.1 s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2 → prun Q l s = some s' →
    InvV Q s'.1 s'.2.1 s'.2.2.1 s'.2.2.2.1 s'.2.2.2.2 := by
  intro l
  induction l with
  | nil => intro s s' hI h; simp only [prun, Option.some.injEq] at h; subst h; exact hI
  | cons x xs ih =>
    intro s s' hI h
    change (pstep Q x.1 s.2.1 s.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2).casesOn none (prun Q xs) = some s' at h
    cases hp : pstep Q x.1 s.2.1 s.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2 with
    | none => rw [hp] at h; simp at h
    | some t =>
      rw [hp] at h
      exact ih t s' (pstep_sound Q hQ _ _ _ _ _ _ _ hI hp) h

lemma QQ_pos : 0 < QQ := by norm_num [QQ]

lemma logS : Real.log ((60184 : ℕ) : ℝ) ≤ ((logHi QQ 60184 1 15 : ℕ) : ℝ) / (QQ : ℝ) := by
  have h := (log_bounds QQ 60184 1 15 (by decide +kernel)).2
  have hQ : (0 : ℝ) < QQ := by exact_mod_cast QQ_pos
  rw [le_div_iff₀ hQ]
  simp only [Nat.cast_one, div_one] at h
  linarith

lemma inv0 : InvV QQ 11 (gaps.drop 1) 4 (logHi QQ 60184 1 15) 60184 := by
  refine ⟨1, by norm_num, rfl, by decide, le_rfl, by decide, le_rfl, logS, Or.inl rfl, ?_⟩
  intro m h1 h2; omega

set_option maxRecDepth 200000 in
theorem pb0 : prun QQ Gen.items0 (11, gaps.drop 1, 4, logHi QQ 60184 1 15, 60184) =
    some (157007, gaps.drop 30, 14433, 220696126601250209557, 156979) := by decide +kernel

set_option maxRecDepth 200000 in
theorem pb1 : prun QQ Gen.items1 (157007, gaps.drop 30, 14433, 220696126601250209557, 156979) =
    some (313909, gaps.drop 38, 27107, 233479442108861945492, 313897) := by decide +kernel

set_option maxRecDepth 200000 in
theorem pb2 : prun QQ Gen.items2 (313909, gaps.drop 38, 27107, 233479442108861945492, 313897) =
    some (471407, gaps.drop 37, 39339, 240980988185374988682, 471403) := by decide +kernel

set_option maxRecDepth 200000 in
theorem pb3 : prun QQ Gen.items3 (471407, gaps.drop 37, 39339, 240980988185374988682, 471403) =
    some (627089, gaps.drop 6, 51131, 246245159455576355421, 627083) := by decide +kernel

set_option maxRecDepth 200000 in
theorem pb4 : prun QQ Gen.items4 (627089, gaps.drop 6, 51131, 246245159455576355421, 627083) =
    some (783151, gaps.drop 14, 62701, 250344903757342998766, 783149) := by decide +kernel

set_option maxRecDepth 200000 in
theorem pb5 : prun QQ Gen.items5 (783151, gaps.drop 14, 62701, 250344903757342998766, 783149) =
    some (938879, gaps.drop 40, 74108, 253690320267046272357, 938869) := by decide +kernel

set_option maxRecDepth 200000 in
theorem pb6 : prun QQ Gen.items6 (938879, gaps.drop 40, 74108, 253690320267046272357, 938869) =
    some (1089523, gaps.drop 10, 84952, 256435346273857382248, 1089509) := by decide +kernel

set_option maxRecDepth 200000 in
theorem pb7 : prun QQ Gen.items7 (1089523, gaps.drop 10, 84952, 256435346273857382248, 1089509) =
    some (1239877, gaps.drop 8, 95733, 258819693253781231432, 1239839) := by decide +kernel

set_option maxRecDepth 200000 in
theorem pb8 : prun QQ Gen.items8 (1239877, gaps.drop 8, 95733, 258819693253781231432, 1239839) =
    some (1389643, gaps.drop 17, 106360, 260923660784416737511, 1389629) := by decide +kernel

set_option maxRecDepth 200000 in
theorem pb9 : prun QQ Gen.items9 (1389643, gaps.drop 17, 106360, 260923660784416737511, 1389629) =
    some (1543631, gaps.drop 29, 117211, 262861939053321715604, 1543589) := by decide +kernel

set_option maxRecDepth 200000 in
theorem pb10 : prun QQ Gen.items10 (1543631, gaps.drop 29, 117211, 262861939053321715604, 1543589) =
    some (1691531, gaps.drop 43, 127537, 264550224616198858308, 1691527) := by decide +kernel

set_option maxRecDepth 200000 in
theorem pb11 : prun QQ Gen.items11 (1691531, gaps.drop 43, 127537, 264550224616198858308, 1691527) =
    some (1841113, gaps.drop 10, 137914, 266113366619529312185, 1841111) := by decide +kernel

set_option maxRecDepth 200000 in
theorem pb12 : prun QQ Gen.items12 (1841113, gaps.drop 10, 137914, 266113366619529312185, 1841111) =
    some (1998221, gaps.drop 16, 148809, 267623833970680526650, 1998209) := by decide +kernel

set_option maxRecDepth 200000 in
theorem pb13 : prun QQ Gen.items13 (1998221, gaps.drop 16, 148809, 267623833970680526650, 1998209) =
    some (2150977, gaps.drop 35, 159313, 268982761103897324316, 2150969) := by decide +kernel

theorem fin14 : 10 * 159313 * 268982761103897324316 ≤ 10 * 2150969 * QQ + 11 * 159313 * QQ := by decide +kernel

theorem pi_good : ∀ m, 60184 ≤ m → m ≤ 2000000 → good m := by
  have I0 := inv0
  have I1 := prun_sound QQ QQ_pos _ _ _ (by exact I0) pb0
  have I2 := prun_sound QQ QQ_pos _ _ _ (by exact I1) pb1
  have I3 := prun_sound QQ QQ_pos _ _ _ (by exact I2) pb2
  have I4 := prun_sound QQ QQ_pos _ _ _ (by exact I3) pb3
  have I5 := prun_sound QQ QQ_pos _ _ _ (by exact I4) pb4
  have I6 := prun_sound QQ QQ_pos _ _ _ (by exact I5) pb5
  have I7 := prun_sound QQ QQ_pos _ _ _ (by exact I6) pb6
  have I8 := prun_sound QQ QQ_pos _ _ _ (by exact I7) pb7
  have I9 := prun_sound QQ QQ_pos _ _ _ (by exact I8) pb8
  have I10 := prun_sound QQ QQ_pos _ _ _ (by exact I9) pb9
  have I11 := prun_sound QQ QQ_pos _ _ _ (by exact I10) pb10
  have I12 := prun_sound QQ QQ_pos _ _ _ (by exact I11) pb11
  have I13 := prun_sound QQ QQ_pos _ _ _ (by exact I12) pb12
  have I14 := prun_sound QQ QQ_pos _ _ _ (by exact I13) pb13
  obtain ⟨i, hi, hgs, hn, hn11, hk, hL, hlog, hLn, hgood⟩ := I14
  dsimp only at hk hL hlog hgood
  intro m h1 h2
  by_cases hmL : m < 2150969
  · exact hgood m h1 (by omega) hmL
  · exact good_of_check QQ_pos fin14 hlog hL (by omega) (pc_le (by omega) hk)

end S68PiCert
end

open S68PiCert in
theorem solution {x : ℝ} (h1 : 60184 ≤ x) (h2 : x ≤ 2 * 10 ^ 6) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ x / (Real.log x - 1.1) := by
  have hm1 : 60184 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast h1)
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hmx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
  have hm2 : ⌊x⌋₊ ≤ 2000000 := by
    have : (⌊x⌋₊ : ℝ) ≤ 2000000 := by linarith
    exact_mod_cast this
  have hg := pi_good _ hm1 hm2
  unfold good at hg
  set m := ⌊x⌋₊
  have hm0 : (0 : ℝ) < m := by
    have : (60184 : ℝ) ≤ m := by exact_mod_cast hm1
    linarith
  have h3 := three_le_log hm1
  have hlx : Real.log m ≤ Real.log x := Real.log_le_log hm0 hmx
  have hlin : Real.log x ≤ Real.log m + (x - m) / m := by
    have := Real.log_le_sub_one_of_pos (div_pos (lt_of_lt_of_le hm0 hmx) hm0)
    rw [Real.log_div (by linarith) hm0.ne'] at this
    have e : x / m - 1 = (x - m) / m := by field_simp
    linarith
  have hp0 : (0 : ℝ) ≤ Nat.primeCounting m := Nat.cast_nonneg _
  have hpm : (Nat.primeCounting m : ℝ) ≤ m := by nlinarith
  have hfrac : (Nat.primeCounting m : ℝ) * ((x - m) / m) ≤ x - m := by
    rw [mul_div_assoc', div_le_iff₀ hm0]; nlinarith
  rw [le_div_iff₀ (by norm_num; linarith)]
  calc (Nat.primeCounting m : ℝ) * (Real.log x - 1.1)
      ≤ (Nat.primeCounting m : ℝ) * (Real.log m + (x - m) / m - 11 / 10) := by
        apply mul_le_mul_of_nonneg_left _ hp0; norm_num; linarith
    _ = (Nat.primeCounting m : ℝ) * (Real.log m - 11 / 10) + (Nat.primeCounting m : ℝ) * ((x - m) / m) := by ring
    _ ≤ m + (x - m) := by linarith
    _ = x := by ring

