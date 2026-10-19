-- Prove2me | solution 1 for FoundationsRL.FuncApprox.bilinucb_pac_bound_v2
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-16T21:14:14.434228+00:00
-- url     : https://prove2.me/submissions/1076468a-e0be-4396-8878-d52e17d54bc7

import Mathlib
import Definitions.Def_FoundationsRL_RLBasics_Core
import Definitions.Def_FoundationsRL_RLBasics_UCBVI
import Definitions.Def_FoundationsRL_FuncApprox_Core
import Definitions.Def_FoundationsRL_FuncApprox_BiLinUCB
import Definitions.Def_FoundationsRL_FuncApprox_Normalization

set_option autoImplicit false

namespace Dp51

open Finset

/-- number of `true` coordinates of a coin vector -/
def cnt {n : ℕ} (b : Fin n → Bool) : ℕ := ∑ j, if b j then 1 else 0

lemma cnt_cons {n : ℕ} (x : Bool) (b : Fin n → Bool) :
    cnt (Fin.cons x b : Fin (n + 1) → Bool) = (if x then 1 else 0) + cnt b := by
  simp only [cnt, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

lemma sum_fin_succ_fun {X : Type} [Fintype X] {T : ℕ} (g : (Fin (T + 1) → X) → ℝ) :
    ∑ f, g f = ∑ x, ∑ rest : Fin T → X, g (Fin.cons x rest) := by
  rw [← (Fin.consEquiv (fun _ : Fin (T + 1) => X)).sum_comp, Fintype.sum_prod_type]
  rfl

lemma card_coins (n : ℕ) : (∑ _b : Fin n → Bool, (1:ℝ)) = 2 ^ n := by
  simp

lemma sum_cnt (n : ℕ) : 2 * ∑ b : Fin n → Bool, (cnt b : ℝ) = n * 2 ^ n := by
  induction n with
  | zero => simp [cnt]
  | succ n ih =>
    rw [sum_fin_succ_fun]
    simp only [cnt_cons, Fintype.sum_bool, if_true, Bool.false_eq_true, if_false]
    push_cast
    rw [Finset.sum_add_distrib, card_coins]
    simp only [zero_add]
    push_cast
    rw [pow_succ]
    linarith

lemma sum_cnt_sq (n : ℕ) : 4 * ∑ b : Fin n → Bool, (cnt b : ℝ) ^ 2 = n * (n + 1) * 2 ^ n := by
  induction n with
  | zero => simp [cnt]
  | succ n ih =>
    have h1 := sum_cnt n
    rw [sum_fin_succ_fun]
    simp only [cnt_cons, Fintype.sum_bool, if_true, Bool.false_eq_true, if_false]
    push_cast
    simp only [add_sq, zero_add, one_pow, mul_one]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, card_coins, ← Finset.mul_sum]
    rw [pow_succ]
    nlinarith

/-- the second moment identity used for Markov's inequality -/
lemma sum_resid_sq (n : ℕ) (hn : 0 < n) (r : ℝ) :
    ∑ b : Fin n → Bool, (r + 1 / 2 - (cnt b : ℝ) / n) ^ 2 = 2 ^ n * (r ^ 2 + 1 / (4 * n)) := by
  have h1 := sum_cnt n
  have h2 := sum_cnt_sq n
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have e : ∀ b : Fin n → Bool, (r + 1 / 2 - (cnt b : ℝ) / n) ^ 2 =
      (r + 1 / 2) ^ 2 * 1 - (2 * (r + 1 / 2) / n) * (cnt b : ℝ) + (1 / (n:ℝ) ^ 2) * (cnt b : ℝ) ^ 2 := by
    intro b; field_simp; ring
  simp_rw [e]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum, card_coins]
  have hS1 : ∑ b : Fin n → Bool, (cnt b : ℝ) = n * 2 ^ n / 2 := by linarith
  have hS2 : ∑ b : Fin n → Bool, (cnt b : ℝ) ^ 2 = n * (n + 1) * 2 ^ n / 4 := by linarith
  rw [hS1, hS2]
  field_simp
  ring

/-- binomial counts -/
lemma card_cnt_eq (n : ℕ) : ∀ j : ℕ,
    ∑ b : Fin n → Bool, (if cnt b = j then (1:ℝ) else 0) = (n.choose j : ℝ) := by
  induction n with
  | zero =>
    intro j
    rcases j with _ | j
    · simp [cnt]
    · simp [cnt]
  | succ n ih =>
    intro j
    rw [sum_fin_succ_fun]
    simp only [cnt_cons, Fintype.sum_bool, if_true, Bool.false_eq_true, if_false, zero_add]
    rcases j with _ | j
    · have : ∀ b : Fin n → Bool, (if 1 + cnt b = 0 then (1:ℝ) else 0) = 0 := by
        intro b; rw [if_neg (by omega)]
      simp only [this, Finset.sum_const_zero, zero_add, ih 0, Nat.choose_zero_right]
    · have : ∀ b : Fin n → Bool, (if 1 + cnt b = j + 1 then (1:ℝ) else 0) =
          if cnt b = j then 1 else 0 := by
        intro b; congr 1; apply propext; omega
      simp only [this, ih j, ih (j + 1), Nat.choose_succ_succ]
      push_cast; ring

/-- central binomial lower bound `C(2N,N)^2 * 4N ≥ 16^N` -/
lemma central_sq (N : ℕ) (hN : 1 ≤ N) :
    16 ^ N ≤ 4 * N * (Nat.centralBinom N) ^ 2 := by
  induction N, hN using Nat.le_induction with
  | base => simp [Nat.centralBinom, Nat.choose]
  | succ N hN ih =>
    have key := Nat.succ_mul_centralBinom_succ N
    have h1 : (N + 1) * (4 * (N + 1) * (Nat.centralBinom (N + 1)) ^ 2) =
        16 * (2 * N + 1) ^ 2 * (Nat.centralBinom N) ^ 2 := by
      have : (N + 1) * (4 * (N + 1) * (Nat.centralBinom (N + 1)) ^ 2) =
          4 * ((N + 1) * Nat.centralBinom (N + 1)) ^ 2 := by ring
      rw [this, key]; ring
    have h2 : (N + 1) * 16 ^ (N + 1) ≤ 16 * (2 * N + 1) ^ 2 * (Nat.centralBinom N) ^ 2 := by
      have h3 : 4 * N * (N + 1) ≤ (2 * N + 1) ^ 2 := by nlinarith
      calc (N + 1) * 16 ^ (N + 1) = 16 * (N + 1) * 16 ^ N := by ring
        _ ≤ 16 * (N + 1) * (4 * N * (Nat.centralBinom N) ^ 2) := by gcongr
        _ = 16 * (4 * N * (N + 1)) * (Nat.centralBinom N) ^ 2 := by ring
        _ ≤ 16 * (2 * N + 1) ^ 2 * (Nat.centralBinom N) ^ 2 := by gcongr
    rw [← h1] at h2
    exact Nat.le_of_mul_le_mul_left h2 (by omega)

lemma central_ge (N : ℕ) (hN : 1 ≤ N) :
    (4:ℝ) ^ N ≤ 2 * Real.sqrt N * ((2 * N).choose N : ℝ) := by
  have h := central_sq N hN
  rw [Nat.centralBinom_eq_two_mul_choose] at h
  have h' : ((16:ℕ) ^ N : ℝ) ≤ ((4 * N * ((2 * N).choose N) ^ 2 : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at h'
  have hs : Real.sqrt N ^ 2 = N := Real.sq_sqrt (by positivity)
  have hsq : ((4:ℝ) ^ N) ^ 2 ≤ (2 * Real.sqrt N * ((2 * N).choose N : ℝ)) ^ 2 := by
    rw [mul_pow, mul_pow, hs, ← pow_mul, mul_comm N 2, pow_mul]
    norm_num
    linarith
  have hx : 0 ≤ (4:ℝ) ^ N := by positivity
  have hy : 0 ≤ 2 * Real.sqrt N * ((2 * N).choose N : ℝ) := by positivity
  nlinarith

/-- ratio bound: `C(2N, N+s) ≥ C(2N,N) q^s` with `q = (N-S)/(N+S)`, for `s ≤ S ≤ N` -/
lemma choose_ratio (N S : ℕ) (hS : S ≤ N) : ∀ s : ℕ, s ≤ S →
    ((2 * N).choose N : ℝ) * (((N:ℝ) - S) / (N + S)) ^ s ≤ ((2 * N).choose (N + s) : ℝ) := by
  intro s
  induction s with
  | zero => intro _; simp
  | succ s ih =>
    intro hs
    have ih' := ih (by omega)
    have hrec := Nat.choose_succ_right_eq (2 * N) (N + s)
    have rec' : ((2 * N).choose (N + s + 1) : ℝ) * (N + s + 1) =
        ((2 * N).choose (N + s) : ℝ) * (N - s) := by
      have : 2 * N - (N + s) = N - s := by omega
      rw [this] at hrec
      have h' : (((2 * N).choose (N + s + 1) * (N + s + 1) : ℕ) : ℝ) =
          (((2 * N).choose (N + s) * (N - s) : ℕ) : ℝ) := by rw [hrec]
      push_cast [Nat.cast_sub (show s ≤ N by omega)] at h'
      linarith
    have hq0 : 0 ≤ ((N:ℝ) - S) / (N + S) := by
      apply div_nonneg _ (by positivity)
      have : (S:ℝ) ≤ N := by exact_mod_cast hS
      linarith
    have hq : ((N:ℝ) - S) / (N + S) ≤ ((N:ℝ) - s) / (N + s + 1) := by
      have hsS : (s:ℝ) + 1 ≤ S := by exact_mod_cast hs
      have hSN : (S:ℝ) ≤ N := by exact_mod_cast hS
      have hS1 : (1:ℝ) ≤ S := by exact_mod_cast (show 1 ≤ S by omega)
      have hN0 : (0:ℝ) ≤ N := by positivity
      rw [div_le_div_iff₀ (by linarith) (by positivity)]
      nlinarith
    have hpos : (0:ℝ) < N + s + 1 := by positivity
    have hc : ((2 * N).choose (N + s + 1) : ℝ) = ((2 * N).choose (N + s) : ℝ) * ((N - s) / (N + s + 1)) := by
      field_simp; linarith
    rw [show N + (s + 1) = N + s + 1 by omega, hc, pow_succ, ← mul_assoc]
    have hC0 : (0:ℝ) ≤ ((2 * N).choose (N + s) : ℝ) := by positivity
    calc ((2 * N).choose N : ℝ) * (((N:ℝ) - S) / (N + S)) ^ s * (((N:ℝ) - S) / (N + S))
        ≤ ((2 * N).choose (N + s) : ℝ) * (((N:ℝ) - S) / (N + S)) := by
          gcongr
      _ ≤ ((2 * N).choose (N + s) : ℝ) * ((N - s) / (N + s + 1)) := by gcongr

/-- `1 - x ≥ exp(-2x)` for `0 ≤ x ≤ 1/2` -/
lemma one_sub_ge_exp (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) : Real.exp (-(2 * x)) ≤ 1 - x := by
  have h := Real.add_one_le_exp (2 * x)
  have hpos : 0 < Real.exp (2 * x) := Real.exp_pos _
  have hinv : Real.exp (-(2 * x)) * Real.exp (2 * x) = 1 := by
    rw [← Real.exp_add]; simp
  have : 1 ≤ (1 - x) * Real.exp (2 * x) := by nlinarith
  nlinarith

lemma q_ge (N S : ℕ) (hN : 0 < N) (hS : 4 * S ≤ N) :
    Real.exp (-(4 * S / N)) ≤ ((N:ℝ) - S) / (N + S) := by
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  have hS' : (4:ℝ) * S ≤ N := by exact_mod_cast hS
  have hS0 : (0:ℝ) ≤ S := by positivity
  have h1 := one_sub_ge_exp (2 * S / N) (by positivity)
    (by rw [div_le_iff₀ hN']; linarith)
  have e : -(2 * (2 * (S:ℝ) / N)) = -(4 * S / N) := by ring
  rw [e] at h1
  refine h1.trans ?_
  rw [le_div_iff₀ (by positivity)]
  have : (1 - 2 * (S:ℝ) / N) * (N + S) = N - S - 2 * S * S / N := by field_simp; ring
  rw [this]
  have : 0 ≤ 2 * (S:ℝ) * S / N := by positivity
  linarith

/-- the lucky-batch count lower bound for `n = 2N` coins -/
lemma anti_conc (α : ℝ) (hα : 0 < α) : ∀ᶠ N : ℕ in Filter.atTop,
    (α / 2) * Real.exp (-(4 * (2 * α + 3) ^ 2)) * 4 ^ N ≤
      ∑ b : Fin (2 * N) → Bool, (if (N:ℝ) + α * Real.sqrt N < cnt b then (1:ℝ) else 0) := by
  filter_upwards [Filter.eventually_ge_atTop (⌈(8 * α + 12) ^ 2⌉₊)] with N hN
  have hN1 : (8 * α + 12) ^ 2 ≤ (N:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hN)
  have hNpos : (1:ℝ) ≤ N := by nlinarith
  have hN0 : 0 < N := by exact_mod_cast (show (0:ℝ) < N by linarith)
  set y := Real.sqrt N with hy
  have hy2 : y ^ 2 = N := Real.sq_sqrt (by positivity)
  have hy0 : 0 ≤ y := Real.sqrt_nonneg _
  have hy1 : 8 * α + 12 ≤ y := by
    rw [hy]; apply Real.le_sqrt_of_sq_le; exact hN1
  set t0 := ⌈α * y⌉₊ with ht0
  have ht0a : α * y ≤ t0 := Nat.le_ceil _
  have ht0b : (t0:ℝ) < α * y + 1 := Nat.ceil_lt_add_one (by positivity)
  set S := 2 * t0 + 1 with hSdef
  have hSr : (S:ℝ) ≤ 2 * α * y + 3 := by rw [hSdef]; push_cast; linarith
  have h4S : 4 * S ≤ N := by
    have : (4:ℝ) * S ≤ N := by nlinarith
    exact_mod_cast this
  -- pointwise: the disjoint union of the level sets lies in the event
  set I := Finset.Icc (t0 + 1) S with hI
  have hpt : ∀ b : Fin (2 * N) → Bool,
      ∑ s ∈ I, (if cnt b = N + s then (1:ℝ) else 0) ≤
        if (N:ℝ) + α * y < cnt b then 1 else 0 := by
    intro b
    rw [Finset.sum_boole]
    split_ifs with hP
    · have : (I.filter (fun s => cnt b = N + s)).card ≤ 1 := by
        apply Finset.card_le_one.2
        intro x hx z hz
        simp only [Finset.mem_filter] at hx hz
        omega
      exact_mod_cast this
    · have : I.filter (fun s => cnt b = N + s) = ∅ := by
        apply Finset.filter_eq_empty_iff.2
        intro s hs hcs
        apply hP
        rw [hcs, hI, Finset.mem_Icc] at *
        push_cast
        have : (t0:ℝ) + 1 ≤ s := by exact_mod_cast hs.1
        linarith
      rw [this]; simp
  have hsum : ∑ s ∈ I, ((2 * N).choose (N + s) : ℝ) ≤
      ∑ b : Fin (2 * N) → Bool, (if (N:ℝ) + α * y < cnt b then (1:ℝ) else 0) := by
    calc ∑ s ∈ I, ((2 * N).choose (N + s) : ℝ)
        = ∑ s ∈ I, ∑ b : Fin (2 * N) → Bool, (if cnt b = N + s then (1:ℝ) else 0) := by
          apply Finset.sum_congr rfl; intro s _; rw [card_cnt_eq]
      _ = ∑ b : Fin (2 * N) → Bool, ∑ s ∈ I, (if cnt b = N + s then (1:ℝ) else 0) :=
          Finset.sum_comm
      _ ≤ _ := Finset.sum_le_sum (fun b _ => hpt b)
  -- each level is large
  have hSN : S ≤ N := by omega
  have hq := q_ge N S hN0 h4S
  have hq1 : ((N:ℝ) - S) / (N + S) ≤ 1 := by
    rw [div_le_one (by positivity)]; have : (0:ℝ) ≤ S := by positivity
    linarith
  have hexp : Real.exp (-(4 * (2 * α + 3) ^ 2)) ≤ (((N:ℝ) - S) / (N + S)) ^ S := by
    calc Real.exp (-(4 * (2 * α + 3) ^ 2)) ≤ Real.exp (S * (-(4 * S / N))) := by
          apply Real.exp_le_exp.2
          have hNr : (0:ℝ) < N := by linarith
          have : (S:ℝ) * S ≤ (2 * α + 3) ^ 2 * N := by
            have h1 : (S:ℝ) ≤ (2 * α + 3) * y := by nlinarith
            have h0 : (0:ℝ) ≤ S := by positivity
            calc (S:ℝ) * S ≤ ((2 * α + 3) * y) * ((2 * α + 3) * y) := by gcongr
              _ = (2 * α + 3) ^ 2 * N := by rw [← hy2]; ring
          rw [show (S:ℝ) * (-(4 * S / N)) = -(4 * (S * S) / N) by ring]
          rw [neg_le_neg_iff, div_le_iff₀ hNr]
          nlinarith
      _ = Real.exp (-(4 * S / N)) ^ S := Real.exp_nat_mul _ _
      _ ≤ (((N:ℝ) - S) / (N + S)) ^ S := by
          apply pow_le_pow_left₀ (Real.exp_pos _).le hq
  have hlev : ∀ s ∈ I, ((2 * N).choose N : ℝ) * Real.exp (-(4 * (2 * α + 3) ^ 2)) ≤
      ((2 * N).choose (N + s) : ℝ) := by
    intro s hs
    rw [hI, Finset.mem_Icc] at hs
    have hq0 : 0 ≤ ((N:ℝ) - S) / (N + S) := by
      apply div_nonneg _ (by positivity)
      have : (S:ℝ) ≤ N := by exact_mod_cast hSN
      linarith
    calc ((2 * N).choose N : ℝ) * Real.exp (-(4 * (2 * α + 3) ^ 2))
        ≤ ((2 * N).choose N : ℝ) * (((N:ℝ) - S) / (N + S)) ^ S := by gcongr
      _ ≤ ((2 * N).choose N : ℝ) * (((N:ℝ) - S) / (N + S)) ^ s :=
          mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hq0 hq1 hs.2) (by positivity)
      _ ≤ _ := choose_ratio N S hSN s hs.2
  have hcard : (I.card : ℝ) = t0 + 1 := by
    rw [hI, Nat.card_Icc]
    have : S + 1 - (t0 + 1) = t0 + 1 := by omega
    rw [this]; push_cast; ring
  have hlow : (t0 + 1 : ℝ) * (((2 * N).choose N : ℝ) * Real.exp (-(4 * (2 * α + 3) ^ 2))) ≤
      ∑ s ∈ I, ((2 * N).choose (N + s) : ℝ) := by
    rw [← hcard, ← nsmul_eq_mul]
    exact Finset.card_nsmul_le_sum _ _ _ hlev
  have hcen := central_ge N (by omega)
  rw [← hy] at hcen
  have hE0 : 0 < Real.exp (-(4 * (2 * α + 3) ^ 2)) := Real.exp_pos _
  have hypos : 0 < y := by linarith
  -- combine
  refine le_trans ?_ (hlow.trans hsum)
  have hC0 : (0:ℝ) ≤ ((2 * N).choose N : ℝ) := by positivity
  have step1 : α * y * (((2 * N).choose N : ℝ) * Real.exp (-(4 * (2 * α + 3) ^ 2))) ≤
      (t0 + 1 : ℝ) * (((2 * N).choose N : ℝ) * Real.exp (-(4 * (2 * α + 3) ^ 2))) := by
    gcongr; linarith
  refine le_trans ?_ step1
  have : (α / 2) * Real.exp (-(4 * (2 * α + 3) ^ 2)) * 4 ^ N ≤
      (α / 2) * Real.exp (-(4 * (2 * α + 3) ^ 2)) * (2 * y * ((2 * N).choose N : ℝ)) := by
    gcongr
  refine this.trans (le_of_eq ?_)
  ring

/-! ### batches of coins -/

lemma sum_batches_prod {m n : ℕ} (f : (Fin n → Bool) → ℝ) :
    ∑ c : Fin m → Fin n → Bool, ∏ i, f (c i) = (∑ b : Fin n → Bool, f b) ^ m := by
  rw [← Fintype.prod_sum (fun (_ : Fin m) (b : Fin n → Bool) => f b)]
  simp

lemma sum_batch_single {m n : ℕ} (i : Fin m) (Y : (Fin n → Bool) → ℝ) :
    ∑ c : Fin m → Fin n → Bool, Y (c i) = (∑ b : Fin n → Bool, Y b) * (2 ^ n) ^ (m - 1) := by
  classical
  have e : ∀ c : Fin m → Fin n → Bool, Y (c i) =
      ∏ j, (if j = i then Y (c j) else 1) := by
    intro c
    rw [Finset.prod_eq_single i]
    · simp
    · intro j _ hj; simp [hj]
    · simp
  have e2 : ∑ c : Fin m → Fin n → Bool, Y (c i) =
      ∏ j : Fin m, ∑ b : Fin n → Bool, (if j = i then Y b else 1) := by
    rw [Fintype.prod_sum]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [e c]
  rw [e2]
  rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i)]
  simp only [if_true]
  congr 1
  rw [Finset.prod_congr rfl (g := fun _ => (2:ℝ) ^ n)]
  · rw [Finset.prod_const, Finset.card_sdiff]
    simp
  · intro j hj
    simp only [Finset.mem_sdiff, Finset.mem_singleton] at hj
    simp [hj.2]

/-- the coin-space good-event bound: survival (Markov) and some lucky batch (independence) -/
lemma good_coins (m n k : ℕ) (hk : k ≤ m) (Y : (Fin n → Bool) → ℝ) (hY : ∀ b, 0 ≤ Y b)
    (β : ℝ) (hβ : 0 < β) (Lk : (Fin n → Bool) → Prop) [DecidablePred Lk] :
    (2 ^ n : ℝ) ^ m - k * (∑ b : Fin n → Bool, Y b) * (2 ^ n) ^ (m - 1) / β -
        ((2 ^ n : ℝ) - ∑ b : Fin n → Bool, (if Lk b then (1:ℝ) else 0)) ^ m ≤
      ∑ c : Fin m → Fin n → Bool,
        (if (∑ i : Fin m, (if i.val < k then Y (c i) else 0)) ≤ β ∧ ∃ i, Lk (c i)
          then (1:ℝ) else 0) := by
  classical
  set Z : (Fin m → Fin n → Bool) → ℝ := fun c => ∑ i : Fin m, (if i.val < k then Y (c i) else 0)
  have hZ0 : ∀ c, 0 ≤ Z c := fun c =>
    Finset.sum_nonneg (fun i _ => by split_ifs <;> simp [hY])
  have hpt : ∀ c : Fin m → Fin n → Bool,
      1 - Z c / β - ∏ i, (if Lk (c i) then (0:ℝ) else 1) ≤
        (if Z c ≤ β ∧ ∃ i, Lk (c i) then (1:ℝ) else 0) := by
    intro c
    have hzb : 0 ≤ Z c / β := div_nonneg (hZ0 c) hβ.le
    have hp0 : 0 ≤ ∏ i, (if Lk (c i) then (0:ℝ) else 1) :=
      Finset.prod_nonneg (fun i _ => by split_ifs <;> norm_num)
    split_ifs with h
    · linarith
    · rw [not_and_or] at h
      rcases h with h | h
      · have : 1 < Z c / β := by rw [lt_div_iff₀ hβ]; linarith
        linarith
      · push_neg at h
        have : ∏ i, (if Lk (c i) then (0:ℝ) else 1) = 1 := by
          apply Finset.prod_eq_one; intro i _; simp [h i]
        linarith
  have hsum := Finset.sum_le_sum (fun c (_ : c ∈ Finset.univ) => hpt c)
  refine le_trans (le_of_eq ?_) hsum
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  congr 1
  · congr 1
    · simp
    · rw [← Finset.sum_div]
      congr 1
      simp only [Z]
      rw [Finset.sum_comm]
      have : ∀ i : Fin m, ∑ c : Fin m → Fin n → Bool, (if i.val < k then Y (c i) else 0) =
          if i.val < k then (∑ b : Fin n → Bool, Y b) * (2 ^ n) ^ (m - 1) else 0 := by
        intro i
        split_ifs
        · exact sum_batch_single i Y
        · simp
      simp_rw [this]
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
      have hc : (Finset.univ.filter (fun i : Fin m => i.val < k)).card = k := by
        have : (Finset.univ.filter (fun i : Fin m => i.val < k)) =
            (Finset.range k).attachFin (fun j hj => by simp at hj; omega) := by
          ext i; simp
        rw [this, Finset.card_attachFin, Finset.card_range]
      rw [hc]; ring
  · rw [sum_batches_prod (fun b => if Lk b then (0:ℝ) else 1)]
    congr 1
    have : ∀ b : Fin n → Bool, (if Lk b then (0:ℝ) else 1) = 1 - (if Lk b then 1 else 0) := by
      intro b; split_ifs <;> norm_num
    simp_rw [this]
    rw [Finset.sum_sub_distrib, card_coins]

end Dp51


namespace Dp51

open FoundationsRL.RLBasics FoundationsRL.FuncApprox

abbrev St := Fin 4
abbrev Tr := Trajectory St Bool 2

/-- layer-1 reward (action independent): `u = 1 ↦ 1`, `w = 3 ↦ R*`, else `0` -/
noncomputable def R1 (ε : ℝ) (s : St) : ℝ := if s = 1 then 1 else if s = 3 then 1 / 2 + 2 * ε else 0

noncomputable def Pm (h : ℕ) (s : St) (a : Bool) (s' : St) : ℝ :=
  if h = 0 ∧ s = 0 ∧ a = false then (if s' = 1 ∨ s' = 2 then 1 / 2 else 0)
  else (if s' = 3 then 1 else 0)

lemma Pm_sum (h : ℕ) (s : St) (a : Bool) : ∑ s' : St, Pm h s a s' = 1 := by
  unfold Pm
  split_ifs <;> simp [Fin.sum_univ_four] <;> norm_num

noncomputable def M (ε : ℝ) : EpisodicMDP St Bool 2 where
  P := Pm
  R := fun h s _ => if h = 1 then R1 ε s else 0
  d1 := fun s => if s = 0 then 1 else 0
  P_nonneg := by intro h s a s'; unfold Pm; split_ifs <;> norm_num
  P_sum_one := Pm_sum
  d1_nonneg := by intro s; split_ifs <;> norm_num
  d1_sum_one := by simp [Fin.sum_univ_four]

/-- the over-optimistic value function -/
noncomputable def Qbad (ε : ℝ) : ℕ → St → Bool → ℝ := fun h s a =>
  if h = 0 then (if s = 0 ∧ a = false then 1 / 2 + 4 * ε else 0)
  else if h = 1 then (if s = 1 ∨ s = 2 then 1 / 2 + 4 * ε else if s = 3 then 1 / 2 + 2 * ε else 0)
  else 0

noncomputable def Qs (ε : ℝ) : ℕ → St → Bool → ℝ :=
  fun h s a => if h < 2 then Qstar (M ε) h s a else 0

noncomputable def qe (ε : ℝ) : Bool → ℕ → St → Bool → ℝ := fun q => cond q (Qbad ε) (Qs ε)

lemma d1_sum (ε : ℝ) (f : St → ℝ) : ∑ s : St, (M ε).d1 s * f s = f 0 := by
  simp [M, Fin.sum_univ_four]

lemma V2_eq (ε : ℝ) (π : Policy St Bool 2) (s : St) : V (M ε) π 2 s = 0 := by
  simp [V, valueAux]

lemma V1_eq (ε : ℝ) (π : Policy St Bool 2) (hπ : ∀ s, ∑ a : Bool, π 1 s a = 1) (s : St) :
    V (M ε) π 1 s = R1 ε s := by
  have h := hπ s
  simp only [V, valueAux]
  norm_num
  simp only [M, if_true]
  rw [Fintype.sum_bool] at h
  try simp only [Fintype.sum_bool]
  rw [← add_mul, h, one_mul]

lemma Qfun_eq (ε : ℝ) (π : Policy St Bool 2) (hπ : ∀ s, ∑ a : Bool, π 1 s a = 1) (h : ℕ)
    (s : St) (a : Bool) :
    FoundationsRL.RLBasics.Q (M ε) π h s a =
      if h = 0 then ∑ s' : St, Pm 0 s a s' * R1 ε s' else if h = 1 then R1 ε s else 0 := by
  unfold FoundationsRL.RLBasics.Q
  rcases h with _ | _ | h
  · have e : ∀ s', V (M ε) π (0 + 1) s' = R1 ε s' := fun s' => V1_eq ε π hπ s'
    simp only [show (0:ℕ) < 2 by norm_num, if_true, e]
    simp [M]
  · have e : ∀ s', V (M ε) π (0 + 1 + 1) s' = 0 := fun s' => V2_eq ε π s'
    simp only [show (0 + 1 : ℕ) < 2 by norm_num, if_true, e]
    simp [M]
  · have : ¬ (h + 1 + 1 < 2) := by omega
    simp [this]

lemma isPolicy_det (g : ℕ → St → Bool) :
    IsPolicy 2 (detPolicy (H := 2) g : Policy St Bool 2) := by
  intro h _ s
  refine ⟨fun a => by unfold detPolicy; split_ifs <;> norm_num, ?_⟩
  unfold detPolicy; cases g h s <;> simp

lemma Qstar_eq (ε : ℝ) (h : ℕ) (s : St) (a : Bool) :
    Qstar (M ε) h s a =
      if h = 0 then ∑ s' : St, Pm 0 s a s' * R1 ε s' else if h = 1 then R1 ε s else 0 := by
  unfold Qstar
  haveI : Nonempty {π : Policy St Bool 2 // IsPolicy 2 π} :=
    ⟨⟨_, isPolicy_det (fun _ _ => true)⟩⟩
  have : (fun π : {π : Policy St Bool 2 // IsPolicy 2 π} =>
      FoundationsRL.RLBasics.Q (M ε) π.1 h s a) =
      fun _ => (if h = 0 then ∑ s' : St, Pm 0 s a s' * R1 ε s' else if h = 1 then R1 ε s else 0) := by
    funext π
    exact Qfun_eq ε π.1 (fun s => (π.2 1 (by norm_num) s).2) h s a
  rw [this]
  exact ciSup_const

lemma Qs_vals (ε : ℝ) :
    Qs ε 0 0 true = 1 / 2 + 2 * ε ∧ Qs ε 0 0 false = 1 / 2 ∧
    (∀ s a, s ≠ 0 → Qs ε 0 s a = 1 / 2 + 2 * ε) ∧ (∀ s a, Qs ε 1 s a = R1 ε s) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [Qs, Qstar_eq, Pm, R1, Fin.sum_univ_four]
  · simp [Qs, Qstar_eq, Pm, R1, Fin.sum_univ_four]
  · intro s a hs
    simp [Qs, Qstar_eq, Pm, R1, Fin.sum_univ_four, hs]
  · intro s a
    simp [Qs, Qstar_eq]

lemma argmax_unique {α : Type*} (f : α → ℝ) (l : List α) (x : α) (hx : x ∈ l)
    (h : ∀ y ∈ l, y ≠ x → f y < f x) : l.argmax f = some x := by
  rcases hm : l.argmax f with _ | m
  · rw [List.argmax_eq_none] at hm; simp [hm] at hx
  · have hmem : m ∈ l := List.argmax_mem hm
    have hle := List.le_of_mem_argmax hx hm
    by_contra hne
    have := h m hmem (fun e => hne (by rw [e]))
    linarith

lemma greedy_bad0 (ε : ℝ) (hε : 0 < ε) : greedyPolicy (qe ε) true 0 0 = false := by
  unfold greedyPolicy
  rw [argmax_unique _ _ false (by simp)]
  · rfl
  · intro y _ hy
    cases y
    · exact absurd rfl hy
    · simp [qe, Qbad]; linarith

lemma greedy_star0 (ε : ℝ) (hε : 0 < ε) : greedyPolicy (qe ε) false 0 0 = true := by
  unfold greedyPolicy
  rw [argmax_unique _ _ true (by simp)]
  · rfl
  · intro y _ hy
    cases y
    · simp only [qe, cond_false]
      rw [(Qs_vals ε).1, (Qs_vals ε).2.1]; linarith
    · exact absurd rfl hy

lemma init_bad (ε : ℝ) (hε : 0 < ε) : initValue (M ε) (qe ε) true = 1 / 2 + 4 * ε := by
  unfold initValue
  rw [d1_sum, greedy_bad0 ε hε]
  simp [qe, Qbad]

lemma init_star (ε : ℝ) (hε : 0 < ε) : initValue (M ε) (qe ε) false = 1 / 2 + 2 * ε := by
  unfold initValue
  rw [d1_sum, greedy_star0 ε hε]
  simp only [qe, cond_false]
  exact (Qs_vals ε).1

lemma Vstar0 (ε : ℝ) (hε : 0 < ε) : Vstar (M ε) 0 0 = 1 / 2 + 2 * ε := by
  unfold Vstar
  have e1 : Qstar (M ε) 0 0 true = 1 / 2 + 2 * ε := by
    have := (Qs_vals ε).1; simpa [Qs] using this
  have e2 : Qstar (M ε) 0 0 false = 1 / 2 := by
    have := (Qs_vals ε).2.1; simpa [Qs] using this
  apply le_antisymm
  · apply ciSup_le; intro a; cases a
    · rw [e2]; linarith
    · rw [e1]
  · have := le_ciSup (Finite.bddAbove_range (fun a : Bool => Qstar (M ε) 0 0 a)) true
    rw [e1] at this; exact this

lemma Vbad0 (ε : ℝ) (hε : 0 < ε) :
    V (M ε) (detPolicy (greedyPolicy (qe ε) true) : Policy St Bool 2) 0 0 = 1 / 2 := by
  have hπ : ∀ s, ∑ a : Bool, (detPolicy (greedyPolicy (qe ε) true) : Policy St Bool 2) 1 s a = 1 :=
    fun s => ((isPolicy_det _) 1 (by norm_num) s).2
  have hV1 := V1_eq ε _ hπ
  simp only [V, valueAux] at hV1 ⊢
  norm_num at hV1 ⊢
  simp only [hV1]
  simp [detPolicy, greedy_bad0 ε hε, M, Pm, R1, Fin.sum_univ_four]

lemma gap_val (ε : ℝ) (hε : 0 < ε) :
    (∑ s : St, (M ε).d1 s * Vstar (M ε) 0 s) -
      (∑ s : St, (M ε).d1 s *
        V (M ε) (detPolicy (greedyPolicy (qe ε) true) : Policy St Bool 2) 0 s) = 2 * ε := by
  rw [d1_sum, d1_sum, Vstar0 ε hε, Vbad0 ε hε]; ring

/-! ### hypotheses of the target statement -/

lemma rewards_norm (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 16) : RewardsNormalized (M ε) := by
  constructor
  · intro h _ s a
    simp only [M, R1]
    constructor <;> split_ifs <;> linarith
  · intro τ _
    have : ∑ h ∈ Finset.range 2, (M ε).R h (stateAt τ h) (actionAt τ h) = R1 ε (stateAt τ 1) := by
      simp [Finset.sum_range_succ, M]
    rw [this]; unfold R1; split_ifs <;> linarith

lemma normalized (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 16) : IsNormalizedValueClass 2 (qe ε) := by
  intro Qf h hh s a
  rcases h with _ | _ | h
  · cases Qf
    · simp only [qe, cond_false]
      by_cases hs : s = 0
      · subst hs; cases a
        · rw [(Qs_vals ε).2.1]; constructor <;> norm_num
        · rw [(Qs_vals ε).1]; constructor <;> linarith
      · rw [(Qs_vals ε).2.2.1 s a hs]; constructor <;> linarith
    · simp only [qe, cond_true, Qbad]
      constructor <;> split_ifs <;> linarith
  · cases Qf
    · simp only [qe, cond_false]
      rw [(Qs_vals ε).2.2.2 s a]
      simp only [R1]; constructor <;> split_ifs <;> linarith
    · simp only [qe, cond_true, Qbad]
      constructor <;> split_ifs <;> linarith
  · omega

/-- `stateDist` is a probability vector for valid policies -/
lemma stateDist_prob (ε : ℝ) (π : Policy St Bool 2) (hπ : IsPolicy 2 π) (s0 : St) :
    ∀ h, h < 2 → (∀ s, 0 ≤ stateDist (M ε) π s0 h s) ∧ ∑ s, stateDist (M ε) π s0 h s = 1 := by
  intro h hh
  induction h with
  | zero =>
    refine ⟨fun s => by simp only [stateDist]; split_ifs <;> norm_num, ?_⟩
    simp [stateDist]
  | succ h ih =>
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    refine ⟨fun s => ?_, ?_⟩
    · simp only [stateDist]
      apply Finset.sum_nonneg; intro sp _
      apply mul_nonneg (ih1 sp)
      apply Finset.sum_nonneg; intro a _
      exact mul_nonneg ((hπ h (by omega) sp).1 a) ((M ε).P_nonneg _ _ _ _)
    · simp only [stateDist]
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum]
      have : ∀ sp, ∑ a : Bool, ∑ s, π h sp a * (M ε).P h sp a s = 1 := by
        intro sp
        simp_rw [← Finset.mul_sum, (M ε).P_sum_one, mul_one]
        exact (hπ h (by omega) sp).2
      simp_rw [Finset.sum_comm (γ := St), this, mul_one]
      exact ih2

lemma layerExp_abs_le (ε : ℝ) (π : Policy St Bool 2) (hπ : IsPolicy 2 π) (h : ℕ) (hh : h < 2)
    (f : St → Bool → ℝ) (hf : ∀ s a, |f s a| ≤ 1) :
    |layerStateActionExp (M ε) π h f| ≤ 1 := by
  unfold layerStateActionExp
  rw [d1_sum]
  obtain ⟨h1, h2⟩ := stateDist_prob ε π hπ 0 h hh
  calc |∑ s, stateDist (M ε) π 0 h s * ∑ a, π h s a * f s a|
      ≤ ∑ s, |stateDist (M ε) π 0 h s * ∑ a, π h s a * f s a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s, stateDist (M ε) π 0 h s * 1 := by
        apply Finset.sum_le_sum; intro s _
        rw [abs_mul, abs_of_nonneg (h1 s)]
        apply mul_le_mul_of_nonneg_left _ (h1 s)
        calc |∑ a, π h s a * f s a| ≤ ∑ a, |π h s a * f s a| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ a, π h s a * 1 := by
              apply Finset.sum_le_sum; intro a _
              rw [abs_mul, abs_of_nonneg ((hπ h hh s).1 a)]
              exact mul_le_mul_of_nonneg_left (hf s a) ((hπ h hh s).1 a)
          _ = 1 := by rw [← Finset.sum_mul, (hπ h hh s).2, one_mul]
    _ = 1 := by rw [← Finset.sum_mul, h2, one_mul]

lemma resid_Qs_zero (ε : ℝ) (π : Policy St Bool 2) (h : ℕ) :
    bellmanResidual (M ε) π h (qe ε false) = 0 := by
  unfold bellmanResidual
  have : (fun s a => qe ε false h s a - ((M ε).R h s a + ∑ s' : St, (M ε).P h s a s' *
      (if h + 1 < 2 then ⨆ a' : Bool, qe ε false (h + 1) s' a' else 0))) =
      fun (_ : St) (_ : Bool) => (0 : ℝ) := by
    funext s a
    rcases h with _ | _ | h
    · simp only [qe, cond_false, Qs, Qstar_eq]
      simp [M]
    · simp only [qe, cond_false, Qs, Qstar_eq]
      simp [M]
    · simp [qe, Qs, M]
  rw [this]
  simp [layerStateActionExp]

lemma resid_bad_bound (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 16) (h : ℕ) (hh : h < 2) (s : St)
    (a : Bool) :
    |qe ε true h s a - ((M ε).R h s a + ∑ s' : St, (M ε).P h s a s' *
      (if h + 1 < 2 then ⨆ a' : Bool, qe ε true (h + 1) s' a' else 0))| ≤ 1 := by
  rcases h with _ | _ | h
  · have hc : ∀ s' : St, (⨆ a' : Bool, qe ε true (0 + 1) s' a') =
        (if s' = 1 ∨ s' = 2 then 1 / 2 + 4 * ε else if s' = 3 then 1 / 2 + 2 * ε else 0) := by
      intro s'; simp [qe, Qbad]
    simp only [show (0 + 1 : ℕ) < 2 by norm_num, if_true, hc]
    rw [abs_le]
    fin_cases s <;> cases a <;> simp [qe, Qbad, M, Pm, Fin.sum_univ_four] <;>
      constructor <;> norm_num <;> linarith
  · simp only [show ¬ (0 + 1 + 1 < 2) by norm_num, if_false]
    rw [abs_le]
    fin_cases s <;> cases a <;> simp [qe, Qbad, M, R1] <;> constructor <;> norm_num <;> linarith
  · omega

lemma rank1 (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 16) :
    ∃ (X : Policy St Bool 2 → ℕ → Fin 1 → ℝ) (W : (ℕ → St → Bool → ℝ) → ℕ → Fin 1 → ℝ),
      (∀ π, IsPolicy 2 π → ∀ Qf : Bool, ∀ h : ℕ, h < 2 →
          bellmanResidual (M ε) π h (qe ε Qf) = ∑ j : Fin 1, X π h j * W (qe ε Qf) h j) ∧
      (∀ π, IsPolicy 2 π → ∀ h : ℕ, h < 2 → ∑ j : Fin 1, (X π h j) ^ 2 ≤ 1) ∧
      (∀ Qf : Bool, ∀ h : ℕ, h < 2 → ∑ j : Fin 1, (W (qe ε Qf) h j) ^ 2 ≤ 1) := by
  classical
  refine ⟨fun π h _ => bellmanResidual (M ε) π h (qe ε true),
    fun Q _ _ => if Q = qe ε true then 1 else 0, ?_, ?_, ?_⟩
  · intro π _ Qf h _
    simp only [Fin.sum_univ_one]
    cases Qf
    · by_cases e : qe ε false = qe ε true
      · rw [if_pos e, e, mul_one]
      · rw [if_neg e, mul_zero, resid_Qs_zero]
    · simp
  · intro π hπ h hh
    simp only [Fin.sum_univ_one]
    rw [sq_le_one_iff_abs_le_one]
    exact layerExp_abs_le ε π hπ h hh _ (fun s a => resid_bad_bound ε hε hε' h hh s a)
  · intro Qf h _
    simp only [Fin.sum_univ_one]
    split_ifs <;> norm_num

/-! ### Part B: BiLinUCB on canonical histories -/


lemma cnt_cast {n : ℕ} (b : Fin n → Bool) : (cnt b : ℝ) = ∑ j, (if b j then (1:ℝ) else 0) := by
  simp [cnt, Nat.cast_sum, Nat.cast_ite]

def s1 (b : Bool) : St := if b then 1 else 2

noncomputable def τc (ε : ℝ) (b : Bool) : Tr :=
  (0, (Fin.cons (false, s1 b) (Fin.cons (greedyPolicy (qe ε) true 1 (s1 b), (3 : St)) finZeroElim) :
    Fin 2 → Bool × St))

lemma trajProb_mk (ε : ℝ) (π : Policy St Bool 2) (s : St) (x0 x1 : Bool × St) :
    trajProb (M ε) π (s, (Fin.cons x0 (Fin.cons x1 finZeroElim) : Fin 2 → Bool × St)) =
      (M ε).d1 s * ((π 0 s x0.1 * (M ε).P 0 s x0.1 x0.2) *
        (π 1 x0.2 x1.1 * (M ε).P 1 x0.2 x1.1 x1.2)) := by
  unfold trajProb
  rw [Fin.prod_univ_two]
  rfl

lemma ret_mk (ε : ℝ) (s : St) (x0 x1 : Bool × St) :
    (∑ h ∈ Finset.range 2, (M ε).R h (stateAt ((s, (Fin.cons x0 (Fin.cons x1 finZeroElim) :
      Fin 2 → Bool × St)) : Tr) h) (actionAt ((s, (Fin.cons x0 (Fin.cons x1 finZeroElim) :
      Fin 2 → Bool × St)) : Tr) h)) = R1 ε x0.2 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  show (M ε).R 0 s _ + (M ε).R 1 x0.2 _ = R1 ε x0.2
  simp [M]

lemma tp_bad (ε : ℝ) (hε : 0 < ε) (b : Bool) :
    trajProb (M ε) (detPolicy (greedyPolicy (qe ε) true)) (τc ε b) = 1 / 2 := by
  unfold τc
  rw [trajProb_mk]
  simp only [detPolicy, greedy_bad0 ε hε, if_true]
  cases b <;> simp [M, Pm, s1]

lemma ret_c (ε : ℝ) (b : Bool) :
    (∑ h ∈ Finset.range 2, (M ε).R h (stateAt (τc ε b) h) (actionAt (τc ε b) h)) =
      if b then 1 else 0 := by
  unfold τc
  rw [ret_mk]
  cases b <;> simp [R1, s1]

lemma res0_c (ε : ℝ) (b : Bool) :
    qe ε true 0 (stateAt (τc ε b) 0) (actionAt (τc ε b) 0) -
        (M ε).R 0 (stateAt (τc ε b) 0) (actionAt (τc ε b) 0) -
        (if 0 + 1 < 2 then ⨆ a' : Bool, qe ε true (0 + 1) (nextStateAt (τc ε b) 0) a' else 0) = 0 := by
  show qe ε true 0 0 false - (M ε).R 0 0 false -
      (if 0 + 1 < 2 then ⨆ a' : Bool, qe ε true (0 + 1) (s1 b) a' else 0) = 0
  cases b <;> simp [qe, Qbad, M, s1]

lemma res1_c (ε : ℝ) (b : Bool) :
    qe ε true 1 (stateAt (τc ε b) 1) (actionAt (τc ε b) 1) -
        (M ε).R 1 (stateAt (τc ε b) 1) (actionAt (τc ε b) 1) -
        (if 1 + 1 < 2 then ⨆ a' : Bool, qe ε true (1 + 1) (nextStateAt (τc ε b) 1) a' else 0) =
      1 / 2 + 4 * ε - (if b then 1 else 0) := by
  show qe ε true 1 (s1 b) _ - (M ε).R 1 (s1 b) _ - _ = _
  cases b <;> simp [qe, Qbad, M, s1, R1] <;> ring

lemma batch_ofFn {T : ℕ} (hist : Fin T → Tr) (n i : ℕ) (h : i * n + n ≤ T) :
    batch (List.ofFn hist) n i =
      List.ofFn (fun j : Fin n => hist ⟨i * n + j, Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.2 _) h⟩) := by
  unfold batch
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, List.length_ofFn]
    generalize i * n = q at h ⊢
    omega
  · intro j h1 h2
    simp [List.getElem_take, List.getElem_drop, List.getElem_ofFn]

lemma batch_take (l : List Tr) (n i L : ℕ) (h : i * n + n ≤ L) :
    batch (l.take L) n i = batch l n i := by
  unfold batch
  rw [List.drop_take, List.take_take]
  congr 1
  generalize i * n = q at h ⊢
  omega

lemma res_take (ε : ℝ) (l : List Tr) (n hh i L : ℕ) (h : i * n + n ≤ L) (Qf : Bool) :
    residualEst (M ε) (qe ε) (l.take L) n hh i Qf = residualEst (M ε) (qe ε) l n hh i Qf := by
  unfold residualEst; rw [batch_take l n i L h]

lemma res0_batch (ε : ℝ) (l : List Tr) (n i : ℕ) (cb : Fin n → Bool)
    (hb : batch l n i = List.ofFn (fun j => τc ε (cb j))) :
    residualEst (M ε) (qe ε) l n 0 i true = 0 := by
  unfold residualEst
  rw [hb, List.map_ofFn, List.sum_ofFn]
  simp only [Function.comp_apply, res0_c, Finset.sum_const_zero, zero_div]

lemma res1_batch (ε : ℝ) (l : List Tr) (n i : ℕ) (hn : 0 < n) (cb : Fin n → Bool)
    (hb : batch l n i = List.ofFn (fun j => τc ε (cb j))) :
    residualEst (M ε) (qe ε) l n 1 i true = 4 * ε + 1 / 2 - (cnt cb : ℝ) / n := by
  unfold residualEst
  rw [hb, List.map_ofFn, List.sum_ofFn]
  simp only [Function.comp_apply, res1_c]
  rw [Finset.sum_sub_distrib, cnt_cast]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  field_simp
  ring

lemma emp_batch (ε : ℝ) (l : List Tr) (n i : ℕ) (cb : Fin n → Bool)
    (hb : batch l n i = List.ofFn (fun j => τc ε (cb j))) :
    empValue (M ε) l n i = (cnt cb : ℝ) / n := by
  unfold empValue
  rw [hb, List.map_ofFn, List.sum_ofFn]
  simp only [Function.comp_apply, ret_c]
  rw [cnt_cast]

lemma bestQ_true (ε : ℝ) (hε : 0 < ε) (l : List Tr) (n : ℕ) (β : ℝ) (k : ℕ)
    (hmem : true ∈ confSet (M ε) (qe ε) l n β k) : bestQ (M ε) (qe ε) l n β k = true := by
  unfold bestQ
  rw [argmax_unique _ _ true (Finset.mem_toList.2 hmem)]
  · rfl
  · intro y _ hy
    cases y
    · rw [init_bad ε hε, init_star ε hε]; linarith
    · exact absurd rfl hy

lemma learner_eq (ε : ℝ) (n : ℕ) (β : ℝ) {T : ℕ} (hist : Fin T → Tr) (t : ℕ) (ht : t ≤ T) :
    biLinUCBLearner (M ε) (qe ε) n β ((List.ofFn hist).take t) =
      detPolicy (greedyPolicy (qe ε)
        (bestQ (M ε) (qe ε) ((List.ofFn hist).take (t / n * n)) n β (t / n))) := by
  unfold biLinUCBLearner iterPolicy
  rw [List.length_take, List.length_ofFn, min_eq_left ht, List.take_take,
    min_eq_left (Nat.div_mul_le_self t n)]

lemma star_ret (ε : ℝ) (hε : 0 < ε) (τ : Tr)
    (h : trajProb (M ε) (detPolicy (greedyPolicy (qe ε) false)) τ ≠ 0) :
    (∑ h ∈ Finset.range 2, (M ε).R h (stateAt τ h) (actionAt τ h)) = 1 / 2 + 2 * ε := by
  obtain ⟨s, f⟩ := τ
  have hf : f = (Fin.cons (f 0) (Fin.cons (f 1) finZeroElim) : Fin 2 → Bool × St) := by
    funext i; fin_cases i <;> rfl
  rw [hf] at h ⊢
  rw [trajProb_mk] at h
  rw [ret_mk]
  have h1 := left_ne_zero_of_mul h
  have h2 := right_ne_zero_of_mul h
  have h3 := left_ne_zero_of_mul h2
  have hπ0 := left_ne_zero_of_mul h3
  have hP0 := right_ne_zero_of_mul h3
  have hs : s = 0 := by
    by_contra hs; apply h1; simp [M, hs]
  subst hs
  have ha : (f 0).1 = true := by
    by_contra ha; apply hπ0
    simp only [detPolicy, greedy_star0 ε hε]
    rw [if_neg ha]
  have hs1 : (f 0).2 = 3 := by
    by_contra hs1; apply hP0
    simp only [M, Pm, ha]
    simp [hs1]
  rw [hs1]; simp [R1]

/-! ### Part C: probability bookkeeping -/

lemma historyProb_cons (L : Learner St Bool 2) (ε : ℝ) {T : ℕ} (x : Tr) (rest : Fin T → Tr) :
    historyProb (M ε) L (Fin.cons x rest : Fin (T + 1) → Tr) =
      trajProb (M ε) (L []) x * historyProb (M ε) (fun h => L (x :: h)) rest := by
  unfold historyProb
  rw [Fin.prod_univ_succ]
  simp [List.ofFn_succ]

lemma sum_fin_succ_fun' {X : Type} [Fintype X] {T : ℕ} (g : (Fin (T + 1) → X) → ℝ) :
    ∑ f, g f = ∑ x, ∑ rest : Fin T → X, g (Fin.cons x rest) := by
  rw [← (Fin.consEquiv (fun _ : Fin (T + 1) => X)).sum_comp, Fintype.sum_prod_type]
  rfl

lemma traj_sum (ε : ℝ) (π : Policy St Bool 2) (hπ : ∀ h s, ∑ a : Bool, π h s a = 1) :
    ∑ τ : Tr, trajProb (M ε) π τ = 1 := by
  rw [Fintype.sum_prod_type]
  have key : ∀ s : St, ∑ f : Fin 2 → Bool × St, trajProb (M ε) π (s, f) =
      ∑ p : (Bool × St) × (Bool × St), (M ε).d1 s * ((π 0 s p.1.1 * (M ε).P 0 s p.1.1 p.1.2) *
        (π 1 p.1.2 p.2.1 * (M ε).P 1 p.1.2 p.2.1 p.2.2)) := by
    intro s
    rw [← (piFinTwoEquiv (fun _ => Bool × St)).symm.sum_comp]
    apply Finset.sum_congr rfl; intro p _
    exact trajProb_mk ε π s p.1 p.2
  simp_rw [key]
  have i1 : ∀ s1 : St, ∑ x1 : Bool × St, π 1 s1 x1.1 * (M ε).P 1 s1 x1.1 x1.2 = 1 := by
    intro s1; rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, (M ε).P_sum_one, mul_one]; exact hπ 1 s1
  have i0 : ∀ s : St, ∑ x0 : Bool × St, π 0 s x0.1 * (M ε).P 0 s x0.1 x0.2 = 1 := by
    intro s; rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, (M ε).P_sum_one, mul_one]; exact hπ 0 s
  have : ∀ s : St, ∑ p : (Bool × St) × (Bool × St), (M ε).d1 s * ((π 0 s p.1.1 *
      (M ε).P 0 s p.1.1 p.1.2) * (π 1 p.1.2 p.2.1 * (M ε).P 1 p.1.2 p.2.1 p.2.2)) = (M ε).d1 s := by
    intro s
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, i1, mul_one, i0, mul_one]
  simp_rw [this]
  exact (M ε).d1_sum_one

lemma mass (ε : ℝ) : ∀ (T : ℕ) (L : Learner St Bool 2),
    (∀ l, ∑ τ : Tr, trajProb (M ε) (L l) τ = 1) →
    ∑ hist : Fin T → Tr, historyProb (M ε) L hist = 1 := by
  intro T
  induction T with
  | zero => intro L _; simp [historyProb]
  | succ T ih =>
    intro L hL
    rw [sum_fin_succ_fun']
    simp_rw [historyProb_cons, ← Finset.mul_sum]
    simp_rw [ih _ (fun l => hL _), mul_one]
    exact hL []

lemma cons_castLE {X : Type} {N T : ℕ} (h : N + 1 ≤ T + 1) (x : X) (rest : Fin T → X) :
    (fun i : Fin (N + 1) => (Fin.cons x rest : Fin (T + 1) → X) (Fin.castLE h i)) =
      Fin.cons x (fun j : Fin N => rest (Fin.castLE (by omega) j)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · have : Fin.castLE h (0 : Fin (N + 1)) = 0 := by ext; simp
    rw [this]; simp
  · have : Fin.castLE h j.succ = (Fin.castLE (by omega) j : Fin T).succ := by ext; simp
    rw [this]; simp

lemma prefix_sum (ε : ℝ) : ∀ (N T : ℕ) (hNT : N ≤ T) (L : Learner St Bool 2)
    (_hL : ∀ l, ∑ τ : Tr, trajProb (M ε) (L l) τ = 1) (G : (Fin N → Tr) → Prop) [DecidablePred G],
    ∑ hist : Fin T → Tr, (if G (fun i => hist (Fin.castLE hNT i)) then historyProb (M ε) L hist else 0) =
      ∑ g : Fin N → Tr, (if G g then historyProb (M ε) L g else 0) := by
  intro N
  induction N with
  | zero =>
    intro T hNT L hL G _
    have hsub : ∀ f g : Fin 0 → Tr, f = g := fun f g => funext (fun i => i.elim0)
    have e : ∀ hist : Fin T → Tr, (fun i => hist (Fin.castLE hNT i)) = (finZeroElim : Fin 0 → Tr) :=
      fun hist => hsub _ _
    simp_rw [e]
    rw [Fintype.sum_eq_single (finZeroElim : Fin 0 → Tr) (fun g hg => absurd (hsub g _) hg)]
    split_ifs
    · rw [mass ε T L hL]; simp [historyProb]
    · simp
  | succ N ih =>
    intro T hNT L hL G _
    obtain ⟨T', rfl⟩ : ∃ T', T = T' + 1 := ⟨T - 1, by omega⟩
    rw [sum_fin_succ_fun', sum_fin_succ_fun']
    apply Finset.sum_congr rfl; intro x _
    simp_rw [cons_castLE hNT x, historyProb_cons]
    have := ih T' (by omega) (fun h => L (x :: h)) (fun l => hL _) (fun g => G (Fin.cons x g))
    have e1 : ∀ rest : Fin T' → Tr, (if G (Fin.cons x (fun j : Fin N => rest (Fin.castLE (by omega) j)))
        then trajProb (M ε) (L []) x * historyProb (M ε) (fun h => L (x :: h)) rest else 0) =
        trajProb (M ε) (L []) x * (if G (Fin.cons x (fun j : Fin N => rest (Fin.castLE (by omega) j)))
        then historyProb (M ε) (fun h => L (x :: h)) rest else 0) := by
      intro rest; split_ifs <;> simp
    have e2 : ∀ g : Fin N → Tr, (if G (Fin.cons x g)
        then trajProb (M ε) (L []) x * historyProb (M ε) (fun h => L (x :: h)) g else 0) =
        trajProb (M ε) (L []) x * (if G (Fin.cons x g)
        then historyProb (M ε) (fun h => L (x :: h)) g else 0) := by
      intro g; split_ifs <;> simp
    simp_rw [e1, e2, ← Finset.mul_sum]
    rw [this]

lemma learner_valid (ε : ℝ) (n : ℕ) (β : ℝ) (l : List Tr) :
    ∑ τ : Tr, trajProb (M ε) (biLinUCBLearner (M ε) (qe ε) n β l) τ = 1 := by
  apply traj_sum
  intro h s
  simp only [biLinUCBLearner, iterPolicy, detPolicy]
  generalize greedyPolicy (qe ε) _ h s = g
  cases g <;> simp

lemma hp_nonneg (ε : ℝ) (n : ℕ) (β : ℝ) {T : ℕ} (hist : Fin T → Tr) :
    0 ≤ historyProb (M ε) (biLinUCBLearner (M ε) (qe ε) n β) hist := by
  unfold historyProb
  apply Finset.prod_nonneg; intro t _
  unfold trajProb
  apply mul_nonneg ((M ε).d1_nonneg _)
  apply Finset.prod_nonneg; intro i _
  apply mul_nonneg _ ((M ε).P_nonneg _ _ _ _)
  simp only [biLinUCBLearner, iterPolicy, detPolicy]
  split_ifs <;> norm_num

/-! ### Part B2: canonical prefixes -/

/-- the first `m` batches of `hist` are the canonical bad trajectories of the coins `c` -/
def CanonPre (ε : ℝ) {m n T : ℕ} (c : Fin m → Fin n → Bool) (hist : Fin T → Tr) : Prop :=
  ∀ (i j : ℕ) (hi : i < m) (hj : j < n) (h : i * n + j < T),
    hist ⟨i * n + j, h⟩ = τc ε (c ⟨i, hi⟩ ⟨j, hj⟩)

lemma batch_canon (ε : ℝ) {m n T : ℕ} (c : Fin m → Fin n → Bool) (hist : Fin T → Tr)
    (hmT : m * n ≤ T) (hc : CanonPre ε c hist) (i : ℕ) (hi : i < m) :
    batch (List.ofFn hist) n i = List.ofFn (fun j => τc ε (c ⟨i, hi⟩ j)) := by
  have hle : i * n + n ≤ T := by
    calc i * n + n = (i + 1) * n := by ring
      _ ≤ m * n := Nat.mul_le_mul_right n hi
      _ ≤ T := hmT
  rw [batch_ofFn hist n i hle]
  congr 1; funext j
  exact hc i j hi j.2 _

noncomputable def Ysq (ε : ℝ) {n : ℕ} (b : Fin n → Bool) : ℝ := (4 * ε + 1 / 2 - (cnt b : ℝ) / n) ^ 2

/-- survival of `Qbad` through the first `m - 1` batches (Part D's form) -/
def Surv (ε β : ℝ) {m n : ℕ} (c : Fin m → Fin n → Bool) : Prop :=
  (∑ i : Fin m, (if i.val < m - 1 then Ysq ε (c i) else 0)) ≤ β

lemma surv_range (ε β : ℝ) {m n : ℕ} (c : Fin m → Fin n → Bool) (hs : Surv ε β c) (k : ℕ)
    (hk : k ≤ m - 1) :
    ∑ i ∈ Finset.range k, (if h : i < m then Ysq ε (c ⟨i, h⟩) else 0) ≤ β := by
  refine le_trans ?_ hs
  set g : ℕ → ℝ := fun i => if h : i < m then Ysq ε (c ⟨i, h⟩) else 0 with hg
  set f : ℕ → ℝ := fun i => if i < m - 1 then g i else 0 with hf
  have e : ∑ i : Fin m, (if i.val < m - 1 then Ysq ε (c i) else 0) = ∑ i ∈ Finset.range m, f i := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl; intro i _
    simp only [hf, hg, dif_pos i.2]
  rw [e]
  have hg0 : ∀ i, 0 ≤ g i := by
    intro i; simp only [hg]; split_ifs
    · exact sq_nonneg _
    · exact le_rfl
  have e2 : ∑ i ∈ Finset.range k, g i = ∑ i ∈ Finset.range k, f i := by
    apply Finset.sum_congr rfl; intro i hi
    have : i < m - 1 := lt_of_lt_of_le (Finset.mem_range.1 hi) hk
    simp only [hf, if_pos this]
  rw [e2]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro x hx; rw [Finset.mem_range] at hx ⊢; omega
  · intro i _ _; simp only [hf]; split_ifs
    · exact hg0 i
    · exact le_rfl

lemma bestQ_canon (ε : ℝ) (hε : 0 < ε) {m n T : ℕ} (hn : 0 < n) (c : Fin m → Fin n → Bool)
    (hist : Fin T → Tr) (hmT : m * n ≤ T) (hc : CanonPre ε c hist) (β : ℝ) (hβ : 0 ≤ β)
    (hs : Surv ε β c) (k : ℕ) (hk : k < m) :
    bestQ (M ε) (qe ε) ((List.ofFn hist).take (k * n)) n β k = true := by
  apply bestQ_true ε hε
  unfold confSet
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hres : ∀ hh i, i ∈ Finset.range k →
      residualEst (M ε) (qe ε) ((List.ofFn hist).take (k * n)) n hh i true =
        residualEst (M ε) (qe ε) (List.ofFn hist) n hh i true := by
    intro hh i hi
    apply res_take
    have : i + 1 ≤ k := Finset.mem_range.1 hi
    calc i * n + n = (i + 1) * n := by ring
      _ ≤ k * n := Nat.mul_le_mul_right n this
  intro h
  match h with
  | ⟨0, _⟩ =>
    have : ∀ i ∈ Finset.range k,
        (residualEst (M ε) (qe ε) ((List.ofFn hist).take (k * n)) n 0 i true) ^ 2 = 0 := by
      intro i hi
      have him : i < m := lt_trans (Finset.mem_range.1 hi) hk
      rw [hres 0 i hi, res0_batch ε _ n i _ (batch_canon ε c hist hmT hc i him)]
      simp
    rw [Finset.sum_congr rfl this]; simp [hβ]
  | ⟨1, _⟩ =>
    have : ∀ i ∈ Finset.range k,
        (residualEst (M ε) (qe ε) ((List.ofFn hist).take (k * n)) n 1 i true) ^ 2 =
          (if h : i < m then Ysq ε (c ⟨i, h⟩) else 0) := by
      intro i hi
      have him : i < m := lt_trans (Finset.mem_range.1 hi) hk
      rw [hres 1 i hi, res1_batch ε _ n i hn _ (batch_canon ε c hist hmT hc i him), dif_pos him]
      rfl
    rw [Finset.sum_congr rfl this]
    exact surv_range ε β c hs k (by omega)

lemma hp_canon (ε : ℝ) (hε : 0 < ε) {m n : ℕ} (hn : 0 < n) (c : Fin m → Fin n → Bool)
    (hist : Fin (m * n) → Tr) (hc : CanonPre ε c hist) (β : ℝ) (hβ : 0 ≤ β) (hs : Surv ε β c) :
    historyProb (M ε) (biLinUCBLearner (M ε) (qe ε) n β) hist = (1 / 2) ^ (m * n) := by
  unfold historyProb
  rw [Finset.prod_congr rfl (g := fun _ => (1 / 2 : ℝ)), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  intro t _
  have hi : t.val / n < m := Nat.div_lt_of_lt_mul (lt_of_lt_of_eq t.2 (mul_comm m n))
  rw [learner_eq ε n β hist t.val t.2.le, bestQ_canon ε hε hn c hist le_rfl hc β hβ hs _ hi]
  have ht : hist t = τc ε (c ⟨t.val / n, hi⟩ ⟨t.val % n, Nat.mod_lt _ hn⟩) := by
    rw [← hc (t.val / n) (t.val % n) hi (Nat.mod_lt _ hn)
      (by rw [Nat.div_add_mod']; exact t.2)]
    congr 1; exact Fin.ext (Nat.div_add_mod' _ _).symm
  rw [ht, tp_bad ε hε]

lemma not_succ (ε : ℝ) (hε : 0 < ε) {m n K : ℕ} (hn : 0 < n) (hmK : m ≤ K)
    (c : Fin m → Fin n → Bool) (hist : Fin (K * n) → Tr) (hc : CanonPre ε c hist) (β : ℝ)
    (hlucky : ∃ i : Fin m, 1 / 2 + 2 * ε < (cnt (c i) : ℝ) / n)
    (hpos : historyProb (M ε) (biLinUCBLearner (M ε) (qe ε) n β) hist ≠ 0) :
    ¬ ((∑ s : St, (M ε).d1 s * Vstar (M ε) 0 s) -
      (∑ s : St, (M ε).d1 s *
        V (M ε) (biLinUCBOutput (M ε) (qe ε) (List.ofFn hist) n β K) 0 s) ≤ ε) := by
  obtain ⟨i, hi⟩ := hlucky
  have hmT : m * n ≤ K * n := Nat.mul_le_mul_right n hmK
  have hEi : empValue (M ε) (List.ofFn hist) n i = (cnt (c i) : ℝ) / n :=
    emp_batch ε _ n i _ (batch_canon ε c hist hmT hc i i.2)
  have hmem : (i : ℕ) ∈ List.range K := List.mem_range.2 (lt_of_lt_of_le i.2 hmK)
  obtain ⟨k, hk⟩ : ∃ k, (List.range K).argmax (empValue (M ε) (List.ofFn hist) n) = some k := by
    cases h : (List.range K).argmax (empValue (M ε) (List.ofFn hist) n) with
    | none => rw [List.argmax_eq_none] at h; simp [h] at hmem
    | some k => exact ⟨k, rfl⟩
  have hkK : k < K := List.mem_range.1 (List.argmax_mem hk)
  have hle := List.le_of_mem_argmax hmem hk
  have hknT : k * n + n ≤ K * n := by
    calc k * n + n = (k + 1) * n := by ring
      _ ≤ K * n := Nat.mul_le_mul_right n hkK
  have hB : bestQ (M ε) (qe ε) ((List.ofFn hist).take (k * n)) n β k = true := by
    cases hb : bestQ (M ε) (qe ε) ((List.ofFn hist).take (k * n)) n β k with
    | true => rfl
    | false =>
      exfalso
      have hret : ∀ j : Fin n, (∑ h ∈ Finset.range 2,
          (M ε).R h (stateAt (hist ⟨k * n + j, Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.2 _) hknT⟩) h)
            (actionAt (hist ⟨k * n + j, Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.2 _) hknT⟩) h))
            = 1 / 2 + 2 * ε := by
        intro j
        apply star_ret ε hε
        unfold historyProb at hpos
        have hfac := (Finset.prod_ne_zero_iff.1 hpos)
          ⟨k * n + j, Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.2 _) hknT⟩ (Finset.mem_univ _)
        rw [learner_eq ε n β hist _ (le_of_lt (Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.2 _) hknT))]
          at hfac
        have hdiv : (k * n + j) / n = k := by
          rw [add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt j.2, zero_add]
        simp only [hdiv] at hfac
        rw [hb] at hfac
        exact hfac
      have hEk : empValue (M ε) (List.ofFn hist) n k = 1 / 2 + 2 * ε := by
        unfold empValue
        rw [batch_ofFn hist n k hknT, List.map_ofFn, List.sum_ofFn]
        simp only [Function.comp_apply, hret]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have hn' : (0:ℝ) < n := by exact_mod_cast hn
        field_simp
      linarith
  have hout : biLinUCBOutput (M ε) (qe ε) (List.ofFn hist) n β K =
      detPolicy (greedyPolicy (qe ε) true) := by
    unfold biLinUCBOutput iterPolicy
    rw [hk]
    simp only [Option.getD_some]
    rw [hB]
  rw [hout, gap_val ε hε]
  linarith

lemma τc_inj (ε : ℝ) : Function.Injective (τc ε) := by
  intro b b' h
  have := congrArg (fun τ : Tr => (τ.2 0).2) h
  cases b <;> cases b' <;> simp_all [τc, s1]

noncomputable def Ec (ε : ℝ) {m n : ℕ} (c : Fin m → Fin n → Bool) : Fin (m * n) → Tr :=
  fun t => τc ε (c (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2)

lemma Ec_canon (ε : ℝ) {m n : ℕ} (c : Fin m → Fin n → Bool) : CanonPre ε c (Ec ε c) := by
  intro i j hi hj h
  simp only [Ec]
  have : finProdFinEquiv.symm (⟨i * n + j, h⟩ : Fin (m * n)) = (⟨i, hi⟩, ⟨j, hj⟩) := by
    rw [Equiv.symm_apply_eq]; ext; simp [finProdFinEquiv]; ring
  rw [this]

lemma Ec_inj (ε : ℝ) {m n : ℕ} : Function.Injective (Ec ε (m := m) (n := n)) := by
  intro c c' h
  funext i j
  have := congrFun h (finProdFinEquiv (i, j))
  simp only [Ec, Equiv.symm_apply_apply] at this
  exact τc_inj ε this

open Classical in
lemma prob_le (ε : ℝ) (hε : 0 < ε) {m n K : ℕ} (hn : 0 < n) (hmK : m ≤ K) (β : ℝ) (hβ : 0 ≤ β) :
    probEvent (M ε) (biLinUCBLearner (M ε) (qe ε) n β) (K * n)
        (fun histT => (∑ s : St, (M ε).d1 s * Vstar (M ε) 0 s) -
          (∑ s : St, (M ε).d1 s *
            V (M ε) (biLinUCBOutput (M ε) (qe ε) (List.ofFn histT) n β K) 0 s) ≤ ε) ≤
      1 - (∑ c : Fin m → Fin n → Bool,
        (if Surv ε β c ∧ (∃ i, 1 / 2 + 2 * ε < (cnt (c i) : ℝ) / n) then (1:ℝ) else 0)) *
          (1 / 2) ^ (m * n) := by
  have hmT : m * n ≤ K * n := Nat.mul_le_mul_right n hmK
  set L := biLinUCBLearner (M ε) (qe ε) n β with hL
  set good : (Fin m → Fin n → Bool) → Prop :=
    fun c => Surv ε β c ∧ (∃ i, 1 / 2 + 2 * ε < (cnt (c i) : ℝ) / n) with hgood
  set G : (Fin (m * n) → Tr) → Prop := fun g => ∃ c, good c ∧ g = Ec ε c with hG
  unfold probEvent
  have step1 : ∀ hist : Fin (K * n) → Tr,
      (if (∑ s : St, (M ε).d1 s * Vstar (M ε) 0 s) -
          (∑ s : St, (M ε).d1 s *
            V (M ε) (biLinUCBOutput (M ε) (qe ε) (List.ofFn hist) n β K) 0 s) ≤ ε
        then historyProb (M ε) L hist else 0) ≤
      historyProb (M ε) L hist -
        (if G (fun i => hist (Fin.castLE hmT i)) then historyProb (M ε) L hist else 0) := by
    intro hist
    have h0 := hp_nonneg ε n β hist
    split_ifs with hs hGh hGh
    · obtain ⟨c, hgc, hpre⟩ := hGh
      have hcan : CanonPre ε c hist := by
        intro i j hi hj h
        have h' : i * n + j < m * n := by
          calc i * n + j < i * n + n := Nat.add_lt_add_left hj _
            _ = (i + 1) * n := by ring
            _ ≤ m * n := Nat.mul_le_mul_right n hi
        have := congrFun hpre ⟨i * n + j, h'⟩
        rw [Ec_canon ε c i j hi hj h'] at this
        rw [← this]; rfl
      have : historyProb (M ε) L hist = 0 := by
        by_contra hne
        exact not_succ ε hε hn hmK c hist hcan β hgc.2 hne hs
      rw [this]; simp
    · simp
    · simp
    · simpa using h0
  calc _ ≤ ∑ hist : Fin (K * n) → Tr, (historyProb (M ε) L hist -
        (if G (fun i => hist (Fin.castLE hmT i)) then historyProb (M ε) L hist else 0)) :=
          Finset.sum_le_sum (fun hist _ => step1 hist)
    _ = 1 - ∑ g : Fin (m * n) → Tr, (if G g then historyProb (M ε) L g else 0) := by
          rw [Finset.sum_sub_distrib, mass ε (K * n) L (learner_valid ε n β),
            prefix_sum ε (m * n) (K * n) hmT L (learner_valid ε n β) G]
    _ = _ := by
          congr 1
          rw [Finset.sum_mul]
          symm
          apply Fintype.sum_of_injective (Ec ε) (Ec_inj ε)
          · intro g hg
            rw [if_neg]
            rintro ⟨c, _, rfl⟩
            exact hg ⟨c, rfl⟩
          · intro c
            by_cases hc : good c
            · have hGc : G (Ec ε c) := ⟨c, hc, rfl⟩
              rw [if_pos hGc, if_pos hc, one_mul,
                hp_canon ε hε hn c (Ec ε c) (Ec_canon ε c) β hβ hc.1]
            · have hGc : ¬ G (Ec ε c) := by
                rintro ⟨c', hc', he⟩
                exact hc ((Ec_inj ε he) ▸ hc')
              rw [if_neg hGc, if_neg hc, zero_mul]

end Dp51

set_option maxHeartbeats 1000000 in
open FoundationsRL.RLBasics FoundationsRL.FuncApprox in
theorem solution : ¬ (∃ c1 c2 c3 : ℝ, 0 < c1 ∧ 0 < c2 ∧ 0 < c3 ∧
      ∀ {S A : Type} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S] [DecidableEq A]
        {H : ℕ} (M : EpisodicMDP S A H) (_hM : RewardsNormalized M)
        {Qc : Type} [Fintype Qc] [Nonempty Qc]
        (qeval : Qc → ℕ → S → A → ℝ) (_hQ : IsNormalizedValueClass H qeval) (q0 : Qc)
        (_hq0 : qeval q0 = fun h s a => if h < H then Qstar M h s a else 0) (d : ℕ)
        (_hrank : ∃ (X : Policy S A H → ℕ → Fin d → ℝ) (W : (ℕ → S → A → ℝ) → ℕ → Fin d → ℝ),
          (∀ π, IsPolicy H π → ∀ Qf : Qc, ∀ h : ℕ, h < H →
              bellmanResidual M π h (qeval Qf) = ∑ j : Fin d, X π h j * W (qeval Qf) h j) ∧
          (∀ π, IsPolicy H π → ∀ h : ℕ, h < H → ∑ j : Fin d, (X π h j) ^ 2 ≤ 1) ∧
          (∀ Qf : Qc, ∀ h : ℕ, h < H → ∑ j : Fin d, (W (qeval Qf) h j) ^ 2 ≤ 1)),
        ∀ ε δ : ℝ, 0 < ε → 0 < δ →
        ∀ n K : ℕ, 0 < n →
          (n : ℝ) ≥ c1 * (H : ℝ) ^ 3 * d * Real.log ((Fintype.card Qc : ℝ) / δ) / ε ^ 2 →
          c2 * ((H : ℝ) * d * Real.log (1 + (n : ℝ) / d)) ≤ K →
          (K : ℝ) ≤ 2 * c2 * ((H : ℝ) * d * Real.log (1 + (n : ℝ) / d)) + 1 →
          ∀ β : ℝ,
            β = c3 * ((K : ℝ) * Real.log (Fintype.card Qc) + Real.log ((H : ℝ) * K / δ)) / n →
            probEvent M (biLinUCBLearner M qeval n β) (K * n)
                (fun histT =>
                  (∑ s : S, M.d1 s * Vstar M 0 s) -
                    (∑ s : S, M.d1 s *
                      V M (biLinUCBOutput M qeval (List.ofFn histT) n β K) 0 s) ≤ ε)
              ≥ 1 - δ) := by
  classical
  rintro ⟨c1, c2, c3, hc1, hc2, hc3, hmain⟩
  have hl8 : 0 < Real.log 8 := Real.log_pos (by norm_num)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set α : ℝ := 8 * Real.sqrt (c1 * Real.log 8) with hα
  have hαpos : 0 < α := by
    have : 0 < Real.sqrt (c1 * Real.log 8) := Real.sqrt_pos.2 (by positivity)
    rw [hα]; linarith
  have hα2 : α ^ 2 = 64 * (c1 * Real.log 8) := by
    rw [hα, mul_pow, Real.sq_sqrt (by positivity)]; norm_num
  set A : ℝ := α ^ 2 + 1 / 8 with hA
  have hApos : 0 < A := by positivity
  set p0 : ℝ := min ((α / 2) * Real.exp (-(4 * (2 * α + 3) ^ 2))) (1 / 2) with hp0
  have hp0pos : 0 < p0 := lt_min (by positivity) (by norm_num)
  have hp0le : p0 ≤ 1 / 2 := min_le_right _ _
  obtain ⟨j0, hj0⟩ : ∃ j0 : ℕ, ∀ j ≥ j0, (1 - p0) ^ j < 1 / 4 := by
    have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith : (0:ℝ) ≤ 1 - p0)
      (by linarith : 1 - p0 < 1)
    exact Filter.eventually_atTop.1 (ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1 / 4)))
  set J : ℕ := max j0 1 with hJ
  have hJ1 : 1 ≤ J := le_max_right _ _
  have hJj : j0 ≤ J := le_max_left _ _
  set B : ℝ := (J : ℝ) * max 1 (8 * A / (c3 * Real.log 2)) with hB
  have hB1 : (J : ℝ) ≤ B := le_mul_of_one_le_right (by positivity) (le_max_left _ _)
  have hB2 : (J : ℝ) * (8 * A / (c3 * Real.log 2)) ≤ B :=
    mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
  have E1 := Dp51.anti_conc α hαpos
  have E2 : ∀ᶠ N : ℕ in Filter.atTop, 16 * α ^ 2 + 1 ≤ (N : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop (⌈16 * α ^ 2 + 1⌉₊)] with N hN
    exact (Nat.le_ceil _).trans (by exact_mod_cast hN)
  have E3 : ∀ᶠ N : ℕ in Filter.atTop, B / (2 * c2) ≤ Real.log N :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  obtain ⟨N, hN1, hN2, hN3⟩ := (E1.and (E2.and E3)).exists
  have hNpos : (1:ℝ) ≤ N := by linarith [sq_nonneg α]
  have hN0 : 0 < N := by exact_mod_cast (show (0:ℝ) < N by linarith)
  set y := Real.sqrt N with hy
  have hy2 : y ^ 2 = N := Real.sq_sqrt (by positivity)
  have hypos : 0 < y := Real.sqrt_pos.2 (by linarith)
  have hy4 : 4 * α ≤ y := by
    rw [hy]; apply Real.le_sqrt_of_sq_le
    have : (4 * α) ^ 2 = 16 * α ^ 2 := by ring
    linarith
  set ε : ℝ := α / (4 * y) with hεdef
  have hε : 0 < ε := by positivity
  have hε' : ε ≤ 1 / 16 := by
    rw [hεdef, div_le_iff₀ (by positivity)]; linarith
  have hε2 : ε ^ 2 = α ^ 2 / (16 * N) := by
    have e : (4 * y) ^ 2 = 16 * N := by rw [mul_pow, hy2]; norm_num
    rw [hεdef, div_pow, e]
  set n : ℕ := 2 * N with hn
  have hnpos : 0 < n := by omega
  have hnR : (n : ℝ) = 2 * N := by rw [hn]; push_cast; ring
  set X : ℝ := ((2:ℕ):ℝ) * ((1:ℕ):ℝ) * Real.log (1 + (n : ℝ) / ((1:ℕ):ℝ)) with hX
  have hX' : X = 2 * Real.log (1 + (n:ℝ)) := by rw [hX]; push_cast; ring
  have hlogN : Real.log N ≤ Real.log (1 + (n:ℝ)) := by
    apply Real.log_le_log (by positivity)
    rw [hnR]; linarith
  have hX0 : 0 ≤ X := by
    rw [hX']; have := Real.log_nonneg (show (1:ℝ) ≤ N by linarith); linarith
  set K : ℕ := ⌈c2 * X⌉₊ with hK
  have hK1 : c2 * X ≤ (K : ℝ) := Nat.le_ceil _
  have hK2 : (K : ℝ) ≤ 2 * c2 * X + 1 := by
    have := Nat.ceil_lt_add_one (show 0 ≤ c2 * X by positivity)
    have : 0 ≤ c2 * X := by positivity
    linarith
  have hKB : B ≤ (K : ℝ) := by
    have h1 : B ≤ 2 * c2 * Real.log N := by
      have := hN3; rw [div_le_iff₀ (by positivity)] at this; linarith
    have h2 : 2 * c2 * Real.log N ≤ c2 * X := by
      rw [hX']
      have := mul_le_mul_of_nonneg_left hlogN hc2.le
      linarith
    linarith
  have hKJ : J ≤ K := by exact_mod_cast (hB1.trans hKB)
  have hK1' : (1:ℝ) ≤ K := by exact_mod_cast (hJ1.trans hKJ)
  set x : ℝ := c3 * K * Real.log 2 / (8 * A) with hx
  have hx0 : 0 ≤ x := by positivity
  have hxJ : (J : ℝ) ≤ x := by
    rw [hx, le_div_iff₀ (by positivity)]
    have := hB2.trans hKB
    rw [mul_div_assoc', div_le_iff₀ (by positivity)] at this
    linarith
  set m : ℕ := min K (⌊x⌋₊ + 1) with hm
  have hmK : m ≤ K := min_le_left _ _
  have hmJ : J ≤ m := le_min hKJ (by have := Nat.le_floor hxJ; omega)
  have hm1 : 1 ≤ m := hJ1.trans hmJ
  have hmx : ((m - 1 : ℕ) : ℝ) ≤ x := by
    have h1 : m - 1 ≤ ⌊x⌋₊ := by have := min_le_right K (⌊x⌋₊ + 1); omega
    exact (by exact_mod_cast h1 : ((m - 1 : ℕ) : ℝ) ≤ ⌊x⌋₊).trans (Nat.floor_le hx0)
  -- β
  have hcard : (Fintype.card Bool : ℝ) = 2 := by simp
  set β : ℝ := c3 * ((K : ℝ) * Real.log (Fintype.card Bool) +
      Real.log (((2:ℕ):ℝ) * K / (1 / 4))) / (n : ℝ) with hβ
  have hlogK : 0 ≤ Real.log (((2:ℕ):ℝ) * K / (1 / 4)) := by
    apply Real.log_nonneg; push_cast; rw [le_div_iff₀ (by norm_num)]; linarith
  have hβlow : c3 * K * Real.log 2 / n ≤ β := by
    rw [hβ, hcard]
    apply div_le_div_of_nonneg_right _ (by positivity)
    rw [mul_add]
    have := mul_nonneg hc3.le hlogK
    have e : c3 * (↑K * Real.log 2) = c3 * ↑K * Real.log 2 := by ring
    linarith
  have hβpos : 0 < β := lt_of_lt_of_le (by positivity) hβlow
  -- the threshold hypothesis holds with equality
  have hthr : (n : ℝ) ≥ c1 * ((2:ℕ):ℝ) ^ 3 * ((1:ℕ):ℝ) *
      Real.log ((Fintype.card Bool : ℝ) / (1 / 4)) / ε ^ 2 := by
    rw [hcard, hε2, hα2, ge_iff_le, div_le_iff₀ (by positivity), hnR]
    have h8 : (2:ℝ) / (1 / 4) = 8 := by norm_num
    rw [h8]; push_cast
    have : 2 * (N:ℝ) * (64 * (c1 * Real.log 8) / (16 * N)) = 8 * (c1 * Real.log 8) := by
      field_simp; ring
    rw [this]; ring_nf; exact le_refl _
  have hP := hmain (Dp51.M ε) (Dp51.rewards_norm ε hε hε') (Dp51.qe ε) (Dp51.normalized ε hε hε')
    false rfl 1 (Dp51.rank1 ε hε hε') ε (1 / 4) hε (by norm_num) n K hnpos hthr hK1 hK2 β rfl
  have hle := Dp51.prob_le ε hε hnpos hmK β hβpos.le
  -- count of good coin patterns
  set Lk : (Fin n → Bool) → Prop := fun b => 1 / 2 + 2 * ε < (Dp51.cnt b : ℝ) / n with hLk
  have hgc := Dp51.good_coins m n (m - 1) (Nat.sub_le m 1) (Dp51.Ysq ε) (fun b => sq_nonneg _)
    β hβpos Lk
  have hY : ∑ b : Fin n → Bool, Dp51.Ysq ε b = 2 ^ n * (A / N) := by
    have := Dp51.sum_resid_sq n hnpos (4 * ε)
    simp only [Dp51.Ysq]
    rw [this, hnR]
    congr 1
    rw [mul_pow, hε2, hA]; field_simp; ring
  have hSL1 : ∑ b : Fin n → Bool, (if Lk b then (1:ℝ) else 0) ≤ 2 ^ n := by
    calc _ ≤ ∑ _b : Fin n → Bool, (1:ℝ) := Finset.sum_le_sum (fun b _ => by split_ifs <;> norm_num)
      _ = 2 ^ n := Dp51.card_coins n
  have hSL2 : p0 * 2 ^ n ≤ ∑ b : Fin n → Bool, (if Lk b then (1:ℝ) else 0) := by
    have h4 : (2:ℝ) ^ n = 4 ^ N := by rw [hn, pow_mul]; norm_num
    have hpt : ∀ b : Fin (2 * N) → Bool,
        (if (N:ℝ) + α * Real.sqrt N < Dp51.cnt b then (1:ℝ) else 0) ≤ if Lk b then 1 else 0 := by
      intro b
      split_ifs with h1 h2
      · exact le_rfl
      · exfalso; apply h2
        simp only [hLk]
        rw [hnR, lt_div_iff₀ (by positivity)]
        have e : (1 / 2 + 2 * ε) * (2 * (N:ℝ)) = N + α * y := by
          rw [hεdef]; field_simp; rw [← hy2]; ring
        rw [e]; exact h1
      · norm_num
      · exact le_rfl
    calc p0 * 2 ^ n ≤ (α / 2) * Real.exp (-(4 * (2 * α + 3) ^ 2)) * 4 ^ N := by
          rw [h4]; exact mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
      _ ≤ _ := hN1
      _ ≤ _ := Finset.sum_le_sum (fun b _ => hpt b)
  have hT1 : ((m - 1 : ℕ) : ℝ) * (∑ b : Fin n → Bool, Dp51.Ysq ε b) * (2 ^ n) ^ (m - 1) / β ≤
      (2 ^ n : ℝ) ^ m / 4 := by
    rw [hY]
    have hpow : (2 ^ n : ℝ) ^ m = 2 ^ n * (2 ^ n) ^ (m - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [hpow, div_le_iff₀ hβpos]
    have hNβ : c3 * K * Real.log 2 / 2 ≤ N * β := by
      have := hβlow; rw [hnR, div_le_iff₀ (by positivity)] at this
      have e : β * (2 * (N:ℝ)) = 2 * (N * β) := by ring
      linarith
    have hmA : 4 * (((m - 1 : ℕ) : ℝ) * A) ≤ c3 * K * Real.log 2 / 2 := by
      have := hmx; rw [hx, le_div_iff₀ (by positivity)] at this
      have e : ((m - 1 : ℕ) : ℝ) * (8 * A) = 8 * (((m - 1 : ℕ) : ℝ) * A) := by ring
      linarith
    have hP0 : (0:ℝ) ≤ 2 ^ n * (2 ^ n) ^ (m - 1) := by positivity
    have hNpos' : (0:ℝ) < N := by linarith
    have : ((m - 1 : ℕ) : ℝ) * (2 ^ n * (A / N)) * (2 ^ n) ^ (m - 1) =
        (((m - 1 : ℕ) : ℝ) * A / N) * (2 ^ n * (2 ^ n) ^ (m - 1)) := by
      field_simp
    rw [this]
    have hq : ((m - 1 : ℕ) : ℝ) * A / N ≤ β / 4 := by
      rw [div_le_iff₀ hNpos']
      have e : β / 4 * N = N * β / 4 := by ring
      rw [e]; linarith
    calc ((m - 1 : ℕ) : ℝ) * A / N * (2 ^ n * (2 ^ n) ^ (m - 1))
        ≤ β / 4 * (2 ^ n * (2 ^ n) ^ (m - 1)) := mul_le_mul_of_nonneg_right hq hP0
      _ = 2 ^ n * (2 ^ n) ^ (m - 1) / 4 * β := by ring
  have hT2 : ((2 ^ n : ℝ) - ∑ b : Fin n → Bool, (if Lk b then (1:ℝ) else 0)) ^ m ≤
      (2 ^ n : ℝ) ^ m / 4 := by
    have h0 : (0:ℝ) ≤ 2 ^ n - ∑ b : Fin n → Bool, (if Lk b then (1:ℝ) else 0) := by linarith
    calc _ ≤ (2 ^ n * (1 - p0) : ℝ) ^ m := pow_le_pow_left₀ h0 (by linarith) m
      _ = (2 ^ n : ℝ) ^ m * (1 - p0) ^ m := mul_pow _ _ _
      _ ≤ (2 ^ n : ℝ) ^ m * (1 / 4) := by
          apply mul_le_mul_of_nonneg_left (hj0 m (hJj.trans hmJ)).le (by positivity)
      _ = _ := by ring
  have hgood : (2 ^ n : ℝ) ^ m / 2 ≤ ∑ c : Fin m → Fin n → Bool,
      (if Dp51.Surv ε β c ∧ (∃ i, 1 / 2 + 2 * ε < (Dp51.cnt (c i) : ℝ) / n) then (1:ℝ) else 0) := by
    have e : ∑ c : Fin m → Fin n → Bool,
        (if (∑ i : Fin m, (if i.val < m - 1 then Dp51.Ysq ε (c i) else 0)) ≤ β ∧ ∃ i, Lk (c i)
          then (1:ℝ) else 0) = ∑ c : Fin m → Fin n → Bool,
        (if Dp51.Surv ε β c ∧ (∃ i, 1 / 2 + 2 * ε < (Dp51.cnt (c i) : ℝ) / n) then (1:ℝ) else 0) :=
      Finset.sum_congr rfl (fun c _ => if_congr Iff.rfl rfl rfl)
    rw [← e]
    linarith
  have hfin : (1:ℝ) / 2 ≤ (∑ c : Fin m → Fin n → Bool,
      (if Dp51.Surv ε β c ∧ (∃ i, 1 / 2 + 2 * ε < (Dp51.cnt (c i) : ℝ) / n) then (1:ℝ) else 0)) *
        (1 / 2) ^ (m * n) := by
    have hone : (2 ^ n : ℝ) ^ m * (1 / 2) ^ (m * n) = 1 := by
      rw [← pow_mul, mul_comm n m, ← mul_pow]; norm_num
    have hp : (0:ℝ) ≤ (1 / 2) ^ (m * n) := by positivity
    calc (1:ℝ) / 2 = (2 ^ n : ℝ) ^ m / 2 * (1 / 2) ^ (m * n) := by
          rw [div_mul_eq_mul_div, hone]
      _ ≤ _ := mul_le_mul_of_nonneg_right hgood hp
  linarith
