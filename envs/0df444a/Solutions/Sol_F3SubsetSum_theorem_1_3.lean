-- Prove2me | solution 1 for F3SubsetSum.theorem_1_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-15T03:23:25.441579+00:00
-- url     : https://prove2.me/submissions/0581c2db-8f6f-4f3e-b384-7d40b3cd4eb6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_F3SubsetSum_theorem_1_7
import Theorems.Thm_F3SubsetSum_fact_1_2
import Theorems.Thm_F3SubsetSum_theorem_3_1
import Theorems.Thm_F3SubsetSum_exhaustive_search_circuit
import Theorems.Thm_F3SubsetSum_generator_branch

/-! # Root reduction for Theorem 1.3 -/

namespace T13

open F3SubsetSum

/-- `n ≤ r^(h/δ)` with `δ = min (1/2) (log κ / 2)`. -/
theorem n_le_rpow (κ r h : ℝ) (n : ℕ) (hκ : 1 < κ) (hn : 1 ≤ n) (hr : κ ≤ r) (hh1 : 1 ≤ h)
    (hh : (n : ℝ) / r ≤ h) :
    (n : ℝ) ≤ r ^ (h / min (1 / 2) (Real.log κ / 2)) := by
  have hr0 : 0 < r := by linarith
  have hr1 : 1 < r := by linarith
  have hlk : 0 < Real.log κ := Real.log_pos hκ
  have hlr : Real.log κ ≤ Real.log r := Real.log_le_log (by linarith) hr
  have hlr0 : 0 < Real.log r := Real.log_pos hr1
  set δ := min (1 / 2) (Real.log κ / 2) with hδ
  have hδ0 : 0 < δ := lt_min (by norm_num) (by linarith)
  have hδ1 : δ ≤ 1 / 2 := min_le_left _ _
  have hδ2 : δ ≤ Real.log κ / 2 := min_le_right _ _
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hln : 0 ≤ Real.log n := Real.log_nonneg hnR
  -- reduce to logs
  rw [← Real.exp_log (show (0 : ℝ) < n by linarith), ← Real.exp_log (Real.rpow_pos_of_pos hr0 _),
    Real.log_rpow hr0]
  apply Real.exp_le_exp.2
  rw [div_mul_eq_mul_div, le_div_iff₀ hδ0]
  -- goal: log n * δ ≤ h * log r
  have hhr : (n : ℝ) / r * Real.log r ≤ h * Real.log r := mul_le_mul_of_nonneg_right hh hlr0.le
  by_cases c1 : (n : ℝ) ≤ r
  · have : Real.log n ≤ Real.log r := Real.log_le_log (by linarith) c1
    nlinarith
  · push Not at c1
    by_cases c2 : Real.sqrt n < r
    · -- log r ≥ (1/2) log n and n / r ≥ 1
      have hs : Real.log n / 2 ≤ Real.log r := by
        have := Real.log_le_log (Real.sqrt_pos.2 (by linarith)) c2.le
        rw [Real.log_sqrt (by linarith)] at this; linarith
      have hnr : 1 ≤ (n : ℝ) / r := by rw [le_div_iff₀ hr0]; linarith
      have : Real.log r ≤ (n : ℝ) / r * Real.log r := by nlinarith
      nlinarith
    · push Not at c2
      -- n / r ≥ √n ≥ log n / 2
      have hsq : Real.sqrt n ≤ (n : ℝ) / r := by
        rw [le_div_iff₀ hr0]
        have h1 : Real.sqrt n * r ≤ Real.sqrt n * Real.sqrt n :=
          mul_le_mul_of_nonneg_left c2 (Real.sqrt_nonneg _)
        rw [Real.mul_self_sqrt (by linarith)] at h1; exact h1
      have hlog : Real.log n / 2 ≤ Real.sqrt n := by
        have h1 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 (show (0:ℝ) < n by linarith))
        rw [Real.log_sqrt (by linarith)] at h1; linarith
      have : Real.log n / 2 * Real.log κ ≤ (n : ℝ) / r * Real.log r := by
        apply mul_le_mul (hlog.trans hsq) hlr hlk.le (by positivity)
      nlinarith


theorem ceil_div_nat (a b : ℕ) (hb : 0 < b) : ⌈(a : ℝ) / b⌉₊ = (a + b - 1) / b := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  set k := (a + b - 1) / b
  have h1 : a ≤ k * b := by
    have h := Nat.lt_mul_div_succ (a + b - 1) hb
    have e : b * ((a + b - 1) / b + 1) = k * b + b := by simp only [k]; ring
    rw [e] at h
    omega
  have h3 : k * b ≤ a + b - 1 := Nat.div_mul_le_self _ _
  apply le_antisymm
  · apply Nat.ceil_le.2
    rw [div_le_iff₀ hbR]; exact_mod_cast h1
  · by_contra hcon
    push Not at hcon
    have h4 : ⌈(a : ℝ) / b⌉₊ + 1 ≤ k := hcon
    have h5 : (a : ℝ) / b ≤ ⌈(a : ℝ) / b⌉₊ := Nat.le_ceil _
    have h6 : (a : ℝ) ≤ ⌈(a : ℝ) / b⌉₊ * b := by rwa [div_le_iff₀ hbR] at h5
    have h7 : ⌈(a : ℝ) / b⌉₊ * b + b ≤ k * b := by nlinarith
    have h8 : (a : ℝ) + b ≤ k * b := by
      have : ((⌈(a : ℝ) / b⌉₊ * b + b : ℕ) : ℝ) ≤ (k * b : ℕ) := by exact_mod_cast h7
      push_cast at this; linarith
    have h9 : (k * b : ℝ) ≤ a + b - 1 := by
      have : ((k * b : ℕ) : ℝ) ≤ ((a + b - 1 : ℕ) : ℝ) := by exact_mod_cast h3
      rw [Nat.cast_sub (by omega)] at this; push_cast at this; linarith
    linarith


/-! ## Machines -/

theorem outputsWithin_mono {M : Turing.TM2ComputableAux Bool Bool} {i o : List Bool} {t t' : ℕ}
    (h : t ≤ t') (hM : HMBinPacking.OutputsWithin M i o t) :
    HMBinPacking.OutputsWithin M i o t' := by
  obtain ⟨e⟩ := hM
  exact ⟨{ toEvalsTo := e.toEvalsTo, steps_le_m := e.steps_le_m.trans h }⟩

theorem computesWithin_mono {q : ℕ} {M : Turing.TM2ComputableAux Bool Bool} {Dec : DecoderFn q}
    {n m t t' : ℕ} (h : t ≤ t') (hc : ComputesWithin M Dec n m t) :
    ComputesWithin M Dec n m t' := fun A b => outputsWithin_mono h (hc A b)

/-! ## Average error from pointwise failure -/

theorem avgError_le (Dec : DecoderFn 3) (n m : ℕ) (δ : ℝ)
    (h : ∀ s e, pointwiseFailure Dec n m s e ≤ δ) : avgError Dec n m ≤ δ := by
  unfold avgError
  have key : ∀ (s : Fin n → ZMod 3) (e : Fin m → Bool),
      ((Finset.univ.filter fun A : Matrix (Fin n) (Fin m) (ZMod 3) =>
        Dec n m A (lweSample A s e) ≠ s).card : ℝ) ≤ δ * (3 : ℝ) ^ (n * m) := by
    intro s e
    have := h s e
    unfold pointwiseFailure at this
    push_cast at this
    rwa [div_le_iff₀ (by positivity)] at this
  have hsplit : (Finset.univ.filter fun x : Matrix (Fin n) (Fin m) (ZMod 3) ×
      (Fin n → ZMod 3) × (Fin m → Bool) => Dec n m x.1 (lweSample x.1 x.2.1 x.2.2) ≠ x.2.1).card =
      ∑ s : Fin n → ZMod 3, ∑ e : Fin m → Bool, (Finset.univ.filter fun A : Matrix (Fin n) (Fin m)
        (ZMod 3) => Dec n m A (lweSample A s e) ≠ s).card := by
    simp only [Finset.card_filter]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp only [Fintype.sum_prod_type]
  rw [div_le_iff₀ (by positivity), hsplit]
  push_cast
  calc (∑ s : Fin n → ZMod 3, ∑ e : Fin m → Bool, ((Finset.univ.filter fun A :
        Matrix (Fin n) (Fin m) (ZMod 3) => Dec n m A (lweSample A s e) ≠ s).card : ℝ))
      ≤ ∑ _s : Fin n → ZMod 3, ∑ _e : Fin m → Bool, δ * (3 : ℝ) ^ (n * m) :=
        Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun e _ => key s e
    _ = δ * ((3 : ℝ) ^ (n * m) * (3 : ℝ) ^ n * (2 : ℝ) ^ m) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, ZMod.card,
          Fintype.card_fin, Fintype.card_bool, nsmul_eq_mul]
        push_cast; ring

/-! ## Polynomial bookkeeping -/

theorem two_level (D₁ D₃ Z W : ℕ) (hZ : 1 ≤ Z) (hW : W ≤ D₁ * Z ^ D₁) :
    D₃ * (W + Z) ^ D₃ + W ≤ (D₃ * (D₁ + 1) ^ D₃ + D₁) * Z ^ ((D₁ + 1) * (D₃ + 1)) := by
  have hZ0 : 0 < Z := hZ
  have p1 : Z ^ D₁ ≤ Z ^ (D₁ + 1) := Nat.pow_le_pow_right hZ0 (by omega)
  have p2 : Z ≤ Z ^ (D₁ + 1) := by
    calc Z = Z ^ 1 := (pow_one Z).symm
      _ ≤ Z ^ (D₁ + 1) := Nat.pow_le_pow_right hZ0 (by omega)
  have hWZ : W + Z ≤ (D₁ + 1) * Z ^ (D₁ + 1) := by
    have := Nat.mul_le_mul_left D₁ p1
    nlinarith
  have e1 : (W + Z) ^ D₃ ≤ (D₁ + 1) ^ D₃ * Z ^ ((D₁ + 1) * (D₃ + 1)) := by
    calc (W + Z) ^ D₃ ≤ ((D₁ + 1) * Z ^ (D₁ + 1)) ^ D₃ := Nat.pow_le_pow_left hWZ _
      _ = (D₁ + 1) ^ D₃ * Z ^ ((D₁ + 1) * D₃) := by rw [mul_pow, ← pow_mul]
      _ ≤ (D₁ + 1) ^ D₃ * Z ^ ((D₁ + 1) * (D₃ + 1)) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hZ0 (Nat.mul_le_mul_left _ (by omega)))
  have e2 : W ≤ D₁ * Z ^ ((D₁ + 1) * (D₃ + 1)) :=
    hW.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hZ0 (by nlinarith)))
  have e3 := Nat.mul_le_mul_left D₃ e1
  calc D₃ * (W + Z) ^ D₃ + W ≤ D₃ * ((D₁ + 1) ^ D₃ * Z ^ ((D₁ + 1) * (D₃ + 1))) +
        D₁ * Z ^ ((D₁ + 1) * (D₃ + 1)) := Nat.add_le_add e3 e2
    _ = (D₃ * (D₁ + 1) ^ D₃ + D₁) * Z ^ ((D₁ + 1) * (D₃ + 1)) := by ring

theorem absorb {κ y A E : ℝ} (hκ : 1 < κ) (hy : κ ≤ y) (hA : 0 ≤ A) (hE : 0 ≤ E) :
    A * y ^ E ≤ y ^ (E + Real.log (A + 1) / Real.log κ) := by
  have hlk : 0 < Real.log κ := Real.log_pos hκ
  have hy0 : 0 < y := by linarith
  have hL : 0 ≤ Real.log (A + 1) / Real.log κ := div_nonneg (Real.log_nonneg (by linarith)) hlk.le
  rw [Real.rpow_add hy0]
  have h1 : κ ^ (Real.log (A + 1) / Real.log κ) = A + 1 := by
    rw [Real.rpow_def_of_pos (by linarith), mul_div_cancel₀ _ hlk.ne', Real.exp_log (by linarith)]
  have h2 : κ ^ (Real.log (A + 1) / Real.log κ) ≤ y ^ (Real.log (A + 1) / Real.log κ) :=
    Real.rpow_le_rpow (by linarith) hy hL
  have h3 : 0 ≤ y ^ E := Real.rpow_nonneg hy0.le _
  nlinarith

theorem chain {κ y A B E Z : ℝ} (k : ℕ) (hκ : 1 < κ) (hy : κ ≤ y) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hE : 0 ≤ E) (hZ0 : 0 ≤ Z) (hZ : Z ≤ B * y ^ E) :
    A * Z ^ k ≤ y ^ (E * k + Real.log (A * B ^ k + 1) / Real.log κ) := by
  have hy0 : 0 < y := by linarith
  have h1 : Z ^ k ≤ B ^ k * y ^ (E * k) := by
    calc Z ^ k ≤ (B * y ^ E) ^ k := pow_le_pow_left₀ hZ0 hZ k
      _ = B ^ k * y ^ (E * k) := by
          rw [mul_pow, ← Real.rpow_natCast (y ^ E), ← Real.rpow_mul hy0.le]
  calc A * Z ^ k ≤ A * (B ^ k * y ^ (E * k)) := mul_le_mul_of_nonneg_left h1 hA
    _ = (A * B ^ k) * y ^ (E * k) := by ring
    _ ≤ _ := absorb hκ hy (by positivity) (by positivity)

/-! ## The size parameters -/

theorem setup (κ : ℝ) (hκ : 1 < κ) (n m : ℕ) (hn : 1 ≤ n) (hm : κ * n ≤ m) (r hR : ℝ)
    (hr : r = (m : ℝ) / n) (hh : hR = (⌈(n : ℝ) ^ 2 / m⌉ : ℝ)) :
    κ ≤ r ∧ 1 ≤ hR ∧ (n : ℝ) ≤ r * hR ∧ κ ≤ r ^ hR ∧
      (n : ℝ) ≤ (r ^ hR) ^ (1 / min (1 / 2) (Real.log κ / 2)) ∧
      (m : ℝ) ≤ (r ^ hR) ^ (1 + 1 / min (1 / 2) (Real.log κ / 2)) ∧
      ((((n ^ 2 + m - 1) / m : ℕ)) : ℝ) = hR ∧
      ((((m + n - 1) / n : ℕ)) : ℝ) < r + 1 ∧ r ≤ ((((m + n - 1) / n : ℕ)) : ℝ) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hmpos : (0 : ℝ) < m := by nlinarith
  have hm0 : 0 < m := by exact_mod_cast hmpos
  have hrκ : κ ≤ r := by rw [hr, le_div_iff₀ (by linarith)]; linarith
  have hr1 : 1 ≤ r := by linarith
  have hr0 : 0 < r := by linarith
  have hhge : (n : ℝ) ^ 2 / m ≤ hR := by rw [hh]; exact Int.le_ceil _
  have hnr : (n : ℝ) / r ≤ hR := by
    rw [hr, div_div_eq_mul_div]; rw [sq] at hhge; exact hhge
  have hh1 : 1 ≤ hR := by
    have : (0 : ℝ) < (n : ℝ) ^ 2 / m := by positivity
    have h0 : (0 : ℤ) < ⌈(n : ℝ) ^ 2 / m⌉ := Int.ceil_pos.2 this
    rw [hh]; exact_mod_cast h0
  have hrh : r ≤ r ^ hR := by
    calc r = r ^ (1 : ℝ) := (Real.rpow_one r).symm
      _ ≤ r ^ hR := Real.rpow_le_rpow_of_exponent_le hr1 hh1
  have hnb := n_le_rpow κ r hR n hκ hn hrκ hh1 hnr
  set δ := min (1 / 2 : ℝ) (Real.log κ / 2)
  have hnb' : (n : ℝ) ≤ (r ^ hR) ^ (1 / δ) := by
    rw [← Real.rpow_mul hr0.le, ← div_eq_mul_one_div]; exact hnb
  refine ⟨hrκ, hh1, ?_, hrκ.trans hrh, hnb', ?_, ?_, ?_, ?_⟩
  · rw [div_le_iff₀ hr0] at hnr; linarith
  · have e : (m : ℝ) = r * n := by rw [hr]; field_simp
    rw [Real.rpow_add (by positivity), Real.rpow_one, e]
    exact mul_le_mul hrh hnb' (by linarith) (by positivity)
  · have hc := ceil_div_nat (n ^ 2) m hm0
    rw [← hc, hh, natCast_ceil_eq_intCast_ceil (by positivity)]
    push_cast; rfl
  · have hc := ceil_div_nat m n (by omega)
    rw [← hc, ← hr]; exact Nat.ceil_lt_add_one hr0.le
  · have hc := ceil_div_nat m n (by omega)
    rw [← hc, ← hr]; exact Nat.le_ceil _

/-- The clock in the regime `m ≥ 2n`. -/
theorem clock_bounds (r hR C₁ : ℝ) (d hN x : ℕ) (hr : 2 ≤ r) (hhN : (hN : ℝ) = hR)
    (hx1 : (x : ℝ) < r + 1) (hx2 : r ≤ x) (hC : C₁ ≤ d) :
    ((x ^ (d * hN) : ℕ) : ℝ) ≤ (r ^ hR) ^ (2 * (d : ℝ)) ∧
      ⌊r ^ (C₁ * hR)⌋₊ ≤ x ^ (d * hN) := by
  have hr0 : 0 < r := by linarith
  have hh0 : 0 ≤ hR := by rw [← hhN]; positivity
  constructor
  · have hx : (x : ℝ) ≤ r ^ 2 := by nlinarith
    push_cast
    calc (x : ℝ) ^ (d * hN) ≤ (r ^ 2) ^ (d * hN) := pow_le_pow_left₀ (by positivity) hx _
      _ = (r ^ hR) ^ (2 * (d : ℝ)) := by
          rw [← Real.rpow_mul hr0.le, ← pow_mul, ← Real.rpow_natCast, ← hhN]
          push_cast; ring_nf
  · apply Nat.floor_le_of_le
    calc r ^ (C₁ * hR) ≤ r ^ ((d : ℝ) * hR) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (mul_le_mul_of_nonneg_right hC hh0)
      _ = r ^ (d * hN) := by rw [← hhN, ← Real.rpow_natCast]; push_cast; ring_nf
      _ ≤ (x : ℝ) ^ (d * hN) := pow_le_pow_left₀ hr0.le hx2 _
      _ = ((x ^ (d * hN) : ℕ) : ℝ) := by push_cast; ring

/-- `2^m` in the regime `m < Kn`. -/
theorem two_pow_bound (κ r hR : ℝ) (hκ : 1 < κ) (n m K : ℕ) (hrκ : κ ≤ r) (hnr : (n : ℝ) ≤ r * hR)
    (hr : r = (m : ℝ) / n) (hn : 1 ≤ n) (hmK : m < K * n) :
    (2 : ℝ) ^ m ≤ (r ^ hR) ^ ((K : ℝ) ^ 2 * Real.log 2 / Real.log κ) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hr0 : 0 < r := by linarith
  have hlk : 0 < Real.log κ := Real.log_pos hκ
  have hmK' : (m : ℝ) < K * n := by exact_mod_cast hmK
  have hrK : r < K := by rw [hr, div_lt_iff₀ (by linarith)]; exact hmK'
  have hK0 : (0 : ℝ) < K := by linarith
  have hh0 : 0 ≤ hR := by nlinarith
  have hmh : (m : ℝ) ≤ (K : ℝ) ^ 2 * hR := by nlinarith
  rw [← Real.rpow_mul hr0.le, Real.rpow_def_of_pos hr0, ← Real.rpow_natCast,
    Real.rpow_def_of_pos (by norm_num)]
  apply Real.exp_le_exp.2
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlr : Real.log κ ≤ Real.log r := Real.log_le_log (by linarith) hrκ
  have e : Real.log r * (hR * ((K : ℝ) ^ 2 * Real.log 2 / Real.log κ)) =
      (K : ℝ) ^ 2 * hR * Real.log 2 * (Real.log r / Real.log κ) := by field_simp
  rw [e]
  have h1 : 1 ≤ Real.log r / Real.log κ := by rw [le_div_iff₀ hlk]; linarith
  have h2 : 0 ≤ (K : ℝ) ^ 2 * hR * Real.log 2 := by positivity
  calc Real.log 2 * (m : ℝ) ≤ (K : ℝ) ^ 2 * hR * Real.log 2 := by nlinarith
    _ ≤ _ := le_mul_of_one_le_right h2 h1

theorem rpoly_le (C : ℝ) (D Z : ℕ) (hD : C ≤ D) (hZ : 1 ≤ Z) :
    C * (Z : ℝ) ^ C ≤ ((D * Z ^ D : ℕ) : ℝ) := by
  have hZR : (1 : ℝ) ≤ Z := by exact_mod_cast hZ
  have hR : (0 : ℝ) ≤ ((D * Z ^ D : ℕ) : ℝ) := by positivity
  rcases le_or_gt C 0 with h0 | h0
  · exact (mul_nonpos_of_nonpos_of_nonneg h0 (Real.rpow_nonneg (by linarith) _)).trans hR
  · push_cast
    rw [← Real.rpow_natCast (Z : ℝ) D]
    exact mul_le_mul hD (Real.rpow_le_rpow_of_exponent_le hZR hD)
      (Real.rpow_nonneg (by linarith) _) (by positivity)

theorem three_halves_lt_logb : (3 / 2 : ℝ) < Real.logb 2 3 := by
  rw [Real.lt_logb_iff_rpow_lt (by norm_num) (by norm_num)]
  have e : ((2 : ℝ) ^ ((3 : ℝ) / 2)) ^ 2 = 8 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  nlinarith [Real.rpow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) ((3 : ℝ) / 2)]

/-- `3ⁿ (2/3)^m ≤ 2^{−bm}` for `m ≥ 3n`, with `b = (2/3) log₂ 3 − 1 > 0`. -/
theorem collision_term (n m : ℕ) (h : 3 * (n : ℝ) ≤ m) :
    (3 : ℝ) ^ n * (2 / 3 : ℝ) ^ m ≤ (2 : ℝ) ^ (-((2 * Real.logb 2 3 / 3 - 1) * m)) := by
  set L := Real.logb 2 3 with hLdef
  have h3 : (3 : ℝ) = 2 ^ L := (Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)).symm
  have e1 : (3 : ℝ) ^ n = 2 ^ (L * n) := by
    rw [Real.rpow_mul (by norm_num), ← h3, Real.rpow_natCast]
  have e2 : (2 / 3 : ℝ) ^ m = 2 ^ ((1 - L) * m) := by
    rw [Real.rpow_mul (by norm_num), Real.rpow_sub (by norm_num), Real.rpow_one, ← h3,
      Real.rpow_natCast]
  rw [e1, e2, ← Real.rpow_add (by norm_num)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have hL : 0 < L := by have := three_halves_lt_logb; linarith
  have := mul_le_mul_of_nonneg_left h hL.le
  linarith

end T13

namespace T13

open F3SubsetSum

theorem one_lt_logb23 : (1 : ℝ) < Real.logb 2 3 := by
  rw [Real.lt_logb_iff_rpow_lt (by norm_num) (by norm_num)]; norm_num

theorem logb_32_3 : Real.logb (((3 : ℕ) : ℝ) / 2) ((3 : ℕ) : ℝ) < 3 := by
  push_cast
  rw [Real.logb_lt_iff_lt_rpow (by norm_num) (by norm_num)]
  rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num

set_option maxHeartbeats 1000000 in
theorem main_1_3 (κ : ℝ) (hκ : Real.logb 2 3 < κ) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (circ : ℕ → ℕ → Circuit) (C c : ℝ), 0 < C ∧ 0 < c ∧
      ∀ n m : ℕ, 1 ≤ n → κ * n ≤ m →
        HMBinPacking.OutputsWithin M (unaryD n ++ unary m) (encodeCircuit (circ n m))
            ⌊((m : ℝ) / n) ^ (C * (⌈(n : ℝ) ^ 2 / m⌉ : ℝ))⌋₊ ∧
          n * m + m ≤ (circ n m).wires ∧
          ((circ n m).gates.length : ℝ) ≤ ((m : ℝ) / n) ^ (C * (⌈(n : ℝ) ^ 2 / m⌉ : ℝ)) ∧
          ((circ n m).wires : ℝ) ≤ ((m : ℝ) / n) ^ (C * (⌈(n : ℝ) ^ 2 / m⌉ : ℝ)) ∧
          1 - (2 : ℝ) ^ (-(c * m)) ≤ successProb n m (circ n m) := by
  have hL1 := one_lt_logb23
  have hκ1 : 1 < κ := by linarith
  have hlk : 0 < Real.log κ := Real.log_pos hκ1
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  -- the ingredients
  obtain ⟨M, Dec, C₁, c₁, _hC₁, hc₁, h17⟩ := theorem_1_7 3 le_rfl 3 logb_32_3
  obtain ⟨G₁, circ₁, C₃, _hC₃, hG₁⟩ := theorem_3_1 M Dec
  set D₁ : ℕ := ⌈C₃⌉₊ with hD₁
  have hD₁C : C₃ ≤ D₁ := Nat.le_ceil _
  obtain ⟨G₂, circ₂, D₂, hG₂⟩ := exhaustive_search_circuit
  obtain ⟨-, hf⟩ := fact_1_2
  obtain ⟨c₂, hc₂, hf2⟩ := hf (κ - Real.logb 2 3) (by linarith)
  set b : ℝ := 2 * Real.logb 2 3 / 3 - 1 with hb
  have hb0 : 0 < b := by have := three_halves_lt_logb; linarith
  set a : ℝ := min c₁ b with ha
  have ha0 : 0 < a := lt_min hc₁ hb0
  set K : ℕ := max 3 ⌈2 * Real.logb 2 3 / a⌉₊ with hK
  set d : ℕ := ⌈C₁⌉₊ with hd
  obtain ⟨G, D₃, hG⟩ := generator_branch G₁ G₂ K d
  have hK3 : 3 ≤ K := le_max_left _ _
  have hK3R : (3 : ℝ) ≤ K := by exact_mod_cast hK3
  have hKL : 2 * Real.logb 2 3 / a ≤ K :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_max_right _ _)
  have hdC : C₁ ≤ d := Nat.le_ceil _
  -- constants
  set δ := min (1 / 2 : ℝ) (Real.log κ / 2) with hδ
  have hδ0 : 0 < δ := lt_min (by norm_num) (by linarith)
  set E₀ : ℝ := max (1 + 1 / δ) (2 * d) with hE₀
  have hE₀a : 1 + 1 / δ ≤ E₀ := le_max_left _ _
  have hE₀b : 2 * (d : ℝ) ≤ E₀ := le_max_right _ _
  have hE₀0 : 0 ≤ E₀ := le_trans (by positivity) hE₀a
  set A₁ : ℕ := D₃ * (D₁ + 1) ^ D₃ + D₁
  set k₁ : ℕ := (D₁ + 1) * (D₃ + 1)
  set E₂ : ℝ := (K : ℝ) ^ 2 * Real.log 2 / Real.log κ with hE₂
  have hE₂0 : 0 ≤ E₂ := div_nonneg (by positivity) hlk.le
  set A₂ : ℕ := D₃ * (D₂ + 1) ^ D₃ + D₂
  set k₂ : ℕ := (D₂ + 1) * (D₃ + 1)
  set Cr1 : ℝ := E₀ * k₁ + Real.log (A₁ * 4 ^ k₁ + 1) / Real.log κ
  set Cr2 : ℝ := (1 + 1 / δ + E₂) * k₂ + Real.log (A₂ * 4 ^ k₂ + 1) / Real.log κ
  set C : ℝ := max Cr1 Cr2 + 1 with hC
  set c : ℝ := min (a / 2) (c₂ / K) with hc
  have hK0 : (0 : ℝ) < K := by linarith
  refine ⟨G, fun n m => if K * n ≤ m then
      circ₁ n m (((m + n - 1) / n) ^ (d * ((n ^ 2 + m - 1) / m))) else circ₂ n m, C, c,
    ?_, lt_min (by linarith) (div_pos hc₂ hK0), ?_⟩
  · have hA0 : (0 : ℝ) ≤ A₁ * 4 ^ k₁ := by positivity
    have hlg : 0 ≤ Real.log (A₁ * 4 ^ k₁ + 1) / Real.log κ :=
      div_nonneg (Real.log_nonneg (by linarith)) hlk.le
    have h1 : 0 ≤ Cr1 := add_nonneg (by positivity) hlg
    have : Cr1 ≤ max Cr1 Cr2 := le_max_left _ _
    linarith
  intro n m hn hm
  simp only
  -- size parameters
  set r := (m : ℝ) / n with hr
  set hR := (⌈(n : ℝ) ^ 2 / m⌉ : ℝ) with hhR
  obtain ⟨hrκ, hh1, hnr, hyκ, hny, hmy, hhN, hx1, hx2⟩ := setup κ hκ1 n m hn hm r hR hr hhR
  set y := r ^ hR with hy
  have hy1 : 1 ≤ y := by linarith
  have hr0 : 0 < r := by linarith
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hm1 : 1 ≤ m := by
    have : (1 : ℝ) ≤ m := by nlinarith
    exact_mod_cast this
  have hyC : ∀ E : ℝ, E ≤ C → y ^ E ≤ r ^ (C * hR) := by
    intro E hE
    rw [hy, ← Real.rpow_mul hr0.le]
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    rw [mul_comm C hR]; exact mul_le_mul_of_nonneg_left hE (by linarith)
  -- the three size conclusions from a single natural bound
  have finish : ∀ (cc : Circuit) (Q t : ℕ) (Ereg : ℝ), Ereg ≤ C → (Q : ℝ) ≤ y ^ Ereg → t ≤ Q →
      cc.gates.length ≤ Q → cc.wires ≤ Q →
      HMBinPacking.OutputsWithin G (unaryD n ++ unary m) (encodeCircuit cc) t →
      HMBinPacking.OutputsWithin G (unaryD n ++ unary m) (encodeCircuit cc)
          ⌊r ^ (C * hR)⌋₊ ∧
        (cc.gates.length : ℝ) ≤ r ^ (C * hR) ∧ (cc.wires : ℝ) ≤ r ^ (C * hR) := by
    intro cc Q t Ereg hE hQ htQ hgQ hwQ hout
    have hQC : (Q : ℝ) ≤ r ^ (C * hR) := hQ.trans (hyC Ereg hE)
    refine ⟨outputsWithin_mono (Nat.le_floor ((by exact_mod_cast htQ : (t : ℝ) ≤ Q).trans hQC)) hout,
      ((by exact_mod_cast hgQ : (cc.gates.length : ℝ) ≤ Q)).trans hQC,
      ((by exact_mod_cast hwQ : (cc.wires : ℝ) ≤ Q)).trans hQC⟩
  by_cases hreg : K * n ≤ m
  · -- regime m ≥ Kn: the quantum reduction from Theorem 1.7
    rw [if_pos hreg]
    set hN := (n ^ 2 + m - 1) / m
    set x := (m + n - 1) / n
    set T := x ^ (d * hN) with hT
    have hKn : (K : ℝ) * n ≤ m := by exact_mod_cast hreg
    have hr3 : 3 ≤ r := by rw [hr, le_div_iff₀ (by linarith)]; nlinarith
    obtain ⟨hTy, hTfl⟩ := clock_bounds r hR C₁ d hN x (by linarith) hhN hx1 hx2 hdC
    have h3n : (3 : ℝ) * n ≤ m := by nlinarith
    obtain ⟨hcomp, hpw⟩ := h17 n m hn h3n
    obtain ⟨hout1, hw1, hg1, hwu1, hs1⟩ := hG₁ n m T (computesWithin_mono hTfl hcomp)
    set Z := n + m + T + 1 with hZ
    have hZ1 : 1 ≤ Z := by omega
    have hrp := rpoly_le C₃ D₁ Z hD₁C hZ1
    have hout := (hG n m _ _).1 hreg (outputsWithin_mono (Nat.floor_le_of_le hrp) hout1)
    have hg1' : (circ₁ n m T).gates.length ≤ D₁ * Z ^ D₁ := by exact_mod_cast hg1.trans hrp
    have hwu1' : (circ₁ n m T).wires ≤ D₁ * Z ^ D₁ := by exact_mod_cast hwu1.trans hrp
    have htl := two_level D₁ D₃ Z (D₁ * Z ^ D₁) hZ1 le_rfl
    have hZy : (Z : ℝ) ≤ 4 * y ^ E₀ := by
      have a1 : (n : ℝ) ≤ y ^ E₀ := hny.trans (Real.rpow_le_rpow_of_exponent_le hy1 (by linarith))
      have a2 : (m : ℝ) ≤ y ^ E₀ := hmy.trans (Real.rpow_le_rpow_of_exponent_le hy1 hE₀a)
      have a3 : (T : ℝ) ≤ y ^ E₀ := hTy.trans (Real.rpow_le_rpow_of_exponent_le hy1 hE₀b)
      have a4 : (1 : ℝ) ≤ y ^ E₀ := Real.one_le_rpow hy1 hE₀0
      simp only [hZ]; push_cast; linarith
    have hQ : ((A₁ * Z ^ k₁ : ℕ) : ℝ) ≤ y ^ Cr1 := by
      push_cast
      exact chain k₁ hκ1 hyκ (by positivity) (by norm_num) hE₀0 (by positivity) hZy
    have htime : D₃ * (D₁ * Z ^ D₁ + n + m + T + 1) ^ D₃ ≤ A₁ * Z ^ k₁ := by
      have e : D₁ * Z ^ D₁ + n + m + T + 1 = D₁ * Z ^ D₁ + Z := by simp only [hZ]; ring
      rw [e]; exact le_of_add_le_left htl
    have hW : D₁ * Z ^ D₁ ≤ A₁ * Z ^ k₁ := le_of_add_le_right htl
    obtain ⟨f1, f2, f3⟩ := finish _ (A₁ * Z ^ k₁) _ Cr1 (by
        have : Cr1 ≤ max Cr1 Cr2 := le_max_left _ _; linarith) hQ htime
      (hg1'.trans hW) (hwu1'.trans hW) hout
    refine ⟨f1, hw1, f2, f3, ?_⟩
    -- success: Theorem 3.1 gives failure ≤ 2η + 3ⁿ(2/3)^m
    have havg : avgError Dec n m ≤ (2 : ℝ) ^ (-(c₁ * m)) := avgError_le Dec n m _ hpw
    have hcol := collision_term n m h3n
    have hm0 : (0 : ℝ) ≤ m := by positivity
    have q1 : (2 : ℝ) ^ (-(c₁ * m)) ≤ (2 : ℝ) ^ (-(a * m)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (by have := mul_le_mul_of_nonneg_right (min_le_left c₁ b) hm0; linarith)
    have q2 : (2 : ℝ) ^ (-(b * m)) ≤ (2 : ℝ) ^ (-(a * m)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (by have := mul_le_mul_of_nonneg_right (min_le_right c₁ b) hm0; linarith)
    have h3 : (3 : ℝ) = 2 ^ Real.logb 2 3 :=
      (Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)).symm
    have hexp : Real.logb 2 3 + -(a * m) ≤ -(c * m) := by
      have e1 : 2 * Real.logb 2 3 ≤ a * K := by rw [div_le_iff₀ ha0] at hKL; linarith
      have hKm : (K : ℝ) ≤ m := by nlinarith
      have e2 : a * K ≤ a * m := mul_le_mul_of_nonneg_left hKm ha0.le
      have e3 : c * m ≤ a / 2 * m := mul_le_mul_of_nonneg_right (min_le_left _ _) hm0
      linarith
    have q3 : 3 * (2 : ℝ) ^ (-(a * m)) ≤ (2 : ℝ) ^ (-(c * m)) := by
      calc 3 * (2 : ℝ) ^ (-(a * m)) = (2 : ℝ) ^ (Real.logb 2 3 + -(a * m)) := by
            rw [Real.rpow_add (by norm_num), ← h3]
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    linarith
  · -- regime κn ≤ m < Kn: exhaustive search
    rw [if_neg hreg]
    push Not at hreg
    obtain ⟨hout2, hw2, hg2, hwu2, hs2⟩ := hG₂ n m
    have hout := (hG n m _ _).2 hreg hout2
    have h2m := two_pow_bound κ r hR hκ1 n m K hrκ hnr hr hn hreg
    set Z := n + m + 2 ^ m + 1 with hZ
    have hZ1 : 1 ≤ Z := Nat.le_add_left 1 _
    have htl := two_level D₂ D₃ Z (D₂ * Z ^ D₂) hZ1 le_rfl
    have hZy : (Z : ℝ) ≤ 4 * y ^ (1 + 1 / δ + E₂) := by
      have hE : 0 ≤ 1 + 1 / δ + E₂ := by positivity
      have a1 : (n : ℝ) ≤ y ^ (1 + 1 / δ + E₂) :=
        hny.trans (Real.rpow_le_rpow_of_exponent_le hy1 (by linarith))
      have a2 : (m : ℝ) ≤ y ^ (1 + 1 / δ + E₂) :=
        hmy.trans (Real.rpow_le_rpow_of_exponent_le hy1 (by linarith))
      have a3 : (2 : ℝ) ^ m ≤ y ^ (1 + 1 / δ + E₂) :=
        h2m.trans (Real.rpow_le_rpow_of_exponent_le hy1 (by
          have : 0 < 1 / δ := by positivity
          linarith))
      have a4 : (1 : ℝ) ≤ y ^ (1 + 1 / δ + E₂) := Real.one_le_rpow hy1 hE
      simp only [hZ]; push_cast; linarith
    have hQ : ((A₂ * Z ^ k₂ : ℕ) : ℝ) ≤ y ^ Cr2 := by
      push_cast
      exact chain k₂ hκ1 hyκ (by positivity) (by norm_num) (by positivity) (by positivity) hZy
    have htime : D₃ * (D₂ * Z ^ D₂ + n + m + 1) ^ D₃ ≤ A₂ * Z ^ k₂ := by
      have hle : D₂ * Z ^ D₂ + n + m + 1 ≤ D₂ * Z ^ D₂ + Z := by
        have : n + m + 1 ≤ Z := by simp only [hZ]; exact Nat.add_le_add_right (Nat.le_add_right _ _) 1
        omega
      exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hle _)).trans (le_of_add_le_left htl)
    have hW : D₂ * Z ^ D₂ ≤ A₂ * Z ^ k₂ := le_of_add_le_right htl
    obtain ⟨f1, f2, f3⟩ := finish _ (A₂ * Z ^ k₂) _ Cr2 (by
        have : Cr2 ≤ max Cr1 Cr2 := le_max_right _ _; linarith) hQ htime
      (hg2.trans hW) (hwu2.trans hW) hout
    refine ⟨f1, hw2, f2, f3, ?_⟩
    -- success: Fact 1.2
    have hm' : (Real.logb 2 3 + (κ - Real.logb 2 3)) * n ≤ m := by
      have e : Real.logb 2 3 + (κ - Real.logb 2 3) = κ := by ring
      rw [e]; exact hm
    have hps := (hf2 n m).1 hm'
    have hmK : (m : ℝ) < K * n := by exact_mod_cast hreg
    have hexp : -(c₂ * n) ≤ -(c * m) := by
      have e3 : c ≤ c₂ / K := min_le_right _ _
      have hm0 : (0 : ℝ) ≤ m := by positivity
      have : c * m ≤ c₂ / K * m := mul_le_mul_of_nonneg_right e3 hm0
      have : c₂ / K * m ≤ c₂ / K * (K * n) :=
        mul_le_mul_of_nonneg_left hmK.le (div_nonneg hc₂.le hK0.le)
      have : c₂ / K * (K * n) = c₂ * n := by field_simp
      linarith
    have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp
    linarith

end T13

open F3SubsetSum in
theorem solution (κ : ℝ) (hκ : Real.logb 2 3 < κ) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (circ : ℕ → ℕ → Circuit) (C c : ℝ), 0 < C ∧ 0 < c ∧
      ∀ n m : ℕ, 1 ≤ n → κ * n ≤ m →
        HMBinPacking.OutputsWithin M (unaryD n ++ unary m) (encodeCircuit (circ n m))
            ⌊((m : ℝ) / n) ^ (C * (⌈(n : ℝ) ^ 2 / m⌉ : ℝ))⌋₊ ∧
          n * m + m ≤ (circ n m).wires ∧
          ((circ n m).gates.length : ℝ) ≤ ((m : ℝ) / n) ^ (C * (⌈(n : ℝ) ^ 2 / m⌉ : ℝ)) ∧
          ((circ n m).wires : ℝ) ≤ ((m : ℝ) / n) ^ (C * (⌈(n : ℝ) ^ 2 / m⌉ : ℝ)) ∧
          1 - (2 : ℝ) ^ (-(c * m)) ≤ successProb n m (circ n m) :=
  T13.main_1_3 κ hκ
