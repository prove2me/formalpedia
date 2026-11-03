-- Prove2me | solution 4 for BitDFT.asymptotic_integer_multiplication_implies_dft
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-02T15:41:12.756839+00:00
-- url     : https://prove2.me/submissions/ce1b0057-9f97-4815-a573-5f64b0ac3d3c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_BitDFT_Numerics
import Definitions.Def_IntMul_HvdH_KronMul
import Theorems.Thm_BitDFT_integer_multiplication_implies_dft
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open BitDFT

theorem solution (g : ℕ → ℝ) (hg : IntMul.MulTimeBound g) :
    ∃ A : IntMul.MultitapeTM, ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ,
      ∀ n b : ℕ, 1 ≤ n → 1 ≤ b → N ≤ guardPrecision n b →
        ∀ U : Fin n → ℤ × ℤ, vectorDisc (guardPrecision n b) U →
          ∃ V : Fin n → ℤ × ℤ,
            Computes A (requestedInput b U)
              (encVector (guardPrecision n b + IntMul.lg n + 1) V)
              (C * transferCost g n (guardPrecision n b)) ∧
            (∀ k, ‖value (guardPrecision n b) (V k)‖ ≤ n) ∧
            (∀ k, ‖value (guardPrecision n b) (V k) -
              dft (fun j => value (guardPrecision n b) (U j)) k‖ < ((2 : ℝ) ^ b)⁻¹) := by
  obtain ⟨M, hex, c, hc, n₀, hn₀⟩ := hg
  classical
  let s : ℕ → ℝ := fun n => if h : 1 ≤ n then Classical.choose (hex n h) else 0
  have hs : ∀ n (h : 1 ≤ n), IntMul.MultipliesAt M n (s n) := by
    intro n h
    simp only [s, dif_pos h]
    exact Classical.choose_spec (hex n h)
  let T : ℕ → ℝ := fun n => if n < n₀ then s n else c * g n
  have hT : Multiplier M T := by
    intro n hn
    simp only [T]
    split_ifs with h
    · exact hs n hn
    · exact hn₀ n (by omega) hn
  obtain ⟨A, C, hC, hmain⟩ := BitDFT.integer_multiplication_implies_dft M T hT
  refine ⟨A, C * max c 1, mul_pos hC (lt_of_lt_of_le zero_lt_one (le_max_right c 1)),
    max n₀ (2 ^ n₀ + 1), ?_⟩
  intro n b hn hb hN U hU
  set q := guardPrecision n b with hqdef
  have hq1 : 1 ≤ q := by unfold q guardPrecision; omega
  have hq_n₀ : n₀ ≤ q := le_trans (le_max_left n₀ (2 ^ n₀ + 1)) hN
  have hnq_n₀ : n₀ ≤ n * q := le_trans hq_n₀ (Nat.le_mul_of_pos_left q hn)
  have hnq1 : 1 ≤ n * q := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  obtain ⟨V, hcomp, h1, h2⟩ := hmain n b hn hb U hU
  refine ⟨V, ?_, h1, h2⟩
  obtain ⟨t, ht, hHalt⟩ := hcomp
  refine ⟨t, le_trans ht ?_, hHalt⟩
  have hT1 : T (n * q) = c * g (n * q) := by
    simp only [T]
    rw [if_neg (by omega : ¬ n * q < n₀)]
  have hT2 : T q = c * g q := by
    simp only [T]
    rw [if_neg (by omega : ¬ q < n₀)]
  have hgnq : 0 ≤ g (n * q) := by
    obtain ⟨u, hu, _⟩ :=
      hn₀ (n * q) hnq_n₀ hnq1 (IntMul.bin (n * q) 0) (IntMul.bin (n * q) 0)
        (by simp [IntMul.bin]) (by simp [IntMul.bin])
    have : (0 : ℝ) ≤ c * g (n * q) := le_trans (Nat.cast_nonneg u) hu
    exact nonneg_of_mul_nonneg_right this hc
  have hgq : 0 ≤ g q := by
    obtain ⟨u, hu, _⟩ :=
      hn₀ q hq_n₀ hq1 (IntMul.bin q 0) (IntMul.bin q 0)
        (by simp [IntMul.bin]) (by simp [IntMul.bin])
    have : (0 : ℝ) ≤ c * g q := le_trans (Nat.cast_nonneg u) hu
    exact nonneg_of_mul_nonneg_right this hc
  have hstep : transferCost T n q ≤ max c 1 * transferCost g n q := by
    set K : ℝ := max c 1 with hK
    set R : ℝ := (q : ℝ) * (IntMul.lg q : ℝ) ^ 2 + (n : ℝ) * (q : ℝ) with hRdef
    have hTeq : transferCost T n q = c * g (n * q) + (n : ℝ) * (c * g q) + R := by
      unfold transferCost
      rw [hT1, hT2, hRdef]
      ring
    have hGeq : transferCost g n q = g (n * q) + (n : ℝ) * g q + R := by
      unfold transferCost
      rw [hRdef]
      ring
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
    have hq0 : (0 : ℝ) ≤ (q : ℝ) := by positivity
    have hAB : 0 ≤ g (n * q) + (n : ℝ) * g q :=
      add_nonneg hgnq (mul_nonneg hn0 hgq)
    have hR0 : 0 ≤ R := by
      rw [hRdef]
      exact add_nonneg (mul_nonneg hq0 (sq_nonneg _)) (mul_nonneg hn0 hq0)
    have hAK : c ≤ K := le_max_left c 1
    have h1K : (1 : ℝ) ≤ K := le_max_right c 1
    rw [hTeq, hGeq]
    calc c * g (n * q) + (n : ℝ) * (c * g q) + R
        = c * (g (n * q) + (n : ℝ) * g q) + R := by ring
      _ ≤ K * (g (n * q) + (n : ℝ) * g q) + R := by
          have h := mul_le_mul_of_nonneg_right hAK hAB
          linarith
      _ ≤ K * (g (n * q) + (n : ℝ) * g q) + K * R := by
          have h : (1 : ℝ) * R ≤ K * R := mul_le_mul_of_nonneg_right h1K hR0
          linarith
      _ = K * (g (n * q) + (n : ℝ) * g q + R) := by ring
  calc C * transferCost T n q ≤ C * (max c 1 * transferCost g n q) :=
        mul_le_mul_of_nonneg_left hstep (le_of_lt hC)
    _ = C * max c 1 * transferCost g n q := by ring
