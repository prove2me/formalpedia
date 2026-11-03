-- Prove2me | solution 5 for BitDFT.runtime_bound_substitution
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-02T15:39:42.912893+00:00
-- url     : https://prove2.me/submissions/5ea30a8b-93e8-46ab-83f6-3b3b796794a9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_BitDFT_Numerics
import Definitions.Def_IntMul_HvdH_KronMul
import Theorems.Thm_BitDFT_integer_multiplication_implies_dft
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open BitDFT

theorem solution
    (M : IntMul.MultitapeTM) (T B : ℕ → ℝ) (hM : Multiplier M T)
    (hB : ∀ n, 1 ≤ n → T n ≤ B n) :
    ∃ A : IntMul.MultitapeTM, ∃ C : ℝ, 0 < C ∧
      ∀ n b : ℕ, 1 ≤ n → 1 ≤ b →
        ∀ U : Fin n → ℤ × ℤ, vectorDisc (guardPrecision n b) U →
          ∃ V : Fin n → ℤ × ℤ,
            Computes A (requestedInput b U)
              (encVector (guardPrecision n b + IntMul.lg n + 1) V)
              (C * transferCost B n (guardPrecision n b)) ∧
            (∀ k, ‖value (guardPrecision n b) (V k)‖ ≤ n) ∧
            (∀ k, ‖value (guardPrecision n b) (V k) -
              dft (fun j => value (guardPrecision n b) (U j)) k‖ < ((2 : ℝ) ^ b)⁻¹) := by
  obtain ⟨A, C, hC, h⟩ := BitDFT.integer_multiplication_implies_dft M T hM
  refine ⟨A, C, hC, ?_⟩
  intro n b hn hb U hU
  obtain ⟨V, hcomp, h1, h2⟩ := h n b hn hb U hU
  refine ⟨V, ?_, h1, h2⟩
  obtain ⟨t, ht, hHalt⟩ := hcomp
  refine ⟨t, le_trans ht ?_, hHalt⟩
  have hq : 1 ≤ guardPrecision n b := by unfold guardPrecision; omega
  have hnq : 1 ≤ n * guardPrecision n b := by
    have : 0 < n * guardPrecision n b := Nat.mul_pos (by omega) (by omega)
    omega
  have hmono : transferCost T n (guardPrecision n b) ≤
      transferCost B n (guardPrecision n b) := by
    unfold transferCost
    have h1' : T (n * guardPrecision n b) ≤ B (n * guardPrecision n b) := hB _ hnq
    have h2' : T (guardPrecision n b) ≤ B (guardPrecision n b) := hB _ hq
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
    have := mul_le_mul_of_nonneg_left h2' hn0
    linarith
  exact mul_le_mul_of_nonneg_left hmono (le_of_lt hC)
