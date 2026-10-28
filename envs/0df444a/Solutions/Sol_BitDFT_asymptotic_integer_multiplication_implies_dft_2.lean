-- Prove2me | solution 2 for BitDFT.asymptotic_integer_multiplication_implies_dft
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T12:41:30.354344+00:00
-- url     : https://prove2.me/submissions/212171e7-6928-4853-9870-6b39fa287488
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_BitDFT_integer_multiplication_implies_dft
import Theorems.Thm_BitDFT_multiplier_time_linear
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
set_option autoImplicit false
noncomputable section
open BitDFT

lemma multiplies_nonneg (M : IntMul.MultitapeTM) (s : ℕ) (t : ℝ)
    (h : IntMul.MultipliesAt M s t) : 0 ≤ t := by
  exact (Nat.cast_nonneg (2 * s)).trans (BitDFT.multiplier_time_linear M s t h)

theorem solution
    (g : ℕ → ℝ) (hg : IntMul.MulTimeBound g) :
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
  classical
  obtain ⟨M, htotal, c, hc, N, hlarge⟩ := hg
  let T : ℕ → ℝ := fun s => if N ≤ s then c * g s else
    if hs : 1 ≤ s then Classical.choose (htotal s hs) else 0
  have hM : Multiplier M T := by
    intro s hs
    by_cases hNs : N ≤ s
    · simpa only [T, if_pos hNs] using hlarge s hNs hs
    · simpa only [T, if_neg hNs, dif_pos hs] using Classical.choose_spec (htotal s hs)
  obtain ⟨A, C, hC, hA⟩ := BitDFT.integer_multiplication_implies_dft M T hM
  refine ⟨A, C * (c + 1), mul_pos hC (by linarith), N, ?_⟩
  intro n b hn hb hN U hU
  obtain ⟨V, ht, hdisc, herr⟩ := hA n b hn hb U hU
  refine ⟨V, ?_, hdisc, herr⟩
  have hq : 1 ≤ guardPrecision n b := by unfold guardPrecision; omega
  have hnq : guardPrecision n b ≤ n * guardPrecision n b := by
    exact Nat.le_mul_of_pos_left _ hn
  have hgq : 0 ≤ g (guardPrecision n b) := by
    have h := multiplies_nonneg M _ _ (hlarge _ hN hq)
    exact nonneg_of_mul_nonneg_right h hc
  have hgnq : 0 ≤ g (n * guardPrecision n b) := by
    have h := multiplies_nonneg M _ _ (hlarge _ (hN.trans hnq) (hq.trans hnq))
    exact nonneg_of_mul_nonneg_right h hc
  have hsmall : T (guardPrecision n b) = c * g (guardPrecision n b) := by simp only [T, if_pos hN]
  have hbig : T (n * guardPrecision n b) = c * g (n * guardPrecision n b) := by simp only [T, if_pos (hN.trans hnq)]
  have hcost : transferCost T n (guardPrecision n b) ≤
      (c + 1) * transferCost g n (guardPrecision n b) := by
    unfold transferCost
    rw [hsmall, hbig]
    have hsum : 0 ≤ g (n * guardPrecision n b) + (n : ℝ) * g (guardPrecision n b) :=
      add_nonneg hgnq (mul_nonneg (Nat.cast_nonneg n) hgq)
    have hsetup : 0 ≤ (guardPrecision n b : ℝ) * (IntMul.lg (guardPrecision n b) : ℝ)^2 + (n : ℝ) * guardPrecision n b :=
      add_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
        (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    have h := add_nonneg hsum (mul_nonneg hc.le hsetup)
    linear_combination h
  obtain ⟨t, htime, hout⟩ := ht
  refine ⟨t, htime.trans ?_, hout⟩
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hcost hC.le
