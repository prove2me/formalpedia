-- Prove2me | solution 3 for BitDFT.asymptotic_integer_multiplication_implies_dft
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T00:06:32.958947+00:00
-- url     : https://prove2.me/submissions/223dcc06-dc80-463b-adbe-3d94fac36213
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_BitDFT_Numerics
import Theorems.Thm_BitDFT_integer_multiplication_implies_dft
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open BitDFT IntMul
set_option maxHeartbeats 800000

theorem solution (g : ℕ → ℝ) (hg : MulTimeBound g) :
    ∃ A : MultitapeTM, ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ,
      ∀ n b : ℕ, 1 ≤ n → 1 ≤ b → N ≤ guardPrecision n b →
        ∀ U : Fin n → ℤ × ℤ, vectorDisc (guardPrecision n b) U →
          ∃ V : Fin n → ℤ × ℤ,
            Computes A (requestedInput b U)
              (encVector (guardPrecision n b + lg n + 1) V)
              (C * transferCost g n (guardPrecision n b)) ∧
            (∀ k, ‖value (guardPrecision n b) (V k)‖ ≤ n) ∧
            (∀ k, ‖value (guardPrecision n b) (V k) -
              dft (fun j => value (guardPrecision n b) (U j)) k‖ < ((2 : ℝ)^b)⁻¹) := by
  rcases hg with ⟨M, hsmall, c, hc, N, hlarge⟩
  choose R hR using hsmall
  let S : ℕ → ℝ := fun s =>
    if N ≤ s then c * g s else if hs : 1 ≤ s then R s hs else 0
  have hM : Multiplier M S := by
    intro s hs
    by_cases hN : N ≤ s
    · simpa [S, hN] using hlarge s hN hs
    · simpa [S, hN, hs] using hR s hs
  have htime_nonneg (s : ℕ) (hs : 1 ≤ s) : 0 ≤ S s := by
    obtain ⟨t, ht, _⟩ := hM s hs (List.replicate s false) (List.replicate s false)
      (by simp) (by simp)
    exact le_trans (Nat.cast_nonneg t) ht
  obtain ⟨A, C, hC, hA⟩ := BitDFT.integer_multiplication_implies_dft M S hM
  refine ⟨A, C * (c + 1), mul_pos hC (by linarith), N, ?_⟩
  intro n b hn hb hNq U hU
  let q := guardPrecision n b
  have hq : 1 ≤ q := by dsimp [q, guardPrecision]; omega
  have hqN : N ≤ q := hNq
  have hqle : q ≤ n * q := by
    calc
      q = 1 * q := by simp
      _ ≤ n * q := Nat.mul_le_mul_right q hn
  have hnqN : N ≤ n * q := hqN.trans hqle
  have hSq : S q = c * g q := by simp [S, hqN]
  have hSnq : S (n * q) = c * g (n * q) := by simp [S, hnqN]
  have hGq : 0 ≤ g q := by
    have h := htime_nonneg q hq
    rw [hSq] at h
    nlinarith
  have hGnq : 0 ≤ g (n*q) := by
    have h := htime_nonneg (n*q) (by nlinarith)
    rw [hSnq] at h
    nlinarith
  have hcost : transferCost S n q ≤ (c + 1) * transferCost g n q := by
    dsimp [transferCost]
    rw [hSq, hSnq]
    have hsetup1 : 0 ≤ (q : ℝ) * (lg q : ℝ)^2 :=
      mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    have hsetup2 : 0 ≤ (n : ℝ) * q := by positivity
    have hsetup : 0 ≤ (q : ℝ) * (lg q : ℝ)^2 + (n : ℝ) * q :=
      add_nonneg hsetup1 hsetup2
    nlinarith
  obtain ⟨V, hrun, hbound, herr⟩ := hA n b hn hb U hU
  obtain ⟨t, ht, hout⟩ := hrun
  refine ⟨V, ⟨t, ?_, hout⟩, hbound, herr⟩
  calc
    (t : ℝ) ≤ C * transferCost S n q := ht
    _ ≤ C * ((c + 1) * transferCost g n q) :=
      mul_le_mul_of_nonneg_left hcost hC.le
    _ = (C * (c + 1)) * transferCost g n q := by ring
