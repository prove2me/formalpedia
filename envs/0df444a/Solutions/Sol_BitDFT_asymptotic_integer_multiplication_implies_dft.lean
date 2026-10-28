-- Prove2me | solution 1 for BitDFT.asymptotic_integer_multiplication_implies_dft
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T12:40:16.346647+00:00
-- url     : https://prove2.me/submissions/4ad802f4-43c8-4e64-9d82-ff910e480519
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
  obtain ⟨M, hT, c, hc, n₀, hb⟩ := hg
  let T : ℕ → ℝ := fun n =>
    if n₀ ≤ n then c * g n else if h : 1 ≤ n then Classical.choose (hT n h) else 0
  have hM : Multiplier M T := by
    intro n hn
    by_cases h0 : n₀ ≤ n
    · simp only [T, if_pos h0]; exact hb n h0 hn
    · simp only [T, if_neg h0, dif_pos hn]; exact Classical.choose_spec (hT n hn)
  have hgpos : ∀ m, n₀ ≤ m → 1 ≤ m → 0 ≤ g m := by
    intro m hm h1
    obtain ⟨t, ht, -⟩ := hb m hm h1 (List.replicate m false) (List.replicate m false)
      (by simp) (by simp)
    have : 0 ≤ c * g m := le_trans (Nat.cast_nonneg t) ht
    exact nonneg_of_mul_nonneg_right this hc
  obtain ⟨A, C, hC, hA⟩ := BitDFT.integer_multiplication_implies_dft M T hM
  refine ⟨A, C * max c 1, mul_pos hC (lt_max_of_lt_right one_pos), n₀ ⊔ 1,
    fun n b hn hb' hN U hU => ?_⟩
  obtain ⟨V, ⟨t, ht, hh⟩, h1, h2⟩ := hA n b hn hb' U hU
  refine ⟨V, ⟨t, ?_, hh⟩, h1, h2⟩
  have key : ∀ p : ℕ, n₀ ⊔ 1 ≤ p → transferCost T n p ≤ max c 1 * transferCost g n p := by
    intro p hN
    have hp0 : n₀ ≤ p := le_trans le_sup_left hN
    have hp1 : 1 ≤ p := le_trans le_sup_right hN
    have hnp : p ≤ n * p := Nat.le_mul_of_pos_left p hn
    have hTp : T p = c * g p := by simp [T, hp0]
    have hTnp : T (n * p) = c * g (n * p) := by simp [T, le_trans hp0 hnp]
    have g1 := hgpos p hp0 hp1
    have g2 := hgpos (n * p) (le_trans hp0 hnp) (le_trans hp1 hnp)
    simp only [transferCost, hTp, hTnp]
    have hm1 : c ≤ max c 1 := le_max_left _ _
    have hm2 : (1 : ℝ) ≤ max c 1 := le_max_right _ _
    have hr : 0 ≤ (p : ℝ) * (IntMul.lg p : ℝ) ^ 2 + (n : ℝ) * p := by positivity
    have hn0 : (0 : ℝ) ≤ n := by positivity
    have e1 := mul_le_mul_of_nonneg_right hm1 g1
    have e2 := mul_le_mul_of_nonneg_right hm1 g2
    have e3 : (p : ℝ) * (IntMul.lg p : ℝ) ^ 2 + (n : ℝ) * p ≤
        max c 1 * ((p : ℝ) * (IntMul.lg p : ℝ) ^ 2 + (n : ℝ) * p) := by
      simpa using mul_le_mul_of_nonneg_right hm2 hr
    have e4 := mul_le_mul_of_nonneg_left e1 hn0
    linear_combination e2 + e4 + e3
  have hle := key _ hN
  calc (t : ℝ) ≤ C * transferCost T n (guardPrecision n b) := ht
    _ ≤ C * (max c 1 * transferCost g n (guardPrecision n b)) := mul_le_mul_of_nonneg_left hle hC.le
    _ = _ := by ring
