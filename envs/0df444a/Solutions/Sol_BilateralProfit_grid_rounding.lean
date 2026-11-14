-- Prove2me | solution 1 for BilateralProfit.grid_rounding
-- status  : ACCEPTED   (prove)
-- author  : @sim2000dg
-- created : 2026-11-13T16:45:22.008381+00:00
-- url     : https://prove2.me/submissions/9ac86ad2-6b92-4b86-95c6-84e12c43cc73

import Definitions.Def_BilateralProfit_Algorithm1

namespace BilateralProfit.GridRoundingFacts

variable {K : ℕ}

theorem ceil_le_grid (K : ℕ) (s : ℝ) (hs : s ≤ 1) : ⌈(K : ℝ) * s⌉₊ ≤ K := by
  apply Nat.ceil_le.mpr
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg K)

theorem floor_le_grid (K : ℕ) (b : ℝ) (hb : b ≤ 1) : ⌊(K : ℝ) * b⌋₊ ≤ K := by
  have h := Nat.floor_mono (show (K : ℝ) * b ≤ (K : ℝ) by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg K))
  simpa using h

theorem seller_rounded_iff (hK : 0 < K) (s : ℝ) (i : Fin (K + 1)) :
    s ≤ (i : ℝ) / K ↔ (⌈(K : ℝ) * s⌉₊ : ℝ) / K ≤ (i : ℝ) / K := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  rw [le_div_iff₀ hKr, div_le_div_iff_of_pos_right hKr]
  constructor
  · intro h
    exact_mod_cast (Nat.ceil_le.mpr (show (K : ℝ) * s ≤ (i : ℝ) by nlinarith))
  · intro h
    have hi : ⌈(K : ℝ) * s⌉₊ ≤ (i : ℕ) := by exact_mod_cast h
    have hh := Nat.ceil_le.mp hi
    nlinarith

theorem buyer_rounded_iff (hK : 0 < K) (b : ℝ) (hb : 0 ≤ b) (j : Fin (K + 1)) :
    (j : ℝ) / K ≤ b ↔ (j : ℝ) / K ≤ (⌊(K : ℝ) * b⌋₊ : ℝ) / K := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  rw [div_le_iff₀ hKr, div_le_div_iff_of_pos_right hKr]
  constructor
  · intro h
    have hj : (j : ℕ) ≤ ⌊(K : ℝ) * b⌋₊ := Nat.le_floor (by nlinarith)
    exact_mod_cast hj
  · intro h
    have hf := Nat.floor_le (mul_nonneg (Nat.cast_nonneg K) hb)
    nlinarith

theorem trades_rounded (hK : 0 < K) (s b : ℝ) (hb : 0 ≤ b) (a : Act K) :
    Trades (s, b) (pt K a.1) ↔
      Trades ((⌈(K : ℝ) * s⌉₊ : ℝ) / K, (⌊(K : ℝ) * b⌋₊ : ℝ) / K) (pt K a.1) := by
  exact and_congr (seller_rounded_iff hK s a.1.1) (buyer_rounded_iff hK b hb a.1.2)

theorem alg1_eq_of_feedback (K T : ℕ) (S S' : Fin T → ℝ × ℝ)
    (h : ∀ (t : Fin T) (a : Act K), Trades (S t) (pt K a.1) ↔ Trades (S' t) (pt K a.1))
    (ω : Fin T → Fin (Jpar K)) : alg1 K T S ω = alg1 K T S' ω := by
  unfold alg1
  simp_rw [h]

end BilateralProfit.GridRoundingFacts

namespace BilateralProfit

theorem cert_grid_rounding_payload (K : ℕ) (hK : 0 < K) :
    (∀ s b : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
      (∃ x : Grid K, pt K x = ((⌈(K : ℝ) * s⌉₊ : ℝ) / K, (⌊(K : ℝ) * b⌋₊ : ℝ) / K)) ∧
      ∀ a : Act K,
        tradeBit (s, b) (pt K a.1) =
            tradeBit ((⌈(K : ℝ) * s⌉₊ : ℝ) / K, (⌊(K : ℝ) * b⌋₊ : ℝ) / K) (pt K a.1) ∧
          profit (s, b) (pt K a.1) =
            profit ((⌈(K : ℝ) * s⌉₊ : ℝ) / K, (⌊(K : ℝ) * b⌋₊ : ℝ) / K) (pt K a.1)) ∧
    ∀ (T : ℕ) (S : Fin T → ℝ × ℝ), (∀ t, S t ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) →
      ∀ ω : Fin T → Fin (Jpar K),
        runW (alg1 K T S ω) =
          runW (alg1 K T (fun t => ((⌈(K : ℝ) * (S t).1⌉₊ : ℝ) / K,
            (⌊(K : ℝ) * (S t).2⌋₊ : ℝ) / K)) ω) := by
  classical
  constructor
  · intro s b hs hb
    refine ⟨?_, ?_⟩
    · refine ⟨(⟨⌈(K : ℝ) * s⌉₊, Nat.lt_succ_of_le (GridRoundingFacts.ceil_le_grid K s hs.2)⟩,
        ⟨⌊(K : ℝ) * b⌋₊, Nat.lt_succ_of_le (GridRoundingFacts.floor_le_grid K b hb.2)⟩), rfl⟩
    · intro a
      have heq := propext (GridRoundingFacts.trades_rounded hK s b hb.1 a)
      constructor
      · simp only [tradeBit, heq]
      · simp only [profit, tradeBit, heq]
  · intro T S hS ω
    apply congrArg runW
    apply GridRoundingFacts.alg1_eq_of_feedback K T S _ _ ω
    intro t a
    exact GridRoundingFacts.trades_rounded hK (S t).1 (S t).2 (hS t).2.1 a

end BilateralProfit

open BilateralProfit

theorem solution (K : ℕ) (hK : 0 < K) :
    (∀ s b : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
      (∃ x : Grid K, pt K x = ((⌈(K : ℝ) * s⌉₊ : ℝ) / K, (⌊(K : ℝ) * b⌋₊ : ℝ) / K)) ∧
      ∀ a : Act K,
        tradeBit (s, b) (pt K a.1) =
            tradeBit ((⌈(K : ℝ) * s⌉₊ : ℝ) / K, (⌊(K : ℝ) * b⌋₊ : ℝ) / K) (pt K a.1) ∧
          profit (s, b) (pt K a.1) =
            profit ((⌈(K : ℝ) * s⌉₊ : ℝ) / K, (⌊(K : ℝ) * b⌋₊ : ℝ) / K) (pt K a.1)) ∧
    ∀ (T : ℕ) (S : Fin T → ℝ × ℝ), (∀ t, S t ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) →
      ∀ ω : Fin T → Fin (Jpar K),
        runW (alg1 K T S ω) =
          runW (alg1 K T (fun t => ((⌈(K : ℝ) * (S t).1⌉₊ : ℝ) / K,
            (⌊(K : ℝ) * (S t).2⌋₊ : ℝ) / K)) ω) := by exact cert_grid_rounding_payload K hK

