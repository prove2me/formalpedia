-- Prove2me | solution 1 for BilateralProfit.lemma_A_6
-- status  : ACCEPTED   (prove)
-- author  : @sim2000dg
-- created : 2026-11-13T16:47:09.245344+00:00
-- url     : https://prove2.me/submissions/58ee2d6f-1c94-42eb-bc0b-24181cc912a5

import Definitions.Def_BilateralProfit_Model

namespace BilateralProfit.A6Submission

lemma pointwise_grid_comparator (K : ℕ) (hK : 1 ≤ K) (p q : ℝ)
    (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q ≤ 1) :
    ∃ a' : Act K, ∀ s b : ℝ,
      profit (s, b) (p, q) ≤ profit (s, b) (pt K a'.1) + 2 / K := by
  classical
  have hk : (0 : ℝ) < K := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hK)
  have hp1 : p ≤ 1 := hpq.trans hq
  have hq0 : 0 ≤ q := hp.trans hpq
  let u : ℕ := ⌈(K : ℝ) * p⌉₊
  let d : ℕ := ⌊(K : ℝ) * q⌋₊
  have huK : u ≤ K := by
    apply Nat.ceil_le.mpr
    nlinarith
  have hdK : d ≤ K := by
    apply Nat.floor_le_of_le
    nlinarith
  have hu : (u : ℝ) < (K : ℝ) * p + 1 :=
    Nat.ceil_lt_add_one (mul_nonneg hk.le hp)
  have hd : (K : ℝ) * q < (d : ℝ) + 1 := Nat.lt_floor_add_one _
  have hpup : p ≤ (u : ℝ) / K := by
    apply (le_div_iff₀ hk).mpr
    have := Nat.le_ceil ((K : ℝ) * p)
    dsimp [u]
    nlinarith
  have hdownq : (d : ℝ) / K ≤ q := by
    apply (div_le_iff₀ hk).mpr
    have := Nat.floor_le (mul_nonneg hk.le hq0)
    dsimp [d]
    nlinarith
  have htwo : (0 : ℝ) ≤ 2 / K := by positivity
  by_cases hud : u ≤ d
  · let a' : Act K :=
      ⟨(⟨u, Nat.lt_succ_of_le huK⟩, ⟨d, Nat.lt_succ_of_le hdK⟩), hud⟩
    refine ⟨a', ?_⟩
    intro s b
    change profit (s, b) (p, q) ≤
      profit (s, b) ((u : ℝ) / K, (d : ℝ) / K) + 2 / K
    have hudr : (u : ℝ) ≤ d := by exact_mod_cast hud
    have hspread0 : 0 ≤ (d : ℝ) / K - (u : ℝ) / K :=
      sub_nonneg.mpr (div_le_div_of_nonneg_right hudr hk.le)
    have hspread : q - p ≤ (d : ℝ) / K - (u : ℝ) / K + 2 / K := by
      rw [show (d : ℝ) / K - (u : ℝ) / K + 2 / K = ((d : ℝ) - u + 2) / K by ring]
      apply (le_div_iff₀ hk).mpr
      nlinarith
    by_cases ht : Trades (s, b) (p, q)
    · have ht' : Trades (s, b) ((u : ℝ) / K, (d : ℝ) / K) :=
        ⟨ht.1.trans hpup, hdownq.trans ht.2⟩
      simpa only [profit, tradeBit, if_pos ht, if_pos ht', mul_one] using hspread
    · unfold profit tradeBit
      rw [if_neg ht, mul_zero]
      split_ifs <;> simp only [mul_one, mul_zero] <;> linarith
  · let a' : Act K := ⟨(0, 0), le_rfl⟩
    refine ⟨a', ?_⟩
    intro s b
    have hudr : (d : ℝ) < u := by exact_mod_cast (lt_of_not_ge hud)
    have hspread : q - p ≤ 2 / K := by
      apply (le_div_iff₀ hk).mpr
      nlinarith
    have hz : profit (s, b) (pt K a'.1) = 0 := by
      simp [a', pt, profit]
    rw [hz, zero_add]
    unfold profit tradeBit
    split_ifs <;> simp only [mul_one, mul_zero] <;> linarith

end BilateralProfit.A6Submission

namespace BilateralProfit

theorem cert_lemma_A_6_submission (K : ℕ) (hK : 1 ≤ K) (p q : ℝ)
    (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q ≤ 1) :
    ∃ a' : Act K,
      (∀ s b : ℝ, profit (s, b) (p, q) ≤ profit (s, b) (pt K a'.1) + 2 / K) ∧
      ∀ (T : ℕ) (S : Fin T → ℝ × ℝ) (X : Fin T → ℝ),
        ∑ t, (profit (S t) (p, q) - X t) ≤
          ∑ t, (profit (S t) (pt K a'.1) - X t) + 2 * T / K := by
  obtain ⟨a', hpoint⟩ := A6Submission.pointwise_grid_comparator K hK p q hp hpq hq
  refine ⟨a', hpoint, ?_⟩
  intro T S X
  calc
    ∑ t, (profit (S t) (p, q) - X t) ≤
        ∑ t, ((profit (S t) (pt K a'.1) - X t) + 2 / K) := by
      apply Finset.sum_le_sum
      intro t _
      have h := hpoint (S t).1 (S t).2
      change profit (S t) (p, q) ≤ profit (S t) (pt K a'.1) + 2 / K at h
      linarith
    _ = ∑ t, (profit (S t) (pt K a'.1) - X t) + 2 * T / K := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

end BilateralProfit


open BilateralProfit

theorem solution (K : ℕ) (hK : 1 ≤ K) (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q ≤ 1) :
    ∃ a' : Act K,
      (∀ s b : ℝ, profit (s, b) (p, q) ≤ profit (s, b) (pt K a'.1) + 2 / K) ∧
      ∀ (T : ℕ) (S : Fin T → ℝ × ℝ) (X : Fin T → ℝ),
        ∑ t, (profit (S t) (p, q) - X t) ≤ ∑ t, (profit (S t) (pt K a'.1) - X t) + 2 * T / K := by exact BilateralProfit.cert_lemma_A_6_submission K hK p q hp hpq hq

