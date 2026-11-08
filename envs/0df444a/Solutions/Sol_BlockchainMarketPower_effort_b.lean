-- Prove2me | solution 1 for BlockchainMarketPower.effort_b
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:32:52.317895+00:00
-- url     : https://prove2.me/submissions/1799d2ae-8009-4ed5-b73c-b24816d43171

import Mathlib
import Definitions.Def_BlockchainMarketPower_Model

open BlockchainMarketPower in
theorem solution (n : ℕ) (hn : 1 ≤ n) (Ψ : ℝ) (hΨ : 0 ≤ Ψ) :
    (∀ e : ℝ, IsSymEffort .B n Ψ e ↔ e = min (Ψ ^ 2) 1) ∧
      (Accepts .B n Ψ (min (Ψ ^ 2) 1) ↔ 0 < Ψ) := by
  have hP : ∀ e' e : ℝ, supplierProfit .B n Ψ e' e = Real.sqrt e' * Ψ - e' / 2 := by
    intro e' e
    simp [supplierProfit, noRecallProb, rho]
  set estar := min (Ψ ^ 2) 1 with hes
  -- value at the optimum
  have hstar : estar ∈ Set.Icc (0 : ℝ) 1 := ⟨le_min (sq_nonneg _) zero_le_one, min_le_right _ _⟩
  -- gap formula
  have hgap : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      (Real.sqrt estar * Ψ - estar / 2) - (s * Ψ - s ^ 2 / 2) =
        if Ψ ≤ 1 then (s - Ψ) ^ 2 / 2 else (1 - s) * (Ψ - (1 + s) / 2) := by
    intro s hs0 hs1
    split_ifs with h
    · have : estar = Ψ ^ 2 := by rw [hes]; apply min_eq_left; nlinarith
      rw [this, Real.sqrt_sq hΨ]; ring
    · have : estar = 1 := by rw [hes]; apply min_eq_right; nlinarith
      rw [this, Real.sqrt_one]; ring
  have hgap_nonneg : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      0 ≤ (Real.sqrt estar * Ψ - estar / 2) - (s * Ψ - s ^ 2 / 2) := by
    intro s hs0 hs1
    rw [hgap s hs0 hs1]
    split_ifs with h
    · positivity
    · push_neg at h
      apply mul_nonneg (by linarith) (by linarith)
  have hopt : ∀ e' ∈ Set.Icc (0 : ℝ) 1, supplierProfit .B n Ψ e' estar ≤
      supplierProfit .B n Ψ estar estar := by
    intro e' he'
    rw [hP, hP]
    have hs0 := Real.sqrt_nonneg e'
    have hs1 : Real.sqrt e' ≤ 1 := Real.sqrt_le_one.mpr he'.2
    have hsq : Real.sqrt e' ^ 2 = e' := Real.sq_sqrt he'.1
    have := hgap_nonneg (Real.sqrt e') hs0 hs1
    rw [hsq] at this
    linarith
  refine ⟨fun e => ⟨fun ⟨he, hmax⟩ => ?_, fun h => h ▸ ⟨hstar, hopt⟩⟩, ?_⟩
  · have h1 := hmax estar hstar
    rw [hP, hP] at h1
    set s := Real.sqrt e with hs
    have hs0 : 0 ≤ s := Real.sqrt_nonneg e
    have hs1 : s ≤ 1 := Real.sqrt_le_one.mpr he.2
    have hsq : s ^ 2 = e := Real.sq_sqrt he.1
    have hg := hgap s hs0 hs1
    rw [hsq] at hg
    have hle : (Real.sqrt estar * Ψ - estar / 2) - (s * Ψ - e / 2) ≤ 0 := by linarith
    rw [hg] at hle
    split_ifs at hle with h
    · have : (s - Ψ) ^ 2 = 0 := by nlinarith [sq_nonneg (s - Ψ)]
      have hsΨ : s = Ψ := by nlinarith [sq_nonneg (s - Ψ)]
      rw [← hsq, hsΨ, hes, min_eq_left (by nlinarith)]
    · push_neg at h
      have h2 : 0 < Ψ - (1 + s) / 2 := by linarith
      have h3 : 1 - s ≤ 0 := by
        by_contra hc; push_neg at hc
        have := mul_pos hc h2
        linarith
      have hs' : s = 1 := by linarith
      rw [← hsq, hs', hes, min_eq_right (by nlinarith)]
      norm_num
  · unfold Accepts
    rw [hP]
    constructor
    · intro h
      by_contra hc
      push_neg at hc
      have hz : Ψ = 0 := le_antisymm hc hΨ
      rw [hz] at h
      have : estar = 0 := by rw [hes, hz]; simp
      rw [this] at h
      simp at h
    · intro hpos
      by_cases h : Ψ ≤ 1
      · have : estar = Ψ ^ 2 := by rw [hes]; apply min_eq_left; nlinarith
        rw [this, Real.sqrt_sq hΨ]
        nlinarith
      · push_neg at h
        have : estar = 1 := by rw [hes]; apply min_eq_right; nlinarith
        rw [this, Real.sqrt_one]
        linarith
