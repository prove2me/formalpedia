-- Prove2me | solution 1 for DigitalPrivacy.Welfare.proposition_5_i
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-17T16:55:35.247717+00:00
-- url     : https://prove2.me/submissions/3dfd9b83-0a86-423a-ab98-0411bf1e2369

import Definitions.Def_DigitalPrivacy_Welfare_Setting

open DigitalPrivacy.Welfare
open DigitalPrivacy.Strategy (abar)

private lemma priv_nonneg {β ρ ξ C : ℝ} (hb : β < 1) (hr : 0 ≤ ρ)
    (hx : 0 ≤ ξ) (hC : 0 ≤ C) : 0 ≤ abar β ρ ξ C := by
  have hb' : 0 < 1 - β := sub_pos.mpr hb
  unfold abar
  split_ifs <;> positivity

private lemma priv_welfare_order (a b α ψ C : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    (α * (a ^ 2 / 2) + (1 - α) * (a - ψ * C) ≤
      α * (b ^ 2 / 2) + (1 - α) * (b - ψ * C)) ↔ a ≤ b := by
  constructor
  · intro h
    by_contra hab
    have hba : b < a := lt_of_not_ge hab
    have hs : b ^ 2 < a ^ 2 := (sq_lt_sq₀ hb ha).mpr hba
    by_cases heq : α = 1
    · subst α
      nlinarith
    · have ha1 : 0 < 1 - α := sub_pos.mpr (lt_of_le_of_ne hα1 heq)
      have hm := mul_nonneg hα (sub_nonneg.mpr hs.le)
      have hm' := mul_pos ha1 (sub_pos.mpr hba)
      nlinarith
  · intro hab
    have hs : a ^ 2 ≤ b ^ 2 := (sq_le_sq₀ ha hb).mpr hab
    have hm := mul_nonneg hα (sub_nonneg.mpr hs)
    have hm' := mul_nonneg (sub_nonneg.mpr hα1) (sub_nonneg.mpr hab)
    nlinarith

private lemma priv_fixed (β ρ ψ α : ℝ) (h : PrintedBounds β ρ ψ 0 α) (C : ℝ)
    (hC : 0 ≤ C) (ξ : ℝ) (hξ : ξ ∈ Set.Icc (0 : ℝ) 1) :
    (∀ ξ' ∈ Set.Icc (0 : ℝ) 1, Pi β ρ ψ 0 ξ' C ≤ Pi β ρ ψ 0 ξ C) ↔
      (∀ ξ' ∈ Set.Icc (0 : ℝ) 1, W β ρ ψ 0 α ξ' C ≤ W β ρ ψ 0 α ξ C) := by
  have ha := priv_nonneg h.2.1 h.2.2.1 hξ.1 hC
  constructor <;> intro hh ξ' hξ'
  · have hb := priv_nonneg h.2.1 h.2.2.1 hξ'.1 hC
    have hc := hh ξ' hξ'
    simp only [Pi, sub_zero, one_mul, zero_mul, add_zero] at hc
    have hab : abar β ρ ξ' C ≤ abar β ρ ξ C := by linarith
    simpa only [W, Pi, DigitalPrivacy.Strategy.CS, sub_zero, one_mul, zero_mul,
      add_zero] using
      (priv_welfare_order _ _ α ψ C hb ha h.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2).mpr hab
  · have hb := priv_nonneg h.2.1 h.2.2.1 hξ'.1 hC
    have hc := hh ξ' hξ'
    simp only [W, Pi, DigitalPrivacy.Strategy.CS, sub_zero, one_mul, zero_mul,
      add_zero] at hc
    have hab := (priv_welfare_order _ _ α ψ C hb ha
      h.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2).mp hc
    simp only [Pi, sub_zero, one_mul, zero_mul, add_zero]
    linarith

theorem solution (β ρ ψ α : ℝ) (h : PrintedBounds β ρ ψ 0 α) (C : ℝ) (hC : 0 ≤ C)
    (ξ : ℝ) (hξ : ξ ∈ Set.Icc (0 : ℝ) 1) :
    (∀ ξ' ∈ Set.Icc (0 : ℝ) 1, Pi β ρ ψ 0 ξ' C ≤ Pi β ρ ψ 0 ξ C) ↔
      (∀ ξ' ∈ Set.Icc (0 : ℝ) 1, W β ρ ψ 0 α ξ' C ≤ W β ρ ψ 0 α ξ C) := by
  exact priv_fixed β ρ ψ α h C hC ξ hξ
