-- Prove2me | solution 1 for BankIntegration.Reversal.eq_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:40:02.111348+00:00
-- url     : https://prove2.me/submissions/c98d178e-b132-4e2b-8749-bb52be7f4770

import Mathlib
import Definitions.Def_BankIntegration_Reversal_Model

open BankIntegration.Reversal in
theorem solution (lam r θ : ℝ) (hlam : 1 < lam) (hr0 : -lam ≤ r) (hr1 : r ≤ lam) :
    IsOptimalRisk lam r θ ↔ θ = (lam + r) / 2 := by
  have hl : 0 < lam := by linarith
  have key : ∀ x : ℝ, (1 - x / lam) * (x - r) =
      (1 - (lam + r) / 2 / lam) * ((lam + r) / 2 - r) - (x - (lam + r) / 2) ^ 2 / lam := by
    intro x; field_simp; ring
  have hmem : (lam + r) / 2 ∈ Set.Icc 0 lam := ⟨by linarith, by linarith⟩
  constructor
  · rintro ⟨_, hopt⟩
    have h := hopt _ hmem
    rw [key θ, key ((lam + r) / 2)] at h
    have h2 : (θ - (lam + r) / 2) ^ 2 / lam ≤ 0 := by
      have : ((lam + r) / 2 - (lam + r) / 2) ^ 2 / lam = 0 := by ring
      linarith
    have h3 : (θ - (lam + r) / 2) ^ 2 ≤ 0 := by
      have := (div_le_iff₀ hl).mp h2; linarith
    have h4 : θ - (lam + r) / 2 = 0 := by nlinarith [sq_nonneg (θ - (lam + r) / 2)]
    linarith
  · rintro rfl
    refine ⟨hmem, fun θ' _ => ?_⟩
    rw [key θ', key ((lam + r) / 2)]
    have : 0 ≤ (θ' - (lam + r) / 2) ^ 2 / lam := by positivity
    have e : ((lam + r) / 2 - (lam + r) / 2) ^ 2 / lam = 0 := by ring
    linarith
