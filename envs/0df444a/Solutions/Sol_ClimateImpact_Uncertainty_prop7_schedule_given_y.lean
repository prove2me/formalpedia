-- Prove2me | solution 1 for ClimateImpact.Uncertainty.prop7_schedule_given_y
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:28:59.248987+00:00
-- url     : https://prove2.me/submissions/27af59dd-8033-4222-8d2f-b52a57e3e289

import Mathlib
import Definitions.Def_ClimateImpact_Interaction_TimeFactors
import Definitions.Def_ClimateImpact_Uncertainty_FixedPoint

set_option autoImplicit false
open Matrix ClimateImpact.Uncertainty

lemma clu2_beta_facts (ρ T t : ℝ) (hρ : 0 < ρ) (hT : 0 < T) (ht : t ∈ Set.Icc 0 T) :
    0 ≤ ClimateImpact.Interaction.beta ρ T t ∧ 0 ≤ ClimateImpact.Interaction.betaC ρ T t ∧
      ClimateImpact.Interaction.beta ρ T t + ClimateImpact.Interaction.betaC ρ T t = 1 := by
  obtain ⟨ht0, htT⟩ := ht
  have hT1 : Real.exp (-(ρ * T)) < 1 := by
    have := Real.exp_lt_exp.2 (show -(ρ * T) < 0 by nlinarith)
    simpa using this
  have hden : 0 < 1 - Real.exp (-(ρ * T)) := by linarith
  have h1 : Real.exp (-(ρ * t)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith
  have h2 : Real.exp (-(ρ * T)) ≤ Real.exp (-(ρ * t)) := by
    apply Real.exp_le_exp.2; nlinarith
  unfold ClimateImpact.Interaction.beta ClimateImpact.Interaction.betaC
  refine ⟨div_nonneg (by linarith) hden.le, div_nonneg (by linarith) hden.le, ?_⟩
  rw [← add_div]
  rw [div_eq_one_iff_eq hden.ne']
  ring

theorem solution {n : ℕ} (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (ρ T t : ℝ) (hρ : 0 < ρ) (hT : 0 < T) (ht : t ∈ Set.Icc 0 T)
    (κ κc κ₀ κc₀ : ℝ) (hκ : 0 < κ) (hκc : 0 < κc) (hκ₀ : 0 < κ₀) (hκc₀ : 0 < κc₀)
    (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i) (y : ℝ) (hy : 0 < y) (i : Fin n) :
    0 < α * ClimateImpact.Interaction.beta ρ T t * κ * y + ClimateImpact.Interaction.betaC ρ T t * κc ∧
    0 ≤ schedule ρ T t α κ κc c y i ∧
    ∀ x : ℝ, 0 ≤ x → x ≠ schedule ρ T t α κ κc c y i →
      ClimateImpact.Interaction.betaC ρ T t * ClimateImpact.Interaction.quadExt κc₀ κc x + α * ClimateImpact.Interaction.beta ρ T t * y * ClimateImpact.Interaction.quadExt κ₀ κ x + c i * x <
        ClimateImpact.Interaction.betaC ρ T t * ClimateImpact.Interaction.quadExt κc₀ κc (schedule ρ T t α κ κc c y i)
          + α * ClimateImpact.Interaction.beta ρ T t * y * ClimateImpact.Interaction.quadExt κ₀ κ (schedule ρ T t α κ κc c y i)
          + c i * schedule ρ T t α κ κc c y i := by
  obtain ⟨hb, hbc, hsum⟩ := clu2_beta_facts ρ T t hρ hT ht
  set b := ClimateImpact.Interaction.beta ρ T t with hbdef
  set bc := ClimateImpact.Interaction.betaC ρ T t with hbcdef
  have hD : 0 < α * b * κ * y + bc * κc := by
    rcases eq_or_lt_of_le hb with h | h
    · have : bc = 1 := by linarith
      rw [← h, this]; nlinarith
    · have : 0 < α * b * κ * y := by positivity
      nlinarith [mul_nonneg hbc hκc.le]
  refine ⟨hD, ?_, ?_⟩
  · exact div_nonneg (hc i) hD.le
  · intro x hx hne
    set ψ := schedule ρ T t α κ κc c y i with hψdef
    have hψ : c i = ψ * (α * b * κ * y + bc * κc) :=
      (div_mul_cancel₀ (c i) hD.ne').symm
    have hsq : 0 < (x - ψ) ^ 2 := by
      have : x - ψ ≠ 0 := sub_ne_zero.2 hne
      positivity
    unfold ClimateImpact.Interaction.quadExt
    have key : (bc * (κc₀ - κc / 2 * ψ ^ 2) + α * b * y * (κ₀ - κ / 2 * ψ ^ 2) + c i * ψ) -
        (bc * (κc₀ - κc / 2 * x ^ 2) + α * b * y * (κ₀ - κ / 2 * x ^ 2) + c i * x) =
        (α * b * κ * y + bc * κc) / 2 * (x - ψ) ^ 2 := by
      rw [hψ]; ring
    have : 0 < (α * b * κ * y + bc * κc) / 2 * (x - ψ) ^ 2 := by positivity
    linarith
