-- Prove2me | solution 1 for BosonicLearn.traceDist_gaussian_common_mean
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-13T21:02:59.814745+00:00
-- url     : https://prove2.me/submissions/373c9cfb-3800-4857-a4f0-a16c47af0ebf

import Mathlib
import Definitions.Def_BosonicLearn_IsGaussianState
import Definitions.Def_BosonicLearn_traceDist
import Theorems.Thm_BosonicLearn_state_displace_pair
import Theorems.Thm_BosonicLearn_state_ext_characteristic

open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Support50.P14
open scoped ENNReal Matrix

open BosonicLearn

noncomputable section

/-- A displaced copy of a Gaussian state with mean `μ` has the characteristic function of the Gaussian
state with the same covariance and mean `μ'`. -/
private lemma char_shift {n : ℕ} (ρ ρ' σ : State (Occupation (Fin n)))
    (μ μ' : Fin n ⊕ Fin n → ℝ) (S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)
    (h : IsGaussianState ρ μ S) (k : IsGaussianState σ μ' S)
    (hχ : ∀ ξ : Fin n × Fin 2 → ℝ, oscillatorCharacteristic ρ'.coefficients ξ =
      Complex.exp (Complex.I * (meanForm
        (fun a : Fin n × Fin 2 => μ' (if a.2 = 0 then Sum.inl a.1 else Sum.inr a.1) -
          μ (if a.2 = 0 then Sum.inl a.1 else Sum.inr a.1)) ξ : ℂ)) *
        oscillatorCharacteristic ρ.coefficients ξ) :
    ρ'.coefficients = σ.coefficients := by
  apply state_ext_characteristic
  intro ξ
  rw [hχ ξ, h.2 ξ, k.2 ξ, ← Complex.exp_add]
  congr 1
  have hm : meanForm (fun a : Fin n × Fin 2 => μ' (if a.2 = 0 then Sum.inl a.1 else Sum.inr a.1) -
        μ (if a.2 = 0 then Sum.inl a.1 else Sum.inr a.1)) ξ +
      meanForm (fun a : Fin n × Fin 2 => μ (if a.2 = 0 then Sum.inl a.1 else Sum.inr a.1)) ξ =
      meanForm (fun a : Fin n × Fin 2 => μ' (if a.2 = 0 then Sum.inl a.1 else Sum.inr a.1)) ξ := by
    unfold meanForm
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [← hm]
  push_cast
  ring

theorem solution {n : ℕ} (ρ₁ ρ₂ σ₁ σ₂ : State (Occupation (Fin n)))
    (μ μ' : Fin n ⊕ Fin n → ℝ) (S₁ S₂ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)
    (h₁ : IsGaussianState ρ₁ μ S₁) (h₂ : IsGaussianState ρ₂ μ S₂)
    (k₁ : IsGaussianState σ₁ μ' S₁) (k₂ : IsGaussianState σ₂ μ' S₂) :
    traceDist ρ₁.coefficients ρ₂.coefficients = traceDist σ₁.coefficients σ₂.coefficients := by
  obtain ⟨ρ₁', ρ₂', hχ₁, hχ₂, htr⟩ := state_displace_pair ρ₁ ρ₂
    (fun a : Fin n × Fin 2 => μ' (if a.2 = 0 then Sum.inl a.1 else Sum.inr a.1) -
      μ (if a.2 = 0 then Sum.inl a.1 else Sum.inr a.1))
  have e₁ := char_shift ρ₁ ρ₁' σ₁ μ μ' S₁ h₁ k₁ hχ₁
  have e₂ := char_shift ρ₂ ρ₂' σ₂ μ μ' S₂ h₂ k₂ hχ₂
  unfold traceDist
  rw [← e₁, ← e₂, htr]
