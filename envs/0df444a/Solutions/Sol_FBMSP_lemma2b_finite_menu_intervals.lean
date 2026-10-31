-- Prove2me | solution 1 for FBMSP.lemma2b_finite_menu_intervals
-- status  : ACCEPTED   (prove)
-- author  : @mikeh
-- created : 2026-10-30T12:10:10.96823+00:00
-- url     : https://prove2.me/submissions/54b1962b-872e-4621-89bf-45a680e04cd4

import Theorems.Thm_FBMSP_lemma2b_general_menu_intervals

open FBMSP

theorem solution {n k : ℕ}
    (η : MeasureTheory.Measure ℝ) (hnoise : ValidNoise η) (hmhr : HasMHR η)
    (μ w : Fin n → ℝ) (hmarket : ValidFiniteMarket μ w)
    (hk : 0 < k) (p : Fin k → ℝ)
    (hp : Monotone p) (hp_nonneg : ∀ j, 0 ≤ p j) :
    ∃ a : Fin n → Fin k,
      Monotone a ∧
      (∀ i j, postedRevenue η (μ i) (p j) ≤
        postedRevenue η (μ i) (p (a i))) ∧
      (∀ i₁ i₂ i₃, i₁ ≤ i₂ → i₂ ≤ i₃ →
        a i₁ = a i₃ → a i₂ = a i₁) ∧
      ∀ b : Fin n → Fin k,
        finitePolicyRevenue η μ w b p ≤ finitePolicyRevenue η μ w a p := by
  obtain ⟨a, ha, hmax, hfibers⟩ :=
    lemma2b_general_menu_intervals hk η hnoise hmhr p hp hp_nonneg
  have hμ : Monotone μ := hmarket.2.1.monotone
  refine ⟨fun i => a (μ i), ha.comp hμ, ?_, ?_, ?_⟩
  · intro i j
    exact hmax (μ i) j
  · intro i₁ i₂ i₃ h₁₂ h₂₃ heq
    exact hfibers (μ i₁) (μ i₂) (μ i₃) (hμ h₁₂) (hμ h₂₃) heq
  · intro b
    unfold finitePolicyRevenue
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (hmax (μ i) (b i)) (le_of_lt (hmarket.2.2.2.1 i))
