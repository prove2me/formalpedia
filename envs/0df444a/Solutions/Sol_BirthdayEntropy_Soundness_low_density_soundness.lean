-- Prove2me | solution 1 for BirthdayEntropy.Soundness.low_density_soundness
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T00:35:36.614972+00:00
-- url     : https://prove2.me/submissions/31654a23-920e-43a8-a84a-e9209881f8ba

import Theorems.Thm_BirthdayEntropy_Soundness_selected_density
import Theorems.Thm_BirthdayEntropy_Soundness_perfect_completeness
noncomputable section
open scoped Classical
open BirthdayEntropy.Soundness

theorem solution (d ε : ℝ) (hd : 1 ≤ d) (hε : 0 < ε) :
    ∃ C₀ c x₀ : ℝ, 0 < C₀ ∧ 0 < c ∧ 0 < x₀ ∧ x₀ < 1/2 ∧
      (∀ (n m : ℕ) (φ : CSP n m), Source φ d → Gap φ ε →
        ∀ (ℓ : ℕ), Admitted n ℓ C₀ x₀ →
          maxDensity φ ℓ ≤ 2 * Real.exp
            (-c * (ℓ : ℝ)^3 / ((n : ℝ)^2 * logScale n ℓ))) ∧
      (∀ (n m : ℕ) (φ : CSP n m) (ℓ : ℕ),
        1 ≤ ℓ → ℓ ≤ n → Satisfiable φ → HasTargetClique φ ℓ) := by
  obtain ⟨C₀, c, x₀, hC₀, hc, hx₀, hxhalf, hden⟩ := selected_density d ε hd hε
  refine ⟨C₀, c, x₀, hC₀, hc, hx₀, hxhalf, ?_, ?_⟩
  · intro n m φ hsrc hgap ℓ hadm
    have hn : (n : ℝ) ≠ 0 := by
      intro hn
      have h := hadm.2.1
      rw [hn, mul_zero] at h
      have hl : (2 : ℝ) ≤ ℓ := by exact_mod_cast hadm.1
      linarith
    have hexp : -c * (n : ℝ) * (ratio n ℓ)^3 / logScale n ℓ =
        -c * (ℓ : ℝ)^3 / ((n : ℝ)^2 * logScale n ℓ) := by
      unfold ratio
      field_simp
      <;> ring
    unfold maxDensity
    apply Finset.sup'_le
    intro H hH
    have hcard : H.card = Nat.choose n ℓ := (Finset.mem_powersetCard.mp hH).2
    simpa only [hexp] using hden n m φ hsrc hgap ℓ hadm H hcard
  · exact fun n m φ ℓ hℓ hℓn hφ => perfect_completeness n m φ ℓ hℓ hℓn hφ
