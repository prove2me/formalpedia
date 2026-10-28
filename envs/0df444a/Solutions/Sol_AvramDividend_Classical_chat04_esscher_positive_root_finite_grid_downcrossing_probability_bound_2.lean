-- Prove2me | solution 2 for AvramDividend.Classical.chat04_esscher_positive_root_finite_grid_downcrossing_probability_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:54:35.903418+00:00
-- url     : https://prove2.me/submissions/af7e2264-f99c-4813-8c85-a7fd6d95915b

import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.NNReal.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.GCongr
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_leftshift_terminal_grid_doob_maximal_bound
import Theorems.Thm_AvramDividend_Classical_levy_psi_positive_secant_monotone
import Theorems.Thm_AvramDividend_Classical_finite_grid_downcrossing_implies_compensated_exponential_sup_threshold
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ b : ℝ) (hq : 0 < q) (hφ : 0 < φ)
    (hroot : X.ψ φ = q)
    (T : ℝ≥0) (g : ℕ → ℝ≥0) (hg : Monotone g)
    (hgT : ∀ i : ℕ, g i ≤ T)
    (a : ℝ≥0) (ha : (a : ℝ) = Real.exp ((φ / 2) * b))
    (n : ℕ) :
    (a : ℝ≥0∞) *
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (φ * X.X T ω - (T : ℝ) * X.ψ φ))))
        {ω : Ω | ∃ k : ℕ, k ≤ n ∧ X.X (g k) ω ≤ -b} ≤ 1 := by
  have hsec := levy_psi_positive_secant_monotone X (φ / 2) φ (by linarith) (by linarith)
  have hκ : 0 ≤ X.ψ φ - X.ψ (φ / 2) := by
    rw [hroot] at hsec ⊢
    have h1 : X.ψ (φ / 2) ≤ q / φ * (φ / 2) := by
      rwa [div_le_iff₀ (by linarith)] at hsec
    have h2 : q / φ * (φ / 2) = q / 2 := by field_simp
    linarith
  have hD := chat04_esscher_leftshift_terminal_grid_doob_maximal_bound X φ (φ / 2)
    hφ.le (by linarith) (by linarith) T g hg hgT a n
  refine le_trans ?_ hD
  refine mul_le_mul_right (measure_mono ?_) _
  intro w hw
  obtain ⟨k, hk, hdown⟩ := hw
  have := finite_grid_downcrossing_implies_compensated_exponential_sup_threshold g
    (fun i => X.X (g i) w) (φ / 2) (X.ψ φ - X.ψ (φ / 2)) b (by linarith) hκ n k hk hdown
  rw [ha]
  refine this.trans (le_of_eq ?_)
  have e : φ - φ / 2 = φ / 2 := by ring
  rw [e]
  congr 1
  funext i
  congr 1
  ring
