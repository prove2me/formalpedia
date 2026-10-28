-- Prove2me | solution 1 for AvramDividend.Classical.chat04_esscher_positive_root_finite_grid_downcrossing_probability_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:52:42.368253+00:00
-- url     : https://prove2.me/submissions/ecd08dc5-a36c-45d3-8eb6-1326494d94cd

import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.NNReal.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.GCongr
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_leftshift_terminal_grid_doob_maximal_bound
import Theorems.Thm_AvramDividend_Classical_levy_psi_positive_secant_monotone
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
  have hD := chat04_esscher_leftshift_terminal_grid_doob_maximal_bound X φ (φ / 2) hφ.le
    (by linarith) (by linarith) T g hg hgT a n
  have h2 := levy_psi_positive_secant_monotone X (φ / 2) φ (by linarith) (by linarith)
  rw [hroot] at h2
  have h3 : X.ψ (φ - φ / 2) ≤ X.ψ φ := by
    have e : φ - φ / 2 = φ / 2 := by ring
    rw [e, hroot]
    rw [div_le_div_iff₀ (by linarith) hφ] at h2
    nlinarith
  refine le_trans (mul_le_mul_of_nonneg_left (measure_mono (fun ω hω => ?_)) zero_le) hD
  obtain ⟨k, hk, hkb⟩ := hω
  simp only [Set.mem_setOf_eq]

  rw [ha]
  refine le_trans ?_ (Finset.le_sup' (fun k => Real.exp
    (-(φ / 2) * X.X (g k) ω - (g k : ℝ) * (X.ψ (φ - φ / 2) - X.ψ φ)))
    (Finset.mem_range.2 (Nat.lt_succ_of_le hk)))
  refine Real.exp_le_exp.2 ?_
  have hg0 : (0:ℝ) ≤ g k := (g k).2
  nlinarith
